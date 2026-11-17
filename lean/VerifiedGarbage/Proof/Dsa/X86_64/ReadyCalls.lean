module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Modulus
public import VerifiedGarbage.Proof.Dsa.X86_64.Call
import VerifiedGarbage.Proof.Dsa.X86_64.Power
import VerifiedGarbage.Proof.Dsa.X86_64.Multiply
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Dsa.X86_64.Return
import VerifiedGarbage.Proof.Dsa.X86_64.Reduce
import VerifiedGarbage.Proof.Dsa.X86_64.Add
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
public import VerifiedGarbage.Proof.Dsa.X86_64.Arguments

/-! ### `Dsa.X86_64.Arguments2`, which this module and modules that import it used -/

section

/-! # Input and output bindings for streaming reduction -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def Arguments2 (mem original : Mem) (B : Addr) (a output : Operand) : Prop :=
  word mem B (8 * arg) = pointerValue original B a.pointer ∧
  word mem B (8 * argLen) = word original B a.length.offset ∧
  word mem B (8 * result) = pointerValue original B output.pointer ∧
  word mem B (8 * resultLen) = word original B output.length.offset

/-- Bind the reduction input and result while preserving saved fields and
both structural and modulus words of the selected child. -/
theorem arguments2_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (ho : 256 ≤ o) (hhi : o + slot wx 8 ≤ Z)
    (a output : Operand) (ha : pointerFits a.pointer) (hout : pointerFits output.pointer) :
    WP isa (.block (Core.operand arg argLen a ++ Core.operand result resultLen output)) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Arguments2 t.mem s.mem B a output ∧
      (∀ f : Field, word t.mem B f.offset = word s.mem B f.offset) ∧
      Frm B argumentRanges s.mem t.mem ∧ Keep [.rax] s t := by
  have hn := hg.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (operand_context hg hZ a ha (by decide) (by decide) (by decide) (by decide) (by decide))
    fun u ⟨hgu, hua, hual, hfieldsu, hfu, hku⟩ => ?_
  have hchildu := call_ready child hfu (by decide) (by decide) ho (by omega_using [hhi, hn])
  refine WP.mono (operand_context hgu hZ output hout (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨hgt, hto, htol, hfieldst, hft, hkt⟩ => ?_
  rw [pointerValue_congr hfieldsu] at hto
  rw [hfieldsu output.length] at htol
  refine ⟨hgt, call_ready hchildu hft (by decide) (by decide) ho (by omega_using [hhi, hn]), ?_,
    fun f => (hfieldst f).trans (hfieldsu f), ?_, (hku.trans hkt).mono (by decide)⟩
  · exact ⟨(call_word hft (by decide) (by decide) (by decide) (by decide) (by decide)).trans hua,
      (call_word hft (by decide) (by decide) (by decide) (by decide) (by decide)).trans hual, hto, htol⟩
  · exact (call_argument_frame hfu (by decide) (by decide)).trans
      (call_argument_frame hft (by decide) (by decide))

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.CoreCalls`, which only this module used -/

section

/-! # Exponentiation and multiplication in the DSA parent workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Complete parent-to-child exponentiation, with a reusable modulus and
an ordinary big-endian result. No primality assumption is required. -/
theorem corePow_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx m k : Nat}
    {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (a b output : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (houtp : pointerFits output.pointer) {ba bb : List Byte}
    (has : OperandBytes s B Z a ba) (hbs : OperandBytes s B Z b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ wx)
    (hb1 : 1 ≤ bb.length) (hb2 : bb.length ≤ 1024)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j)) :
    WP isa (Core.pow Sq.mm M.mm o a b output) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k =
        Spec.Dsa.encodeBE k (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE bb) m) ∧
      CallFrame B o wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  apply call3_ok hg child hZ hlo hhi ho a b output ha hb houtp hl hk1 hk' hkw hout hprefix
  intro u hc hchild hargs hf hk
  have hz : 176 ≤ Z := Nat.le_trans (by decide) hZ
  refine WP.mono (power_ok M Sq hc hw2 hw48 hwx hw30 hm hodd hchild.modulus hchild.inverse
    (by decide) (by decide) (by decide) (by decide)
    hargs.1 (hargs.2.1.trans has.length) (arguments_source hf hk hz has.source) ha1 haw
    hargs.2.2.1 (hargs.2.2.2.1.trans hbs.length) (arguments_source hf hk hz hbs.source) hb1 hb2)
    fun v ⟨hcv, hv, hmv, hfv, hkv⟩ => ⟨hcv, hmv, hv, hfv, hkv⟩

/-- Complete parent-to-child multiplication. Both input buffers may contain
unreduced values, and the destination may alias either input. -/
theorem coreProduct_ok (M : Mont) {s : State} {B : Addr} {Z o w wx m k : Nat}
    {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (a b output : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (houtp : pointerFits output.pointer) {ba bb : List Byte}
    (has : OperandBytes s B Z a ba) (hbs : OperandBytes s B Z b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ wx)
    (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ wx)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j)) :
    WP isa (Core.product M.mm o a b output) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k =
        Spec.Dsa.encodeBE k (Spec.Dsa.decodeBE ba * Spec.Dsa.decodeBE bb % m) ∧
      CallFrame B o wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  apply call3_ok hg child hZ hlo hhi ho a b output ha hb houtp hl hk1 hk' hkw hout hprefix
  intro u hc hchild hargs hf hk
  have hz : 176 ≤ Z := Nat.le_trans (by decide) hZ
  refine WP.mono (product_ok M hc hw2 hw48 hwx hw30 hm hodd hchild.modulus hchild.inverse
    (by decide) (by decide) (by decide) (by decide)
    hargs.1 (hargs.2.1.trans has.length) (arguments_source hf hk hz has.source) ha1 haw
    hargs.2.2.1 (hargs.2.2.2.1.trans hbs.length) (arguments_source hf hk hz hbs.source) hb1 hbw)
    fun v ⟨hcv, hv, hmv, hfv, hkv⟩ => ⟨hcv, hmv, hv, hfv, hkv⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.CoreReduce`, which only this module used -/

section

/-! ### `Dsa.X86_64.Call2`, which only this module used -/

section

/-! # Complete DSA arithmetic calls, from operand binding through return -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- The common two-operand calling convention. The arithmetic body is
proved separately for the selected Montgomery backend. -/
theorem call2_ok {s : State} {B : Addr} {Z o w wx m value k : Nat}
    {minv parentMinv : BitVec 64} {body : Prog isa}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (a output : Operand) (ha : pointerFits a.pointer)
    (houtp : pointerFits output.pointer)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j))
    (run : ∀ u, SubCtx u B Z o w wx minv → ChildReady u.mem B o wx m minv →
      Arguments2 u.mem s.mem B a output → Frm B argumentRanges s.mem u.mem → Keep coreRegs s u →
      WP isa body u fun v => SubCtx v B Z o w wx minv ∧
        ModCtx v (off B o) (slot wx 8) wx minv m ∧
        wv v.mem (off B o) (slot wx aY) wx = value ∧
        Frm (off B o) (workRanges wx) u.mem v.mem ∧ Keep mmRegs u v) :
    WP isa (seqs (([.block (Core.operand arg argLen a ++
      Core.operand result resultLen output ++ Core.enter o), body] : List (Prog isa)) ++ Core.finish)) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k = Spec.Dsa.encodeBE k value ∧
      CallFrame B o wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  have hslot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  change WP isa (.seq (.block _) (.seq body (seqs Core.finish))) s _
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (arguments2_ok hg child hZ (by omega_using [hlo, hslot]) (by omega_using [hhi]) a output ha houtp)
    fun u ⟨hgu, hchild, hargs, _, hf, hk⟩ => ?_
  refine WP.mono (enter_ok hgu hchild.header hlo hhi ho) fun v ⟨hcv, hmem, hkv⟩ => ?_
  have hfv : Frm B argumentRanges s.mem v.mem := by rw [hmem]; exact hf
  have hav : Arguments2 v.mem s.mem B a output := by rw [hmem]; exact hargs
  have hchv : ChildReady v.mem B o wx m minv := by rw [hmem]; exact hchild
  have hks : Keep coreRegs s v := (hk.trans hkv).mono (by decide)
  refine WP.mono (returnAfter_ok (parentMinv := parentMinv) hcv (run v hcv hchv hav hfv hks)
    (by rw [hmem]; exact hgu.hdr.hminv) hav.2.2.1 (hav.2.2.2.trans hl)
    hk1 hk' hkw (fun j hj => by rw [hks.2.2]; exact hout j hj) hprefix)
    fun t ⟨hgt, hct, htout, _, hft, hkt⟩ => ?_
  refine ⟨hgt, hct, htout, ?_, (hks.trans hkt).mono (by decide)⟩
  intro x hx hc hxout
  exact (hft x hc hxout).trans (hfv x (by
    intro r hr
    simp only [argumentRanges, List.mem_singleton] at hr
    subst r
    exact hx))

end VG.Proof.Dsa.X86_64

end

end

/-! # Streaming reduction in the DSA parent workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Complete streaming reduction call, including empty digest inputs. -/
theorem coreReduce_ok (M : Mont) {s : State} {B : Addr} {Z w wx m k : Nat}
    {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B qWorkspace wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ qWorkspace)
    (hhi : qWorkspace + slot wx 8 + tabBytes wx ≤ Z)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48)
    (hm : 255 < m) (hodd : m % 2 = 1)
    (a output : Operand) (ha : pointerFits a.pointer)
    (houtp : pointerFits output.pointer) {ba : List Byte}
    (has : OperandBytes s B Z a ba) (hal : ba.length < 2 ^ 64)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j)) :
    WP isa (Core.reduce M.mm a output) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B qWorkspace wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k =
        Spec.Dsa.encodeBE k (Spec.Dsa.decodeBE ba % m) ∧
      CallFrame B qWorkspace wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  apply call2_ok hg child hZ hlo hhi (by decide) a output ha houtp hl hk1 hk' hkw hout hprefix
  intro u hc hchild hargs hf hk
  exact reduce_ok M hc hw2 hw48 hm hodd hchild.modulus hchild.inverse
    (by decide) (by decide) hargs.1 (hargs.2.1.trans has.length)
    (arguments_source hf hk (Nat.le_trans (by decide) hZ) has.source) hal

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.CoreAdd`, which only this module used -/

section

/-! # Exponentiation and multiplication in the DSA parent workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Complete modular addition call for two already reduced scalars. -/
theorem coreAdd_ok {s : State} {B : Addr} {Z w wx m k : Nat}
    {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B qWorkspace wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ qWorkspace)
    (hhi : qWorkspace + slot wx 8 + tabBytes wx ≤ Z)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (a b output : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (houtp : pointerFits output.pointer) {ba bb : List Byte}
    (has : OperandBytes s B Z a ba) (hbs : OperandBytes s B Z b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ wx)
    (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ wx)
    (haReduced : Spec.Dsa.decodeBE ba < m) (hbReduced : Spec.Dsa.decodeBE bb < m)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j)) :
    WP isa (Core.add a b output) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B qWorkspace wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k =
        Spec.Dsa.encodeBE k ((Spec.Dsa.decodeBE ba + Spec.Dsa.decodeBE bb) % m) ∧
      CallFrame B qWorkspace wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  have h := call3_ok (body := seqs [Arithmetic.load aX arg argLen,
    Arithmetic.load aXm arg2 arg2Len, Crt.addMod aY aX aXm])
    hg child hZ hlo hhi (by decide) a b output ha hb houtp hl hk1 hk' hkw hout hprefix
    (value := (Spec.Dsa.decodeBE ba + Spec.Dsa.decodeBE bb) % m) ?_
  · change WP isa (.seq (.block _) (.seq (Arithmetic.load aX arg argLen)
      (.seq (Arithmetic.load aXm arg2 arg2Len) (.seq (Crt.addMod aY aX aXm) (seqs Core.finish))))) s _
    refine WP.seq (WP.mono (WP.seq_iff.mp h) fun u hu => ?_)
    exact WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp hu)) fun v hv =>
      WP.seq (WP.mono (WP.seq_iff.mp hv) fun z hz => WP.seq hz))
  intro u hc hchild hargs hf hk
  have hz : 176 ≤ Z := Nat.le_trans (by decide) hZ
  exact add_ok hc ⟨hc.good, hchild.modulus, hchild.inverse⟩ hw2 hw48 hwx hw30
    (by decide) (by decide) (by decide) (by decide)
    hargs.1 (hargs.2.1.trans has.length) (arguments_source hf hk hz has.source) ha1 haw
    hargs.2.2.1 (hargs.2.2.2.1.trans hbs.length) (arguments_source hf hk hz hbs.source) hb1 hbw
    haReduced hbReduced

end VG.Proof.Dsa.X86_64

end

end


/-! # Arithmetic calls preserving the complete DSA execution context -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure CallResult (L : ExecutionLayout) (side : ModulusSide) (d value : Nat) (s t : State) : Prop where
  ready : Ready L t
  bytes : Spec.Rsa.bytesAt t.mem (off L.base d) (side.length L) = Spec.Dsa.encodeBE (side.length L) value
  frame : CallFrame L.base side.offset (side.words L) (off L.base d) (side.length L) s.mem t.mem
  keep : Keep coreRegs s t

theorem readyPow_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s : State} (h : Ready L s)
    (side : ModulusSide) (hm : 1 < side.value L) (hodd : side.value L % 2 = 1)
    (a b : Operand) {ba bb : List Byte} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (has : OperandBytes s L.base activeBytes a ba) (hbs : OperandBytes s L.base activeBytes b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ side.words L)
    (hb1 : 1 ≤ bb.length) (hb2 : bb.length ≤ 1024)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes) :
    WP isa (Core.pow Sq.mm M.mm side.offset a b ⟨.local d, side.lengthField⟩) s
      (CallResult L side d (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE bb) (side.value L)) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, hk1, hk31⟩ := side.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega_using [hend, this]
  refine WP.mono (corePow_ok M Sq h.parent (h.child side) (by decide) hlo hhi ho
    hw2 hw48 hw48 (by decide) hm hodd a b ⟨.local d, side.lengthField⟩ ha hb hdp
    has hbs ha1 haw hb1 hb2 (h.length side) hk1 hk31 rfl
    (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterCall side hp hc hf hk hd hend, hv, hf, hk⟩

theorem readyProduct_ok (M : Mont) {L : ExecutionLayout} {s : State} (h : Ready L s)
    (side : ModulusSide) (hm : 1 < side.value L) (hodd : side.value L % 2 = 1)
    (a b : Operand) {ba bb : List Byte} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (has : OperandBytes s L.base activeBytes a ba) (hbs : OperandBytes s L.base activeBytes b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ side.words L)
    (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ side.words L)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes) :
    WP isa (Core.product M.mm side.offset a b ⟨.local d, side.lengthField⟩) s
      (CallResult L side d (Spec.Dsa.decodeBE ba * Spec.Dsa.decodeBE bb % side.value L) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, hk1, hk31⟩ := side.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega_using [hend, this]
  refine WP.mono (coreProduct_ok M h.parent (h.child side) (by decide) hlo hhi ho
    hw2 hw48 hw48 (by decide) hm hodd a b ⟨.local d, side.lengthField⟩ ha hb hdp
    has hbs ha1 haw hb1 hbw (h.length side) hk1 hk31 rfl
    (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterCall side hp hc hf hk hd hend, hv, hf, hk⟩

theorem readyReduce_ok (M : Mont) {L : ExecutionLayout} {s : State} (h : Ready L s)
    (hm : 255 < L.subgroup) (hodd : L.subgroup % 2 = 1)
    (a : Operand) {ba : List Byte} (ha : pointerFits a.pointer)
    (has : OperandBytes s L.base activeBytes a ba) (hal : ba.length < 2 ^ 64)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + L.qLen ≤ usedBytes) :
    WP isa (Core.reduce M.mm a (Core.scalar d)) s
      (CallResult L .q d (Spec.Dsa.decodeBE ba % L.subgroup) s) := by
  obtain ⟨hw2, hw48, hlo, _, hhi, hk1, hk31⟩ := ModulusSide.q.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega_using [hend, this]
  refine WP.mono (coreReduce_ok M h.parent h.qChild (by decide) hlo hhi hw2 hw48 hm hodd
    a (Core.scalar d) ha hdp has hal (h.length .q) hk1 hk31 rfl
    (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterQ hp hc hf hk hd hend, hv, hf, hk⟩

theorem readyAdd_ok {L : ExecutionLayout} {s : State} (h : Ready L s)
    (a b : Operand) {ba bb : List Byte} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (has : OperandBytes s L.base activeBytes a ba) (hbs : OperandBytes s L.base activeBytes b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ L.qWords)
    (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ L.qWords)
    (har : Spec.Dsa.decodeBE ba < L.subgroup) (hbr : Spec.Dsa.decodeBE bb < L.subgroup)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + L.qLen ≤ usedBytes) :
    WP isa (Core.add a b (Core.scalar d)) s
      (CallResult L .q d ((Spec.Dsa.decodeBE ba + Spec.Dsa.decodeBE bb) % L.subgroup) s) := by
  obtain ⟨hw2, hw48, hlo, _, hhi, hk1, hk31⟩ := ModulusSide.q.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega_using [hend, this]
  refine WP.mono (coreAdd_ok h.parent h.qChild (by decide) hlo hhi hw2 hw48 hw48 (by decide)
    a b (Core.scalar d) ha hb hdp has hbs ha1 haw hb1 hbw har hbr
    (h.length .q) hk1 hk31 rfl (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterQ hp hc hf hk hd hend, hv, hf, hk⟩

end VG.Proof.Dsa.X86_64
