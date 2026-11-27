module

public import VerifiedGarbage.Proof.Dsa.AArch64.CallHeader
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Dsa.AArch64.Arguments`, which this module and modules that import it used -/

section

/-! # Preparing the three operand bindings of a DSA arithmetic call -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def argumentRanges : List (Nat × Nat) := [(128, 48)]

theorem call_argument_frame {mem mem' : Mem} {B : Addr} {sp sl : Nat}
    (hf : Frm B (callRanges sp sl) mem mem') (hsp : 16 ≤ sp ∧ sp ≤ 21) (hsl : 16 ≤ sl ∧ sl ≤ 21) :
    Frm B argumentRanges mem mem' := by
  intro x hx
  apply hf x
  intro r hr
  have h := hx (128, 48) (List.mem_singleton_self _)
  simp only [callRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> omega

theorem call_word {mem mem' : Mem} {B : Addr} {sp sl i : Nat}
    (hf : Frm B (callRanges sp sl) mem mem') (_hsp : sp < 32) (_hsl : sl < 32)
    (hi : i < 32) (h1 : i ≠ sp) (h2 : i ≠ sl) :
    word mem' B (8 * i) = word mem B (8 * i) := by
  apply hf.word_eq _ (by omega_using [hi])
  intro r hr
  simp only [callRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> omega_arith

/-- All six call-header words, expressed using the original saved fields. -/
def Arguments (mem original : Mem) (B : Addr) (a b output : Operand) : Prop :=
  word mem B (8 * arg) = pointerValue original B a.pointer ∧
  word mem B (8 * argLen) = word original B a.length.offset ∧
  word mem B (8 * arg2) = pointerValue original B b.pointer ∧
  word mem B (8 * arg2Len) = word original B b.length.offset ∧
  word mem B (8 * result) = pointerValue original B output.pointer ∧
  word mem B (8 * resultLen) = word original B output.length.offset

/-- Setting up a power, product or sum call preserves its selected child
and all saved pointers and lengths. -/
theorem arguments_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (ho : 256 ≤ o) (hhi : o + slot wx 8 ≤ Z)
    (a b output : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hout : pointerFits output.pointer) :
    WP isa (.block (Core.operand arg argLen a ++ Core.operand arg2 arg2Len b ++
      Core.operand result resultLen output)) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Arguments t.mem s.mem B a b output ∧
      (∀ f : Field, word t.mem B f.offset = word s.mem B f.offset) ∧
      Frm B argumentRanges s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  have hn := hg.scr.nowrap
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (operand_context hg hZ a ha (by decide) (by decide) (by decide) (by decide) (by decide))
    fun u ⟨hgu, hua, hual, hfieldsu, hfu, hku⟩ => ?_
  have hchildu := call_ready child hfu (by decide) (by decide) ho (by omega_using [hhi, hn])
  rw [WP.block_append_iff]
  refine WP.mono (operand_context hgu hZ b hb (by decide) (by decide) (by decide) (by decide) (by decide))
    fun v ⟨hgv, hvb, hvbl, hfieldsv, hfv, hkv⟩ => ?_
  have hchildv := call_ready hchildu hfv (by decide) (by decide) ho (by omega_using [hhi, hn])
  have hfieldsv' : ∀ f : Field, word v.mem B f.offset = word s.mem B f.offset :=
    fun f => (hfieldsv f).trans (hfieldsu f)
  rw [pointerValue_congr hfieldsu] at hvb
  rw [hfieldsu b.length] at hvbl
  have hva := (call_word hfv (by decide) (by decide) (by decide) (by decide) (by decide)).trans hua
  have hval := (call_word hfv (by decide) (by decide) (by decide) (by decide) (by decide)).trans hual
  refine WP.mono (operand_context hgv hZ output hout (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨hgt, hto, htol, hfieldst, hft, hkt⟩ => ?_
  rw [pointerValue_congr hfieldsv'] at hto
  rw [hfieldsv' output.length] at htol
  refine ⟨hgt, call_ready hchildv hft (by decide) (by decide) ho (by omega_using [hhi, hn]), ?_,
    fun f => (hfieldst f).trans (hfieldsv' f), ?_, ((hku.trans hkv).trans hkt).mono (by decide)⟩
  · exact ⟨(call_word hft (by decide) (by decide) (by decide) (by decide) (by decide)).trans hva,
      (call_word hft (by decide) (by decide) (by decide) (by decide) (by decide)).trans hval,
      (call_word hft (by decide) (by decide) (by decide) (by decide) (by decide)).trans hvb,
      (call_word hft (by decide) (by decide) (by decide) (by decide) (by decide)).trans hvbl, hto, htol⟩
  · exact ((call_argument_frame hfu (by decide) (by decide)).trans
      (call_argument_frame hfv (by decide) (by decide))).trans
      (call_argument_frame hft (by decide) (by decide))

end VG.Proof.Dsa.AArch64

end

end

/-! # Complete DSA arithmetic calls, from operand binding through return -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- An operand's saved length and readable byte representation. -/
structure OperandBytes (s : State) (B : Addr) (Z : Nat) (a : Operand) (bytes : List Byte) : Prop where
  length : word s.mem B a.length.offset = BitVec.ofNat 64 bytes.length
  source : Src s B Z (pointerValue s.mem B a.pointer) bytes

/-- A complete call may change its six argument words, child work area and result. -/
def CallFrame (B : Addr) (o wx : Nat) (out : Addr) (k : Nat) (mem mem' : Mem) : Prop :=
  ∀ x, (ofs B x < 128 ∨ 176 ≤ ofs B x) →
    (∀ r ∈ workRanges wx, ofs (off B o) x < r.1 ∨ r.1 + r.2 ≤ ofs (off B o) x) →
    (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → mem' x = mem x

/-- Sources outside the active prefix survive the argument writes. -/
theorem arguments_source {s t : State} {B p : Addr} {Z : Nat} {bytes : List Byte}
    {rs : List Reg} (hf : Frm B argumentRanges s.mem t.mem) (hk : Keep rs s t)
    (hZ : 176 ≤ Z) (hs : Src s B Z p bytes) : Src t B Z p bytes := by
  apply hs.congrK _ hk
  apply InScr.of_frm hf
  intro r hr
  simp only [argumentRanges, List.mem_singleton] at hr
  subst r
  exact hZ

/-- The common three-operand calling convention. The arithmetic body is
proved separately for the selected Montgomery backend. -/
theorem call3_ok {s : State} {B : Addr} {Z o w wx m value k : Nat}
    {minv parentMinv : BitVec 64} {body : Prog isa}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 16)
    (a b output : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (houtp : pointerFits output.pointer)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j))
    (run : ∀ u, SubCtx u B Z o w wx minv → ChildReady u.mem B o wx m minv →
      Arguments u.mem s.mem B a b output → Frm B argumentRanges s.mem u.mem → Keep coreRegs s u →
      WP isa body u fun v => SubCtx v B Z o w wx minv ∧
        ModCtx v (off B o) (slot wx 8) wx minv m ∧
        wv v.mem (off B o) (slot wx aY) wx = value ∧
        Frm (off B o) (workRanges wx) u.mem v.mem ∧ Keep mmRegs u v) :
    WP isa (seqs (([.block (Core.operand arg argLen a ++ Core.operand arg2 arg2Len b ++
      Core.operand result resultLen output ++ Core.enter o), body] : List (Prog isa)) ++ Core.finish)) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k = Spec.Dsa.encodeBE k value ∧
      CallFrame B o wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  have hslot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  change WP isa (.seq (.block _) (.seq body (seqs Core.finish))) s _
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (arguments_ok hg child hZ (by omega_using [hlo, hslot]) (by omega_using [hhi]) a b output ha hb houtp)
    fun u ⟨hgu, hchild, hargs, _, hf, hk⟩ => ?_
  refine WP.mono (enter_ok hgu hchild.header hlo hhi ho) fun v ⟨hcv, hmem, hkv⟩ => ?_
  have hfv : Frm B argumentRanges s.mem v.mem := by rw [hmem]; exact hf
  have hav : Arguments v.mem s.mem B a b output := by rw [hmem]; exact hargs
  have hchv : ChildReady v.mem B o wx m minv := by rw [hmem]; exact hchild
  have hks : Keep coreRegs s v := (hk.trans hkv).mono (by decide)
  refine WP.mono (returnAfter_ok (parentMinv := parentMinv) hcv (run v hcv hchv hav hfv hks)
    (by rw [hmem]; exact hgu.hdr.hminv) hav.2.2.2.2.1 (hav.2.2.2.2.2.trans hl)
    hk1 hk' hkw (fun j hj => by rw [hks.wr]; exact hout j hj) hprefix)
    fun t ⟨hgt, hct, htout, _, hft, hkt⟩ => ?_
  refine ⟨hgt, hct, htout, ?_, (hks.trans hkt).mono (by decide)⟩
  intro x hx hc hxout
  exact (hft x hc hxout).trans (hfv x (by
    intro r hr
    simp only [argumentRanges, List.mem_singleton] at hr
    subst r
    exact hx))

end VG.Proof.Dsa.AArch64
