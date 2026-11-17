module

public import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import Batteries.Logic
public import VerifiedGarbage.Proof.Dsa.AArch64.Finish
public import VerifiedGarbage.Proof.Dsa.AArch64.Frame

/-! ### `Dsa.AArch64.Return`, which this module and modules that import it used -/

section

/-! # Composing DSA arithmetic with result encoding and workspace return -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- A result call changes the selected child and the designated output bytes. -/
def ResultFrame (B : Addr) (o wx : Nat) (out : Addr) (k : Nat) (mem mem' : Mem) : Prop :=
  ∀ x, (∀ r ∈ workRanges wx, ofs (off B o) x < r.1 ∨ r.1 + r.2 ≤ ofs (off B o) x) →
    (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → mem' x = mem x

/-- The parent can call a child again with the same modulus and inverse. -/
structure ChildReady (mem : Mem) (B : Addr) (o wx m : Nat) (minv : BitVec 64) : Prop where
  header : WsAt mem B o wx minv
  modulus : wv mem (off B o) (slot wx aN) wx = m
  inverse : ((word mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0

/-- Any verified arithmetic body can return an encoded result while keeping
its modulus and every parent-header word available for the next call. -/
theorem returnAfter_ok {s : State} {B out : Addr} {Z o w wx m value k : Nat}
    {minv parentMinv : BitVec 64} {body : Prog isa}
    (hc : SubCtx s B Z o w wx minv)
    (run : WP isa body s fun u => SubCtx u B Z o w wx minv ∧
      ModCtx u (off B o) (slot wx 8) wx minv m ∧
      wv u.mem (off B o) (slot wx aY) wx = value ∧
      Frm (off B o) (workRanges wx) s.mem u.mem ∧ Keep mmRegs s u)
    (hpm : word s.mem B (8 * sMinv) = parentMinv)
    (hp : word s.mem B (8 * result) = out)
    (hl : word s.mem B (8 * resultLen) = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (out + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j)) :
    WP isa (.seq body (seqs Core.finish)) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Spec.Rsa.bytesAt t.mem out k = Spec.Dsa.encodeBE k value ∧
      (∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i)) ∧
      ResultFrame B o wx out k s.mem t.mem ∧ Keep coreRegs s t := by
  have hlo := hc.lo
  have hhi := hc.hi
  have hroot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  have hchild : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  refine WP.seq (WP.mono run fun u ⟨hcu, hmu, huv, hfu, hku⟩ => ?_)
  refine WP.mono (finish_ok hcu ((work_parent hc hfu (by decide)).trans hpm)
    ((work_parent hc hfu (by decide)).trans hp) ((work_parent hc hfu (by decide)).trans hl)
    hk1 hk' hkw (fun j hj => by rw [hku.wr]; exact hout j hj) hprefix)
    fun t ⟨hgt, htout, htword, hft, hkt⟩ => ?_
  have hcword : ∀ d, o + d + 8 ≤ Z → word t.mem (off B o) d = word u.mem (off B o) d := by
    intro d hd
    rw [word_off, word_off]
    exact htword _ hd
  have hhdr : WsAt t.mem B o wx minv :=
    (show WsAt u.mem B o wx minv from ⟨hcu.hdr, hcu.link⟩).of_words
      (fun i hi => hcword _ (by omega_using [hhi, hchild, hi]))
  have hn : wv t.mem (off B o) (slot wx aN) wx = m := by
    rw [wv_congr (fun i hi => hcword _ (by have := slot_le (w := wx) (show aN < 8 by decide); omega_using [hhi, hi, this]))]
    exact hmu.modulus
  have hinv : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hcword _ (by have := slot_le (w := wx) (show aN < 8 by decide); omega_using [hhi, this])]
    exact hmu.inverse
  rw [huv] at htout
  exact ⟨hgt, ⟨hhdr, hn, hinv⟩, htout,
    fun i hi => (htword _ (by omega_using [hhi, hchild, hi])).trans (work_parent hc hfu hi),
    fun x hx ho => (hft x ho).trans (hfu x hx), (hku.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # Frames for DSA arithmetic call arguments -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def callRanges (sp sl : Nat) : List (Nat × Nat) := [(8 * sp, 8), (8 * sl, 8)]

/-- Each pair of argument writes preserves the parent structure and saved
fields, and records the exact pointer and length handed to the child. -/
theorem operand_context {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : pWorkspace ≤ Z) (a : Operand) (ha : pointerFits a.pointer)
    {sp sl : Nat} (hsp0 : 16 ≤ sp) (hsp : sp < 32) (hsl0 : 16 ≤ sl) (hsl : sl < 32)
    (hne : sp ≠ sl) :
    WP isa (.block (Core.operand sp sl a)) s fun t =>
      Good t B Z w minv ∧
      word t.mem B (8 * sp) = pointerValue s.mem B a.pointer ∧
      word t.mem B (8 * sl) = word s.mem B a.length.offset ∧
      (∀ f : Field, word t.mem B f.offset = word s.mem B f.offset) ∧
      Frm B (callRanges sp sl) s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  refine WP.mono (operand_ok hg.scr hg.x0 hZ a ha hsp hsl) fun t ⟨hmem, hk⟩ => ?_
  let first := s.mem.writeW (off B (8 * sp)) (pointerValue s.mem B a.pointer)
  have ho1 : Outside B (8 * sp) 8 s.mem first := writeW_outside _ _ _ (by omega_using [hsp])
  have ho2 : Outside B (8 * sl) 8 first t.mem := by
    rw [hmem]; exact writeW_outside _ _ _ (by omega_using [hsl])
  refine ⟨⟨hg.scr.congr hk.wr, (hk.gpr .x0 (by decide)).trans hg.x0, ?_⟩, ?_, ?_, ?_, ?_, hk⟩
  · rw [hmem]
    exact (hg.hdr.store hsp0 hsp _).store hsl0 hsl _
  · rw [hmem, hdrStore_hdr _ _ _ hsl hsp (Ne.symm hne), word_writeW_self]
  · rw [hmem, word_writeW_self]
  · intro f
    have hf := VG.Proof.Dsa.field_bounds f
    have hp : pWorkspace < 2 ^ 64 := by decide
    rw [ho2.word (Or.inr (by omega_using [hsl, hf])) (by omega_using [hf, hp]), ho1.word (Or.inr (by omega_using [hsp, hf])) (by omega_using [hf, hp])]
  · exact (Frm.of_outside ho1 (by simp [callRanges])).trans
      (Frm.of_outside ho2 (by simp [callRanges]))

/-- Call-header writes leave every child workspace header intact. -/
theorem call_child {mem mem' : Mem} {B : Addr} {o wx sp sl : Nat} {minv : BitVec 64}
    (h : WsAt mem B o wx minv) (hf : Frm B (callRanges sp sl) mem mem')
    (hsp : sp < 32) (hsl : sl < 32) (ho : 256 ≤ o) (hbound : o + 136 ≤ 2 ^ 64) :
    WsAt mem' B o wx minv := by
  apply h.of_words
  intro i hi
  rw [word_off, word_off]
  apply hf.word_eq
  · intro r hr
    simp only [callRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> right <;> omega
  · omega_using [hbound, hi]

/-- Arguments remain in the active arithmetic prefix, so sources in the
scratch suffix or caller buffers retain their values and permissions. -/
theorem call_source {s t : State} {B p : Addr} {Z sp sl : Nat} {bytes : List Byte}
    {rs : List Reg} (hf : Frm B (callRanges sp sl) s.mem t.mem) (hk : Keep rs s t)
    (hsp : sp < 32) (hsl : sl < 32) (hZ : 256 ≤ Z) (hs : Src s B Z p bytes) :
    Src t B Z p bytes := by
  apply hs.congrK _ hk
  apply InScr.of_frm hf
  intro r hr
  simp only [callRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only <;> omega_arith

/-- Saved-field equality is sufficient to resolve every operand identically. -/
theorem pointerValue_congr {mem mem' : Mem} {B : Addr}
    (hf : ∀ f : Field, word mem' B f.offset = word mem B f.offset) (p : Pointer) :
    pointerValue mem' B p = pointerValue mem B p := by
  cases p with
  | input f => exact hf f
  | «local» _ => rfl
  | signatureS => exact congrArg₂ (· + ·) (hf .signature) (hf .qLen)

/-- Argument writes preserve the selected child's full reusable modulus state. -/
theorem call_ready {mem mem' : Mem} {B : Addr} {o wx m sp sl : Nat} {minv : BitVec 64}
    (h : ChildReady mem B o wx m minv) (hf : Frm B (callRanges sp sl) mem mem')
    (hsp : sp < 32) (hsl : sl < 32) (ho : 256 ≤ o)
    (hbound : o + slot wx 8 ≤ 2 ^ 64) : ChildReady mem' B o wx m minv := by
  have hslot : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  have hword : ∀ d, 256 ≤ d → d + 8 ≤ 2 ^ 64 → word mem' B d = word mem B d := by
    intro d hd hd'
    apply hf.word_eq _ hd'
    intro r hr
    simp only [callRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> right <;> omega
  have hN := slot_le (w := wx) (show aN < 8 by decide)
  have hNlo : 256 ≤ slot wx aN := by unfold slot hdrBytes; omega_using []
  refine ⟨call_child h.header hf hsp hsl ho (by omega_using [hbound, hslot]), ?_, ?_⟩
  · rw [wv_congr (m := mem) (m' := mem') (fun i hi => by rw [word_off, word_off]; exact hword _ (by omega_using [ho]) (by omega_using [hbound, hN, hi]))]
    exact h.modulus
  · rw [word_off, hword _ (by omega_using [ho]) (by omega_using [hbound, hN]), ← word_off]
    exact h.inverse

end VG.Proof.Dsa.AArch64
