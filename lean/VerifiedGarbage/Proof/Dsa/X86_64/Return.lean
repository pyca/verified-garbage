module

public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
public import VerifiedGarbage.Impl.Dsa.X86_64.Core
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.CrtMath

/-! ### `Dsa.X86_64.Finish`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.EnterLeave`, which this module and modules that import it used -/

section

/-! # Switching between the DSA parent and arithmetic workspaces -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Enter a linked child without changing memory or any other register. -/
theorem enter_ok {s : State} {B : Addr} {Z o w wx : Nat} {parentMinv minv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : WsAt s.mem B o wx minv)
    (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31) :
    WP isa (.block (Core.enter o)) s fun t =>
      SubCtx t B Z o w wx minv ∧ t.mem = s.mem ∧ Keep [.rdi] s t := by
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B o ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hdi, hm⟩, hk⟩ =>
      ⟨⟨hg.scr.congr hk.2.2, hdi, hm ▸ child.hdr, hm ▸ child.link,
        hm ▸ hg.hdr.hw, hm ▸ hg.hdr.harr, hlo, hhi⟩, hm, hk⟩
  unfold Core.enter
  xrun [hg.rdi, sx_ofNat ho]

/-- Return through the child's parent link; all parent fields and operand
buffers retain the memory frame established by the arithmetic routine. -/
theorem leave_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv parentMinv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv)
    (hp : word s.mem B (8 * sMinv) = parentMinv) :
    WP isa (.block [Crt.leave]) s fun t =>
      Good t B Z w parentMinv ∧ t.mem = s.mem ∧ Keep [.rdi] s t := by
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hdi, hm⟩, hk⟩ =>
      ⟨⟨hc.scr.congr hk.2.2, hdi, ⟨hm ▸ hc.nw, hm ▸ hp, hm ▸ hc.narr⟩⟩, hm, hk⟩
  unfold Crt.leave
  xrun [State.ea, hdr, hc.rdi, hdrOff, hc.link,
    hc.good.scr.ld (show 8 * Crt.sLink + 8 ≤ slot wx 8 from hdr_lt_slot wx 8 (by decide))]

end VG.Proof.Dsa.X86_64

end

end

/-! # Returning an encoded DSA arithmetic result to the parent workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Internal DSA calls may use the arithmetic registers and temporarily
switch rdi to the child workspace. The enclosing entry point saves the ABI. -/
def coreRegs : List Reg := .rdi :: mmRegs

/-- Encode the arithmetic result, restore the parent workspace pointer,
and preserve every word in the active prefix. -/
theorem finish_ok {s : State} {B : Addr} {Z o w wx k : Nat} {minv parentMinv : BitVec 64}
    {out : Addr} (hc : SubCtx s B Z o w wx minv)
    (hpm : word s.mem B (8 * sMinv) = parentMinv)
    (hp : word s.mem B (8 * result) = out)
    (hl : word s.mem B (8 * resultLen) = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (out + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j)) :
    WP isa (seqs Core.finish) s fun t =>
      Good t B Z w parentMinv ∧
      Spec.Rsa.bytesAt t.mem out k = Spec.Dsa.encodeBE k (wv s.mem (off B o) (slot wx aY) wx) ∧
      (∀ d, d + 8 ≤ Z → word t.mem B d = word s.mem B d) ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧ Keep coreRegs s t := by
  unfold Core.finish seqs
  refine WP.seq (WP.mono (storeSuffix_ok hc (by decide) (by decide) (by decide)
    hp hl hk1 hk' hkw hout hprefix) fun u ⟨hcu, huout, hwrd, _, hfu, hku⟩ => ?_)
  have hpmu : word u.mem B (8 * sMinv) = parentMinv :=
    (hwrd _ (by have := hc.lo; have := hc.hi; have := hdr_lt_slot w 8 (show sMinv < 32 by decide); omega_arith)).trans hpm
  refine WP.mono (leave_ok hcu hpmu) fun t ⟨hgt, hmem, hkt⟩ =>
    ⟨hgt, hmem ▸ huout, hmem ▸ hwrd, hmem ▸ hfu, (hku.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # Composing DSA arithmetic with result encoding and workspace return -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

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
    hk1 hk' hkw (fun j hj => by rw [hku.2.2]; exact hout j hj) hprefix)
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

end VG.Proof.Dsa.X86_64
