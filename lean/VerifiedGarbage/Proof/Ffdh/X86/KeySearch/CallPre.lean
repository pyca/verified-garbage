module

public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Frame
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Ffdh.X86.ABI
import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Entry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig

/-! # The attempt's precondition (x86)

With its eleven arguments in the frame (`ArgsAt`), `vg_ffdh_generate_key`'s
contract holds on its entry, narrowed to the domain and the tape's next
`p_len` octets, which it reads, and to the outputs, the working space and
its frame of arguments, which it writes (`call_pre`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.KeySearch
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The tape's next `p_len` octets. -/
abbrev winR (o : State) (used : Nat) : Region := ⟨(arg o 8 + BitVec.ofNat 32 used).setWidth 64, (arg o 7).toNat⟩

/-- What the callee may read and write. -/
abbrev callRd (o : State) (used : Nat) : List Region := [dR o, winR o used]
abbrev callWr (o : State) : List Region :=
  [⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩, ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩, bR o, frR o]

/-- The callee's arguments, on its entry. -/
theorem ce_arg {o t : State} {used : Nat} (A : KeySearchABI o)
    (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) (ha : ArgsAt o used 11 t.mem)
    (rd wr : List Region) {j : Nat} (hj : j < 11) :
    arg (t.callEntry.withRegions rd wr) j = callArg o used j := by
  have h1 : 164 ≤ (o.gpr .esp).toNat := A.stackLow
  have hb := A.stackBound
  have hn : (t.gpr .esp).toNat = (o.gpr .esp).toNat - 44 := by rw [he]; exact VG.X86.sub_toNat (by unfold argsBytes; omega)
  rw [arg_withRegions, arg_callEntry (by omega) (by omega), ← ha j hj]
  congr 1
  rw [show (t.gpr .esp + BitVec.ofNat 32 (4 * j)).setWidth 64 = addr (t.gpr .esp) (4 * j) from rfl, he,
    addr_sub A (by decide) (by unfold argsBytes; omega)]
  rfl

/-- The window's base, at its offset in the tape. -/
theorem win_base {o : State} (A : KeySearchABI o) {used : Nat} (hu : used + (arg o 7).toNat ≤ (arg o 9).toNat) :
    (arg o 8 + BitVec.ofNat 32 used).setWidth 64 = argumentPointer o 8 + BitVec.ofNat 64 used := by
  have := A.rBound
  have := A.pLen
  unfold Spec.Ffdh.pLenValid at this
  exact addr_eq (by omega)

theorem win_toNat {o : State} (A : KeySearchABI o) {used : Nat} (hu : used + (arg o 7).toNat ≤ (arg o 9).toNat) :
    (arg o 8 + BitVec.ofNat 32 used).toNat = (arg o 8).toNat + used := by
  have := A.rBound
  have := A.pLen
  unfold Spec.Ffdh.pLenValid at this
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := used) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem win_sub {o : State} (A : KeySearchABI o) {used : Nat} (hu : used + (arg o 7).toNat ≤ (arg o 9).toNat) :
    Region.Sub (winR o used) (rR o) := by
  rw [winR, win_base A hu]; exact Offset.sub_base _ hu

theorem call_pre {o t : State} {used : Nat} (A : KeySearchABI o) (hu : used + (arg o 7).toNat ≤ (arg o 9).toNat)
    (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) (ha : ArgsAt o used 11 t.mem) :
    (Spec.Ffdh.generateKeyContract abi Proof.Ffdh.X86.stack).pre
      (t.callEntry.withRegions (callRd o used) (callWr o)) := by
  have h1 : 164 ≤ (o.gpr .esp).toNat := A.stackLow
  have hb := A.stackBound
  have hs4 : t.gpr .esp - 4 = o.gpr .esp - BitVec.ofNat 32 48 := by
    rw [he]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, argsBytes]
    have := (o.gpr .esp).isLt
    show (2 ^ 32 - 4 % 2 ^ 32 + (2 ^ 32 - 44 % 2 ^ 32 + (o.gpr .esp).toNat) % 2 ^ 32) % 2 ^ 32 = _
    omega
  have hs4n : (o.gpr .esp - BitVec.ofNat 32 48).toNat = (o.gpr .esp).toNat - 48 := VG.X86.sub_toNat (by omega)
  have ha0 : argAddr (t.callEntry.withRegions (callRd o used) (callWr o)) 0 = low o + BitVec.ofNat 64 120 := by
    rw [argAddr_withRegions, argAddr_callEntry, show 4 * 0 = 0 from rfl, BitVec.add_zero, he,
      sw_sub A (by decide)]; rfl
  have hl116 : (o.gpr .esp - BitVec.ofNat 32 48).setWidth 64 - 116#64 = low o := by
    rw [sw_sub A (by decide)]; show low o + BitVec.ofNat 64 116 - BitVec.ofNat 64 116 = _
    exact BitVec.add_sub_cancel _ _
  have xr := xR_eq A
  have yr := yR_eq A
  have W := win_sub A hu
  have Fs : Region.Sub (frR o) (lowR o) := low_sub (by decide)
  have Rs : Region.Sub ⟨low o + BitVec.ofNat 64 116, 4⟩ (lowR o) := low_sub (by decide)
  have Bs : Region.Sub ⟨low o, 116⟩ (lowR o) := Region.sub_prefix (by decide)
  have dXY : Region.Disjoint ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← xr, ← yr]; exact A.xy
  have dXD : Region.Disjoint ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ (dR o) := by rw [← xr]; exact A.xd
  have dXW : Region.Disjoint ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ (winR o used) := by
    rw [← xr]; exact A.xr.sub_right W
  have dXB : Region.Disjoint ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ (bR o) := by rw [← xr]; exact A.xb
  have dXF : Region.Disjoint ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ (frR o) := by
    rw [← xr]; exact A.lowX.symm.sub_right Fs
  have dYD : Region.Disjoint ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ (dR o) := by rw [← yr]; exact A.yd
  have dYW : Region.Disjoint ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ (winR o used) := by
    rw [← yr]; exact A.yr.sub_right W
  have dYB : Region.Disjoint ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ (bR o) := by rw [← yr]; exact A.yb
  have dYF : Region.Disjoint ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ (frR o) := by
    rw [← yr]; exact A.lowY.symm.sub_right Fs
  have dDB : Region.Disjoint (dR o) (bR o) := A.db
  have dDF : Region.Disjoint (dR o) (frR o) := A.lowD.symm.sub_right Fs
  have dWB : Region.Disjoint (winR o used) (bR o) := A.rb.sub_left W
  have dWF : Region.Disjoint (winR o used) (frR o) := (A.lowRand.symm.sub_left W).sub_right Fs
  have dBF : Region.Disjoint (bR o) (frR o) := A.lowB.symm.sub_right Fs
  have rX : Region.Disjoint ⟨low o + BitVec.ofNat 64 116, 4⟩ ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← xr]; exact A.lowX.sub_left Rs
  have rY : Region.Disjoint ⟨low o + BitVec.ofNat 64 116, 4⟩ ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← yr]; exact A.lowY.sub_left Rs
  have rD : Region.Disjoint ⟨low o + BitVec.ofNat 64 116, 4⟩ (dR o) := A.lowD.sub_left Rs
  have rW : Region.Disjoint ⟨low o + BitVec.ofNat 64 116, 4⟩ (winR o used) := (A.lowRand.sub_left Rs).sub_right W
  have rB : Region.Disjoint ⟨low o + BitVec.ofNat 64 116, 4⟩ (bR o) := A.lowB.sub_left Rs
  have rF : Region.Disjoint ⟨low o + BitVec.ofNat 64 116, 4⟩ (frR o) :=
    Offset.disjoint _ (by omega) (by omega) (by omega)
  have bX : Region.Disjoint ⟨low o, 116⟩ ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← xr]; exact A.lowX.sub_left Bs
  have bY : Region.Disjoint ⟨low o, 116⟩ ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← yr]; exact A.lowY.sub_left Bs
  have bD : Region.Disjoint ⟨low o, 116⟩ (dR o) := A.lowD.sub_left Bs
  have bW : Region.Disjoint ⟨low o, 116⟩ (winR o used) := (A.lowRand.sub_left Bs).sub_right W
  have bB : Region.Disjoint ⟨low o, 116⟩ (bR o) := A.lowB.sub_left Bs
  have bF : Region.Disjoint ⟨low o, 116⟩ (frR o) := Offset.base_disjoint _ (by omega) (by omega)
  have xB : (arg o 0).toNat + (arg o 7).toNat ≤ 2 ^ 32 := by have := A.xBound; rw [A.xLen] at this; exact this
  have yB : (arg o 2).toNat + (arg o 7).toNat ≤ 2 ^ 32 := by have := A.yBound; rw [A.yLen] at this; exact this
  have wB : (arg o 8 + BitVec.ofNat 32 used).toNat + (arg o 7).toNat ≤ 2 ^ 32 := by
    rw [win_toNat A hu]; have := A.rBound; omega
  have dB := A.dBound
  have sB := A.bBound
  have pL := A.pLen
  have dL := A.dLen
  have sL := A.scratchLength
  have st : Proof.Ffdh.X86.stack ≤ (o.gpr .esp - BitVec.ofNat 32 48).toNat := by
    rw [hs4n]; show 116 ≤ _; omega
  have st' : (o.gpr .esp - BitVec.ofNat 32 48).toNat + 4 + 44 ≤ 2 ^ 32 := by rw [hs4n]; omega
  sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [hs4, ha0, Nat.reduceEqDiff, Nat.reduceSub, ↓reduceIte, BitVec.add_sub_cancel, ce_arg A he ha _ _ (show 0 < 11 by decide), ce_arg A he ha _ _ (show 1 < 11 by decide),
    ce_arg A he ha _ _ (show 2 < 11 by decide), ce_arg A he ha _ _ (show 3 < 11 by decide),
    ce_arg A he ha _ _ (show 4 < 11 by decide), ce_arg A he ha _ _ (show 5 < 11 by decide),
    ce_arg A he ha _ _ (show 6 < 11 by decide), ce_arg A he ha _ _ (show 7 < 11 by decide),
    ce_arg A he ha _ _ (show 8 < 11 by decide), ce_arg A he ha _ _ (show 9 < 11 by decide),
    ce_arg A he ha _ _ (show 10 < 11 by decide), callArg, sw_sub A (show 48 ≤ 164 by decide)]
  sig_and_intros
  all_goals first
    | exact True.intro
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›

end VG.Proof.Ffdh.X86.KeySearch
