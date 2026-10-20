module
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Data
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline

import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Where the attempt's buffers are, from the controller's

The attempt's buffers are the controller's (`x`, `y`, the domain, a slice
of the tape and the working space), and its stack arguments, return
address and its callee's return address are in the 56 octets of stack below
the controller's return address, which no buffer overlaps.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The attempt's regions: its outputs, the domain, the tape's slice, the
working space, its arguments; its return address and its callee's. -/
abbrev rX (p : KeyPublic) : Region := ⟨p.xp, p.len⟩
abbrev rY (p : KeyPublic) : Region := ⟨p.yp, p.len⟩
abbrev rD (p : KeyPublic) : Region := ⟨p.dp, p.dlen⟩
abbrev rR (p : KeyPublic) (used : Nat) : Region := ⟨p.rp + BitVec.ofNat 64 used, p.len⟩
abbrev rS (p : KeyPublic) : Region := ⟨p.B, p.Z⟩
abbrev rA (p : KeyPublic) : Region := ⟨p.sp - 40, 40⟩
abbrev rRet (p : KeyPublic) : Region := ⟨p.sp - 40 - 8, 8⟩
abbrev rHole (p : KeyPublic) : Region := hole (p.sp - 40 - 8)

structure CallFacts (p : KeyPublic) (used : Nat) : Prop where
  room : 56 ≤ p.sp.toNat
  xy : (rX p).Disjoint (rY p)
  xd : (rX p).Disjoint (rD p)
  xr : (rX p).Disjoint (rR p used)
  xs : (rX p).Disjoint (rS p)
  xa : (rX p).Disjoint (rA p)
  yd : (rY p).Disjoint (rD p)
  yr : (rY p).Disjoint (rR p used)
  ys : (rY p).Disjoint (rS p)
  ya : (rY p).Disjoint (rA p)
  ds : (rD p).Disjoint (rS p)
  rs : (rR p used).Disjoint (rS p)
  sa : (rS p).Disjoint (rA p)
  nx : p.xp.toNat + p.len ≤ 2 ^ 64
  ny : p.yp.toNat + p.len ≤ 2 ^ 64
  nd : p.dp.toNat + p.dlen ≤ 2 ^ 64
  nr : (p.rp + BitVec.ofNat 64 used).toNat + p.len ≤ 2 ^ 64
  ns : p.B.toNat + p.Z ≤ 2 ^ 64
  ret : ∀ r ∈ [rX p, rY p, rD p, rR p used, rS p, rA p], (rRet p).Disjoint r
  hole : ∀ r ∈ [rX p, rY p, rD p, rR p used, rS p, rA p], r.Disjoint (rHole p)
  len : Spec.Ffdh.pLenValid p.len
  dlen : Spec.Ffdh.domainLenValid p.len p.dlen
  scratch : Spec.Rsa.scratchWords p.len ≤ p.Z / 8
  z8 : p.Z / 8 * 8 = p.Z
  len64 : p.len < 2 ^ 64
  dlen64 : p.dlen < 2 ^ 64

private theorem sub_tape {r : Addr} {n used len : Nat}
    (hu : used + len ≤ n) : Region.Sub ⟨r + BitVec.ofNat 64 used, len⟩ ⟨r, n⟩ :=
  Offset.sub_base r hu

private theorem nowrap_tape {r : Addr} {n used len : Nat} (hn : r.toNat + n ≤ 2 ^ 64)
    (hu : used + len ≤ n) : (r + BitVec.ofNat 64 used).toNat + len ≤ 2 ^ 64 := by
  have hul : used < 2 ^ 64 ∨ len = 0 := by omega
  rcases hul with hul | hz
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hul]
    have := Nat.mod_le (r.toNat + used) (2 ^ 64)
    by_cases hz : r.toNat + used < 2 ^ 64
    · rw [Nat.mod_eq_of_lt hz]; omega
    · omega
  · subst hz; simp only [Nat.add_zero]; exact Nat.le_of_lt (BitVec.isLt _)

private theorem sp_48 (sp : Addr) : sp - 40 - 8 = sp - BitVec.ofNat 64 48 := by
  rw [BitVec.sub_sub]; rfl

private theorem sp_56 (sp : Addr) : sp - 40 - 8 - 8 = sp - BitVec.ofNat 64 56 := by
  rw [BitVec.sub_sub, BitVec.sub_sub]; rfl

private theorem sp_40 (sp : Addr) : sp - 40 = sp - BitVec.ofNat 64 40 := rfl

theorem rRet_sub (p : KeyPublic) : Region.Sub (rRet p) (below p.sp stackUse) := by
  rw [rRet, sp_48]; exact Offset.sub_below _ (by decide) (by decide)

theorem rA_sub (p : KeyPublic) : Region.Sub (rA p) (below p.sp stackUse) := by
  rw [rA, sp_40]; exact Offset.sub_below _ (by decide) (by decide)

theorem rHole_sub (p : KeyPublic) : Region.Sub (rHole p) (below p.sp stackUse) := by
  rw [rHole, hole, sp_56]; exact Offset.sub_below _ (by decide) (by decide)

theorem ret_args (p : KeyPublic) : (rRet p).Disjoint (rA p) := by
  have := Offset.base_disjoint (p.sp - 40 - 8) (k := 8) (e := 8) (n := 40) (by decide) (by decide)
  rwa [show p.sp - 40 - 8 + BitVec.ofNat 64 8 = p.sp - 40 from BitVec.sub_add_cancel _ _] at this

theorem hole_args (p : KeyPublic) : (rA p).Disjoint (rHole p) := by
  have := Offset.base_disjoint (p.sp - 40 - 8 - 8) (k := 8) (e := 16) (n := 40) (by decide) (by decide)
  rw [show p.sp - 40 - 8 - 8 + BitVec.ofNat 64 16 = p.sp - 40 by
    rw [BitVec.sub_sub (p.sp - 40) 8 8]
    exact BitVec.sub_add_cancel _ _] at this
  exact this.symm

theorem KeyLive.callFacts {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen) :
    CallFacts p used := by
  have hi := h.input
  obtain ⟨_, hsp, _, _, hnw, hpw, hwr, hstk, hlen, hdlen, hrsi, hrcx, hscr, -, -, -, -⟩ := hi.1
  cases hi.2
  simp only [inWrites, inReads, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append, List.Pairwise.nil,
    and_true] at hnw hpw hwr hstk
  obtain ⟨⟨pxy, pxu, pxs, pxc⟩, ⟨pyu, pys, pyc⟩, ⟨pus, puc⟩, psc⟩ := hpw
  obtain ⟨⟨wxd, wxr, wxa⟩, ⟨wyd, wyr, wya⟩, -, ⟨wsd, wsr, wsa⟩, -⟩ := hwr
  obtain ⟨⟨-, bx⟩, ⟨-, by'⟩, -, ⟨-, bs⟩, -, ⟨-, bd⟩, ⟨-, br⟩, -⟩ := hstk
  obtain ⟨nx, ny, -, ns, -, nd, nr, -⟩ := hnw
  have hX : rX (keyOfState original) = inX original := by
    simp only [rX, inX, keyOfState, hrsi]
  have hY : rY (keyOfState original) = inY original := by
    simp only [rY, inY, keyOfState, hrcx]
  have hD : rD (keyOfState original) = inDom original := rfl
  have hS : rS (keyOfState original) = inScr original := rfl
  have hR : Region.Sub (rR (keyOfState original) used) (inRand original) :=
    sub_tape hroom
  have hA := rA_sub (keyOfState original)
  have hRet := rRet_sub (keyOfState original)
  have hH := rHole_sub (keyOfState original)
  have hsp' : (keyOfState original).sp = original.gpr .rsp := rfl
  rw [hsp'] at hA hRet hH
  rw [← hX] at pxy pxs wxd wxr bx nx
  rw [← hY] at pxy pys wyd wyr by' ny
  rw [← hD] at wxd wyd wsd bd nd
  rw [← hS] at pxs pys wsd wsr bs ns
  refine ⟨by rw [hsp']; exact hsp, pxy, wxd, wxr.sub_right hR, pxs, (bx.symm.sub_right hA),
    wyd, wyr.sub_right hR, pys, by'.symm.sub_right hA, wsd.symm, (wsr.sub_right hR).symm,
    bs.symm.sub_right hA, nx, ny, nd, nowrap_tape nr hroom, ns, ?_, ?_, hlen, hdlen, ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bx.sub_left hRet
    · exact by'.sub_left hRet
    · exact bd.sub_left hRet
    · exact (br.sub_left hRet).sub_right hR
    · exact bs.sub_left hRet
    · exact ret_args _
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (bx.sub_left hH).symm
    · exact (by'.sub_left hH).symm
    · exact (bd.sub_left hH).symm
    · exact ((br.sub_left hH).sub_right hR).symm
    · exact (bs.sub_left hH).symm
    · exact hole_args _
  · simp only [keyOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
    exact hscr
  · simp only [keyOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
  · exact BitVec.isLt _
  · exact BitVec.isLt _

end VG.Proof.Ffdh.X86_64.KeyGeneration
