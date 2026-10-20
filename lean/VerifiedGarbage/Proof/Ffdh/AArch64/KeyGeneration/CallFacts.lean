module
public import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Data

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # Where the attempt's buffers are, from the controller's (AArch64)

The attempt's buffers are the controller's (`x`, `y`, the domain, a slice
of the tape and the working space), and its stack arguments are in the
attempt's frame, in the 48 bytes of stack below the controller's stack
pointer on entry, which no buffer overlaps.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.KeyGeneration

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

/-- The stack pointer in the attempt's frame. -/
abbrev callSp (p : KeyPublic) : Addr := p.sp - 16 - BitVec.ofNat 64 32

theorem callSp_eq (p : KeyPublic) : callSp p = p.sp - BitVec.ofNat 64 48 := by
  rw [callSp, BitVec.sub_sub]; rfl

/-- The attempt's regions: its outputs, the domain, the tape's slice, the
working space and its arguments. -/
abbrev rX (p : KeyPublic) : Region := ⟨p.xp, p.len⟩
abbrev rY (p : KeyPublic) : Region := ⟨p.yp, p.len⟩
abbrev rD (p : KeyPublic) : Region := ⟨p.dp, p.dlen⟩
abbrev rR (p : KeyPublic) (used : Nat) : Region := ⟨p.rp + BitVec.ofNat 64 used, p.len⟩
abbrev rS (p : KeyPublic) : Region := ⟨p.B, p.Z⟩
abbrev rA (p : KeyPublic) : Region := ⟨callSp p, 24⟩

structure CallFacts (p : KeyPublic) (used : Nat) : Prop where
  room : 48 ≤ p.sp.toNat
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

theorem rA_sub (p : KeyPublic) : Region.Sub (rA p) (below p.sp stackUse) := by
  rw [rA, callSp_eq]; exact Offset.sub_below _ (by decide) (by decide)

theorem KeyLive.callFacts {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen) :
    CallFacts p used := by
  have hi := h.input
  obtain ⟨_, hsp, _, _, hnw, hpw, hwr, hstk, hlen, hdlen, hx1, hx3, hscr, -, -, -, -⟩ := hi.1
  cases hi.2
  simp only [inWrites, inReads, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.cons_append, List.nil_append, List.Pairwise.nil,
    and_true] at hnw hpw hwr hstk
  obtain ⟨⟨pxy, pxu, pxs, pxc⟩, ⟨pyu, pys, pyc⟩, ⟨pus, puc⟩, psc⟩ := hpw
  obtain ⟨⟨wxd, wxr, wxa⟩, ⟨wyd, wyr, wya⟩, -, ⟨wsd, wsr, wsa⟩, -⟩ := hwr
  obtain ⟨bx, by', -, bs, -, bd, br, -⟩ := hstk
  obtain ⟨nx, ny, -, ns, -, nd, nr, -⟩ := hnw
  have hX : rX (keyOfState original) = inX original := by
    simp only [rX, inX, keyOfState, hx1]
  have hY : rY (keyOfState original) = inY original := by
    simp only [rY, inY, keyOfState, hx3]
  have hD : rD (keyOfState original) = inDom original := rfl
  have hS : rS (keyOfState original) = inScr original := rfl
  have hR : Region.Sub (rR (keyOfState original) used) (inRand original) :=
    sub_tape hroom
  have hA := rA_sub (keyOfState original)
  have hsp' : (keyOfState original).sp = original.sp := rfl
  rw [hsp'] at hA
  rw [← hX] at pxy pxs wxd wxr bx nx
  rw [← hY] at pxy pys wyd wyr by' ny
  rw [← hD] at wxd wyd wsd bd nd
  rw [← hS] at pxs pys wsd wsr bs ns
  refine ⟨by rw [hsp']; exact hsp, pxy, wxd, wxr.sub_right hR, pxs, (bx.symm.sub_right hA),
    wyd, wyr.sub_right hR, pys, by'.symm.sub_right hA, wsd.symm, (wsr.sub_right hR).symm,
    bs.symm.sub_right hA, nx, ny, nd, nowrap_tape nr hroom, ns, hlen, hdlen, ?_, ?_, ?_, ?_⟩
  · simp only [keyOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
    exact hscr
  · simp only [keyOfState, Nat.mul_div_cancel _ (by decide : 0 < 8)]
  · exact BitVec.isLt _
  · exact BitVec.isLt _

end VG.Proof.Ffdh.AArch64.KeyGeneration
