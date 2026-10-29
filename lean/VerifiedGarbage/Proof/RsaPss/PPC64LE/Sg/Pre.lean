module

public import VerifiedGarbage.Spec.RsaPss.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
public import VerifiedGarbage.Impl.RsaPss.PPC64LE.Sign
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS signing on PPC64LE: the precondition

Untrusted: everything here is checked by Lean. `PreS D s`: the shared
contract's precondition (`Spec.RsaPss.signContract`, with the stack of the
frames and of `vg_rsa_private_checked`, `stackBytes`), by name (`preS_of`),
for a digest of `D` bytes; the working space `Ss s` and the values the code
keeps in `r15`–`r23` (`vS s`), both functions of the entry state `s` alone,
as `Base` takes them, all public; and `Fits` for any state with `s`'s stack
pointer and regions.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Proof.RsaOaep.PPC64LE

theorem stackArgs_thirteen (s : State) :
    List.map (stackArg s) (List.range 13) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12] := rfl

/-- The stack the function uses: its frame (`frameBytes`), the private
operation's (`privBytes`) and that function's own. -/
def stackBytes : Nat := frameBytes + privBytes + Impl.Rsa.PPC64LE.Priv.frameBytes

theorem stackBytes_eq : stackBytes = 3776 := rfl

/-! ## The buffers -/

abbrev oR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
abbrev pR (s : State) : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
abbrev qR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
abbrev dpR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
abbrev dqR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
abbrev qiR (s : State) : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
abbrev dgR (D : Nat) (s : State) : Region := ⟨stackArg s 8, D⟩
abbrev sR (s : State) : Region := ⟨stackArg s 9, (stackArg s 10).toNat⟩
abbrev scR (s : State) : Region := ⟨stackArg s 11, (stackArg s 12).toNat * 8⟩
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 104⟩

/-- The stack the function uses. -/
abbrev kS (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩

/-- What the code needs of `signContract.pre`, by name. -/
structure PreS (D : Nat) (s : State) : Prop where
  sp1 : stackBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + 200 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, pR s, qR s, dpR s, dqR s, qiR s, dgR D s, sR s, aR s]
  hwr : s.wr = [oR s, scR s]
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  op : (oR s).Disjoint (pR s)
  oq : (oR s).Disjoint (qR s)
  odp : (oR s).Disjoint (dpR s)
  odq : (oR s).Disjoint (dqR s)
  oqi : (oR s).Disjoint (qiR s)
  odg : (oR s).Disjoint (dgR D s)
  osl : (oR s).Disjoint (sR s)
  os : (oR s).Disjoint (scR s)
  oa : (oR s).Disjoint (aR s)
  ns : (nR s).Disjoint (scR s)
  es : (eR s).Disjoint (scR s)
  ps : (pR s).Disjoint (scR s)
  qs : (qR s).Disjoint (scR s)
  dps : (dpR s).Disjoint (scR s)
  dqs : (dqR s).Disjoint (scR s)
  qis : (qiR s).Disjoint (scR s)
  dgs : (dgR D s).Disjoint (scR s)
  sls : (sR s).Disjoint (scR s)
  sa : (scR s).Disjoint (aR s)
  ko : (kS s).Disjoint (oR s)
  kn : (kS s).Disjoint (nR s)
  ke : (kS s).Disjoint (eR s)
  kp : (kS s).Disjoint (pR s)
  kq : (kS s).Disjoint (qR s)
  kdp : (kS s).Disjoint (dpR s)
  kdq : (kS s).Disjoint (dqR s)
  kqi : (kS s).Disjoint (qiR s)
  kdg : (kS s).Disjoint (dgR D s)
  ksl : (kS s).Disjoint (sR s)
  ks : (kS s).Disjoint (scR s)
  ka : (kS s).Disjoint (aR s)
  wo : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  wn : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  we : (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  wp : (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64
  wq : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wdp : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wdq : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  wqi : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64
  wdg : (stackArg s 8).toNat + D ≤ 2 ^ 64
  wsl : (stackArg s 9).toNat + (stackArg s 10).toNat ≤ 2 ^ 64
  wsc : (stackArg s 11).toNat + (stackArg s 12).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .r6).toNat
  k2 : (s.gpr .r6).toNat ≤ 1024
  ok : (s.gpr .r4).toNat = (s.gpr .r6).toNat
  e1 : 1 ≤ (s.gpr .r8).toNat
  e2 : (s.gpr .r8).toNat ≤ (s.gpr .r6).toNat
  p1 : 1 ≤ (s.gpr .r10).toNat
  p2 : (s.gpr .r10).toNat < (s.gpr .r6).toNat
  q1 : 1 ≤ (stackArg s 1).toNat
  q2 : (stackArg s 1).toNat < (s.gpr .r6).toNat
  h3 : (stackArg s 3).toNat = (s.gpr .r10).toNat
  h7 : (stackArg s 7).toNat = (s.gpr .r10).toNat
  h5 : (stackArg s 5).toNat = (stackArg s 1).toNat
  hs : Spec.RsaPss.scratchWords (s.gpr .r6).toNat ≤ (stackArg s 12).toNat

theorem preS_of {G : Spec.Mgf1.Hash} {s : State}
    (h : (Spec.RsaPss.signContract G G abi stackBytes).pre s) : PreS G.len s := by
  have e : stackBytes = 3775 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs,
    stackArgs_thirteen, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp1, sp2, hrd, hwr, on, oe, op, oq, odp, odq, oqi, odg, osl, os, oa, ns, es, ps, qs, dps, dqs, qis, dgs,
    sls, sa, ko, kn, ke, kp, kq, kdp, kdq, kqi, kdg, ksl, ks, ka, wo, wn, we, wp, wq, wdp, wdq, wqi, wdg, wsl, wsc,
    ⟨k1, k2⟩, ok, e1, e2, p1, p2, q1, q2, h3, h7, h5, hs⟩ := h
  exact ⟨sp1, by omega, hrd, hwr, on, oe, op, oq, odp, odq, oqi, odg, osl, os, oa, ns, es, ps, qs, dps, dqs, qis, dgs,
    sls, sa, ko, kn, ke, kp, kq, kdp, kdq, kqi, kdg, ksl, ks, ka, wo, wn, we, wp, wq, wdp, wdq, wqi, wdg, wsl, wsc,
    k1, k2, ok, e1, e2, p1, p2, q1, q2, h3, h7, h5, hs⟩

/-! ## The working space and the registers the code keeps -/

/-- The working space. -/
abbrev Ss (s : State) : Addr := stackArg s 11

/-- `k`. -/
abbrev kk (s : State) : Nat := (s.gpr .r6).toNat

/-- `lo` of the modulus' first byte: 1 if `emLen = k - 1`. -/
def loS (s : State) : BitVec 64 :=
  let a := (s.mem (s.gpr .r5)).setWidth 64 >>> 1
  let b := a ||| a >>> 1
  let c := b ||| b >>> 2
  ((c ||| c >>> 4) - BitVec.ofNat 64 1) >>> 63

/-- The values `Base` fixes in `r15`–`r23`: `k`, `out`, `p`, `p_len`,
`salt_len`, `n`, `e`, `e_len` and `lo`. -/
def vS (s : State) : Reg → BitVec 64
  | .r15 => s.gpr .r6
  | .r16 => s.gpr .r3
  | .r17 => s.gpr .r9
  | .r18 => s.gpr .r10
  | .r19 => stackArg s 10
  | .r20 => s.gpr .r5
  | .r21 => s.gpr .r7
  | .r22 => s.gpr .r8
  | .r23 => loS s
  | _ => 0

section
variable {D : Nat} {s : State} (P : PreS D s)
include P

theorem scLen : oRsa ≤ (stackArg s 12).toNat * 8 := by
  have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; unfold oRsa; omega

theorem sc_sub : Region.Sub (SC Ss s) (scR s) := Region.sub_prefix (scLen P)

omit P in
theorem kR_sub : Region.Sub (kR s) (kS s) := below_sub (by rw [stackBytes_eq]; decide) (by rw [stackBytes_eq]; decide)

/-- `Fits` for any state with the entry's stack pointer, regions and stack
arguments. -/
theorem fits : Fits Ss s where
  sp1 := by have := P.sp1; rw [stackBytes_eq] at this; omega
  sc := ⟨scR s, by rw [P.hwr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl, scLen P⟩
  ksc := (P.ks.sub_left kR_sub).sub_right (sc_sub P)
  wS := by show (stackArg s 11).toNat + oRsa ≤ 2 ^ 64; have := P.wsc; have := scLen P; omega

end

section
variable {s t : State} (h : Base Ss vS s t)
include h

theorem Base.r15 : t.gpr .r15 = s.gpr .r6 := h.vs .r15 (by decide)
theorem Base.r16 : t.gpr .r16 = s.gpr .r3 := h.vs .r16 (by decide)
theorem Base.r17 : t.gpr .r17 = s.gpr .r9 := h.vs .r17 (by decide)
theorem Base.r18 : t.gpr .r18 = s.gpr .r10 := h.vs .r18 (by decide)
theorem Base.r19 : t.gpr .r19 = stackArg s 10 := h.vs .r19 (by decide)
theorem Base.r20 : t.gpr .r20 = s.gpr .r5 := h.vs .r20 (by decide)
theorem Base.r21 : t.gpr .r21 = s.gpr .r7 := h.vs .r21 (by decide)
theorem Base.r22 : t.gpr .r22 = s.gpr .r8 := h.vs .r22 (by decide)
theorem Base.r23 : t.gpr .r23 = loS s := h.vs .r23 (by decide)

end

end VG.Proof.RsaPss.PPC64LE.Sg
