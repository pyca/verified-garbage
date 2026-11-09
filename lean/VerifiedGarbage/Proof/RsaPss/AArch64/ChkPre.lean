module

public import VerifiedGarbage.Proof.RsaPss.EncodingContract
public import VerifiedGarbage.Proof.RsaPss.AArch64.EncContract
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPre
import VerifiedGarbage.Proof.Framework.Offset

/-!
# EMSA-PSS's check of an encoding on AArch64: the precondition

`PreC D tsH tsG s`: the precondition of `checkEncoding` (`chkK`), with the
stack `stk 288` of the frame, MGF1's frame and the hash functions' calls,
and the tables `tsH` and `tsG` at the stack arguments. The frame is that of
signing (`Sgn.fb`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Chk

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64.Sgn (stk kR fb kb)

/-- The stack `checkEncoding` uses: its frame, and the 288 bytes below it
that MGF1's frame and the hash functions' calls use. -/
abbrev chkStack : Nat := stk 288

/-- The buffers: the digest, `em` and the working space, the tables and the
stack arguments. -/
abbrev dgR (D : Nat) (s : State) : Region := ⟨s.gpr .x0, D⟩
abbrev emR (s : State) : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
abbrev sR (s : State) : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat * 8⟩
abbrev tHR (s : State) : Region := Sig.tableRegion 64 (stackArg s 0) 11
abbrev tGR (s : State) : Region := Sig.tableRegion 64 (stackArg s 1) 5
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- What the code needs at the entry, for the tables `tsH` of `MdHash` and
`tsG` of `Hash`. -/
structure PreC (D : Nat) (tsH tsG : List FnTable) (s : State) : Prop where
  sp1 : chkStack ≤ s.sp.toNat
  sp2 : s.sp.toNat + 16 ≤ 2 ^ 64
  tabH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem (stackArg s 0) (FnTable.words isa s T)
  tabG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem (stackArg s 1) (FnTable.words isa s T)
  hsy : ((tsH.map (·.fns)).flatten ++ (tsG.map (·.fns)).flatten).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g
  hrd : s.rd = [dgR D s, emR s, tHR s, tGR s, aR s]
  hwr : s.wr = [sR s]
  ds : (dgR D s).Disjoint (sR s)
  es : (emR s).Disjoint (sR s)
  stH : (sR s).Disjoint (tHR s)
  stG : (sR s).Disjoint (tGR s)
  sA : (sR s).Disjoint (aR s)
  kd : (kR 288 s).Disjoint (dgR D s)
  ke : (kR 288 s).Disjoint (emR s)
  ks : (kR 288 s).Disjoint (sR s)
  ktH : (kR 288 s).Disjoint (tHR s)
  ktG : (kR 288 s).Disjoint (tGR s)
  kA : (kR 288 s).Disjoint (aR s)
  wd : (s.gpr .x0).toNat + D ≤ 2 ^ 64
  we : (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  ws : (s.gpr .x6).toNat + (s.gpr .x7).toNat * 8 ≤ 2 ^ 64
  wtH : (stackArg s 0).toNat + 88 ≤ 2 ^ 64
  wtG : (stackArg s 1).toNat + 40 ≤ 2 ^ 64
  b1 : 1 ≤ (s.gpr .x3).toNat
  b2 : (s.gpr .x3).toNat ≤ Proof.RsaPss.maxEmBits
  hel : (s.gpr .x2).toNat = Spec.RsaPss.emLength (s.gpr .x3).toNat
  hs : Proof.RsaPss.encScratch ≤ (s.gpr .x7).toNat

variable {D : Nat} {tsH tsG : List FnTable} {s : State}

theorem PreC.k1 (hp : PreC D tsH tsG s) : 1 ≤ (s.gpr .x2).toNat := by
  have := hp.hel; have := hp.b1; unfold Spec.RsaPss.emLength at *; omega

theorem PreC.k2 (hp : PreC D tsH tsG s) : (s.gpr .x2).toNat ≤ 1024 := by
  have := hp.hel; have := hp.b2; unfold Spec.RsaPss.emLength Proof.RsaPss.maxEmBits at *; omega

/-- `z = 8 emLen - emBits`, the bits of `em` above `emBits`, is below 8. -/
theorem PreC.z (hp : PreC D tsH tsG s) : (s.gpr .x3).toNat ≤ 8 * (s.gpr .x2).toNat ∧
    8 * (s.gpr .x2).toNat - (s.gpr .x3).toNat < 8 := by
  have := hp.hel; unfold Spec.RsaPss.emLength at *; omega

theorem fb_toNat (hp : PreC D tsH tsG s) : (fb s).toNat + frameBytes = s.sp.toNat := by
  have := hp.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold chkStack stk at this; omega

end VG.Proof.RsaPss.AArch64.Chk
