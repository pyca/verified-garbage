module

public import VerifiedGarbage.Proof.RsaPss.AArch64.EncContract
public import VerifiedGarbage.Proof.RsaPss.EncodingContract
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPre
import VerifiedGarbage.Proof.Framework.Offset

/-!
# EMSA-PSS's encoding on AArch64: the precondition

`PreE D tsH tsG s`: the precondition of `encode` (`encK`), with the stack
`stk 288` of the frame, MGF1's frame and the hash functions' calls, and the
tables `tsH` and `tsG` at the stack arguments. The frame is that of signing
(`Sgn.fb`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64.Sgn (stk kR fb kb frame_sub0)

/-- The stack `encode` uses: its frame, and the 288 bytes below it that MGF1's
frame and the hash functions' calls use. -/
abbrev encStack : Nat := stk 288

/-- The buffers: `em`, the digest, the salt and the working space, the
tables and the stack arguments. -/
abbrev emR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
abbrev dgR (D : Nat) (s : State) : Region := ⟨s.gpr .x2, D⟩
abbrev saR (s : State) : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
abbrev sR (s : State) : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat * 8⟩
abbrev tHR (s : State) : Region := Sig.tableRegion 64 (stackArg s 0) 11
abbrev tGR (s : State) : Region := Sig.tableRegion 64 (stackArg s 1) 5
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- What the code needs at the entry, for the tables
`tsH` of `MdHash` and `tsG` of `Hash`. -/
structure PreE (D : Nat) (tsH tsG : List FnTable) (s : State) : Prop where
  sp1 : encStack ≤ s.sp.toNat
  sp2 : s.sp.toNat + 16 ≤ 2 ^ 64
  tabH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem (stackArg s 0) (FnTable.words isa s T)
  tabG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem (stackArg s 1) (FnTable.words isa s T)
  hsy : ((tsH.map (·.fns)).flatten ++ (tsG.map (·.fns)).flatten).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g
  hrd : s.rd = [dgR D s, saR s, tHR s, tGR s, aR s]
  hwr : s.wr = [emR s, sR s]
  ed : (emR s).Disjoint (dgR D s)
  esa : (emR s).Disjoint (saR s)
  es : (emR s).Disjoint (sR s)
  etH : (emR s).Disjoint (tHR s)
  etG : (emR s).Disjoint (tGR s)
  eA : (emR s).Disjoint (aR s)
  ds : (dgR D s).Disjoint (sR s)
  sas : (saR s).Disjoint (sR s)
  stH : (sR s).Disjoint (tHR s)
  stG : (sR s).Disjoint (tGR s)
  sA : (sR s).Disjoint (aR s)
  ke : (kR 288 s).Disjoint (emR s)
  kd : (kR 288 s).Disjoint (dgR D s)
  ksa : (kR 288 s).Disjoint (saR s)
  ks : (kR 288 s).Disjoint (sR s)
  ktH : (kR 288 s).Disjoint (tHR s)
  ktG : (kR 288 s).Disjoint (tGR s)
  kA : (kR 288 s).Disjoint (aR s)
  we : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  wd : (s.gpr .x2).toNat + D ≤ 2 ^ 64
  wsa : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64
  ws : (s.gpr .x6).toNat + (s.gpr .x7).toNat * 8 ≤ 2 ^ 64
  wtH : (stackArg s 0).toNat + 88 ≤ 2 ^ 64
  wtG : (stackArg s 1).toNat + 40 ≤ 2 ^ 64
  b1 : 1 ≤ (s.gpr .x5).toNat
  b2 : (s.gpr .x5).toNat ≤ Proof.RsaPss.maxEmBits
  hel : (s.gpr .x1).toNat = Spec.RsaPss.emLength (s.gpr .x5).toNat
  hs : Proof.RsaPss.encScratch ≤ (s.gpr .x7).toNat

variable {D : Nat} {tsH tsG : List FnTable} {s : State}

theorem PreE.k1 (hp : PreE D tsH tsG s) : 1 ≤ (s.gpr .x1).toNat := by
  have := hp.hel; have := hp.b1; unfold Spec.RsaPss.emLength at *; omega

theorem PreE.k2 (hp : PreE D tsH tsG s) : (s.gpr .x1).toNat ≤ 1024 := by
  have := hp.hel; have := hp.b2; unfold Spec.RsaPss.emLength Proof.RsaPss.maxEmBits at *; omega

/-- `z = 8 emLen - emBits`, the bits of `em` above `emBits`, is below 8. -/
theorem PreE.z (hp : PreE D tsH tsG s) : (s.gpr .x5).toNat ≤ 8 * (s.gpr .x1).toNat ∧
    8 * (s.gpr .x1).toNat - (s.gpr .x5).toNat < 8 := by
  have := hp.hel; unfold Spec.RsaPss.emLength at *; omega

theorem fb_toNat (hp : PreE D tsH tsG s) : (fb s).toNat + frameBytes = s.sp.toNat := by
  have := hp.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold encStack stk at this; omega

theorem kb_toNat (hp : PreE D tsH tsG s) : (kb 288 s).toNat + encStack = s.sp.toNat := by
  have := hp.sp1
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]
  unfold encStack stk frameBytes at *
  omega

end VG.Proof.RsaPss.AArch64.Enc
