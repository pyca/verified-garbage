module

public import VerifiedGarbage.Proof.RsaPss.EncodingContract
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPre
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# EMSA-PSS's encoding on AArch64: the precondition

`PreE D s`: the shared contract's precondition (`encodeContract`, with the
stack `stk 16` of the frame and the hash functions' calls), by name
(`preE_of`). The frame is that of signing (`Sgn.fb`); every argument is in a
register.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64.Sgn (stk kR fb kb frame_sub0)

/-- The stack `encode` uses: its frame, and the 16 bytes below it that the
hash functions' calls use. -/
abbrev encStack : Nat := stk 16

/-- The buffers: `em`, the digest, the salt and the working space. -/
abbrev emR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
abbrev dgR (D : Nat) (s : State) : Region := ⟨s.gpr .x2, D⟩
abbrev saR (s : State) : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
abbrev sR (s : State) : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat * 8⟩

/-- What the code needs of `encodeContract.pre`, by name. -/
structure PreE (D : Nat) (s : State) : Prop where
  sp1 : encStack ≤ s.sp.toNat
  hrd : s.rd = [dgR D s, saR s]
  hwr : s.wr = [emR s, sR s]
  ed : (emR s).Disjoint (dgR D s)
  esa : (emR s).Disjoint (saR s)
  es : (emR s).Disjoint (sR s)
  ds : (dgR D s).Disjoint (sR s)
  sas : (saR s).Disjoint (sR s)
  ke : (kR 16 s).Disjoint (emR s)
  kd : (kR 16 s).Disjoint (dgR D s)
  ksa : (kR 16 s).Disjoint (saR s)
  ks : (kR 16 s).Disjoint (sR s)
  we : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  wd : (s.gpr .x2).toNat + D ≤ 2 ^ 64
  wsa : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64
  ws : (s.gpr .x6).toNat + (s.gpr .x7).toNat * 8 ≤ 2 ^ 64
  b1 : 1 ≤ (s.gpr .x5).toNat
  b2 : (s.gpr .x5).toNat ≤ Proof.RsaPss.maxEmBits
  hel : (s.gpr .x1).toNat = Spec.RsaPss.emLength (s.gpr .x5).toNat
  hs : 1024 ≤ (s.gpr .x7).toNat

theorem preE_of (G : Spec.Mgf1.Hash) {s : State} (h : (Proof.RsaPss.encodeContract G G abi encStack).pre s) :
    PreE G.len s := by
  have e : encStack = (frameBytes + 16 - 1) + 1 := by unfold encStack stk frameBytes; omega
  rw [e] at h
  sig_pre [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, List.append_eq] at h
  sig_pre [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, List.append_eq] at h
  obtain ⟨sp1, hrd, hwr, ed, esa, es, ds, sas, ke, kd, ksa, ks, we, wd, wsa, ws, b1, b2, hel, hs⟩ := h
  rw [← e] at sp1 ke kd ksa ks
  exact ⟨sp1, hrd, hwr, ed, esa, es, ds, sas, ke, kd, ksa, ks, we, wd, wsa, ws, b1, b2, hel, hs⟩

variable {D : Nat} {s : State}

theorem PreE.k1 (hp : PreE D s) : 1 ≤ (s.gpr .x1).toNat := by
  have := hp.hel; have := hp.b1; unfold Spec.RsaPss.emLength at *; omega

theorem PreE.k2 (hp : PreE D s) : (s.gpr .x1).toNat ≤ 1024 := by
  have := hp.hel; have := hp.b2; unfold Spec.RsaPss.emLength Proof.RsaPss.maxEmBits at *; omega

/-- `z = 8 emLen - emBits`, the bits of `em` above `emBits`, is below 8. -/
theorem PreE.z (hp : PreE D s) : (s.gpr .x5).toNat ≤ 8 * (s.gpr .x1).toNat ∧
    8 * (s.gpr .x1).toNat - (s.gpr .x5).toNat < 8 := by
  have := hp.hel; unfold Spec.RsaPss.emLength at *; omega

theorem fb_toNat (hp : PreE D s) : (fb s).toNat + frameBytes = s.sp.toNat := by
  have := hp.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold encStack stk at this; omega

theorem kb_toNat (hp : PreE D s) : (kb 16 s).toNat + encStack = s.sp.toNat := by
  have := hp.sp1
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]
  unfold encStack stk frameBytes at *
  omega

end VG.Proof.RsaPss.AArch64.Enc
