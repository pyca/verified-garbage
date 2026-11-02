module

public import VerifiedGarbage.Proof.RsaPss.EncodingContract
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPre
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# EMSA-PSS's check of an encoding on AArch64: the precondition

`PreC D s`: the shared contract's precondition (`checkEncodingContract`,
with the stack `stk 16` of the frame and the hash functions' calls), by name
(`preC_of`). The frame is that of signing (`Sgn.fb`); every argument is in a
register.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Chk

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64.Sgn (stk kR fb kb)

/-- The stack `checkEncoding` uses: its frame, and the 16 bytes below it that
the hash functions' calls use. -/
abbrev chkStack : Nat := stk 16

/-- The buffers: the digest, `em` and the working space. -/
abbrev dgR (D : Nat) (s : State) : Region := ⟨s.gpr .x0, D⟩
abbrev emR (s : State) : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
abbrev sR (s : State) : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat * 8⟩

/-- What the code needs of `checkEncodingContract.pre`, by name. -/
structure PreC (D : Nat) (s : State) : Prop where
  sp1 : chkStack ≤ s.sp.toNat
  hrd : s.rd = [dgR D s, emR s]
  hwr : s.wr = [sR s]
  ds : (dgR D s).Disjoint (sR s)
  es : (emR s).Disjoint (sR s)
  kd : (kR 16 s).Disjoint (dgR D s)
  ke : (kR 16 s).Disjoint (emR s)
  ks : (kR 16 s).Disjoint (sR s)
  wd : (s.gpr .x0).toNat + D ≤ 2 ^ 64
  we : (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  ws : (s.gpr .x6).toNat + (s.gpr .x7).toNat * 8 ≤ 2 ^ 64
  b1 : 1 ≤ (s.gpr .x3).toNat
  b2 : (s.gpr .x3).toNat ≤ Proof.RsaPss.maxEmBits
  hel : (s.gpr .x2).toNat = Spec.RsaPss.emLength (s.gpr .x3).toNat
  hs : 1024 ≤ (s.gpr .x7).toNat

theorem preC_of (G : Spec.Mgf1.Hash) {s : State} (h : (Proof.RsaPss.checkEncodingContract G G abi chkStack).pre s) :
    PreC G.len s := by
  have e : chkStack = (frameBytes + 16 - 1) + 1 := by unfold chkStack stk frameBytes; omega
  rw [e] at h
  sig_pre [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, List.append_eq] at h
  sig_pre [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, List.append_eq] at h
  obtain ⟨sp1, hrd, hwr, ds, es, kd, ke, ks, wd, we, ws, b1, b2, hel, hs⟩ := h
  rw [← e] at sp1 kd ke ks
  exact ⟨sp1, hrd, hwr, ds, es, kd, ke, ks, wd, we, ws, b1, b2, hel, hs⟩

variable {D : Nat} {s : State}

theorem PreC.k1 (hp : PreC D s) : 1 ≤ (s.gpr .x2).toNat := by
  have := hp.hel; have := hp.b1; unfold Spec.RsaPss.emLength at *; omega

theorem PreC.k2 (hp : PreC D s) : (s.gpr .x2).toNat ≤ 1024 := by
  have := hp.hel; have := hp.b2; unfold Spec.RsaPss.emLength Proof.RsaPss.maxEmBits at *; omega

/-- `z = 8 emLen - emBits`, the bits of `em` above `emBits`, is below 8. -/
theorem PreC.z (hp : PreC D s) : (s.gpr .x3).toNat ≤ 8 * (s.gpr .x2).toNat ∧
    8 * (s.gpr .x2).toNat - (s.gpr .x3).toNat < 8 := by
  have := hp.hel; unfold Spec.RsaPss.emLength at *; omega

theorem fb_toNat (hp : PreC D s) : (fb s).toNat + frameBytes = s.sp.toNat := by
  have := hp.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold chkStack stk at this; omega

end VG.Proof.RsaPss.AArch64.Chk
