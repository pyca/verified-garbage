module

import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecBody
public import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Data.Fintype.Card
public import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecBase
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecFns
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem

/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: verified

The frames around the body (`wrap_ok`, `wrap_ct`), the result as the shared
contract states it, and a state that meets it (`sat`):
`vg_rsa_pkcs1_decrypt`, calling `vg_rsa_private_checked` over any
implementation `v` of `vg_rsa_private_crt` and the ARMv7 SHA-256 and
HMAC-SHA-256 functions, is verified (`code_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm

theorem entered_state {s : State} (h : spec.pre s) :
    S (ep s) (entered frameBytes s) (entered frameBytes s) :=
  ⟨in_of_pre h, ⟨(in_of_pre h).ok, (in_of_pre h).ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem spec_sp {s : State} (h : spec.pre s) : stackBytes ≤ s.sp.toNat := by
  sig_pre [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi,
    argRegs, reduceClassify, Loc.val] at h
  exact h.1

/-- The code, calling `vg_rsa_private_checked` over `v`. -/
abbrev decryptCode (v : Proof.Rsa.Arm.CrtImpl) : Prog isa :=
  code decFns (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)

theorem code_ok (v : Proof.Rsa.Arm.CrtImpl) {s : State} (h : spec.pre s) :
    WP isa (decryptCode v) s fun t => abiPreserved s t ∧ spec.post s t := by
  have hs := spec_sp h
  have hin := in_of_pre h
  have st := entered_state h
  have hsp : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) hs
  have hF : FrameOk frameBytes := by decide
  have hb := (body_vp (P := ep s) v).wp _ _ st
  refine WP.mono (wrap_ok hF (by rw [Nat.add_comm]; exact hsp) (W := (ep s).lay.W)
    (Q := fun r m => Res (ep s) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 76) (C := 3440) (argv := (ep s).argv)
      (ro := [(ep s).N, (ep s).E, (ep s).D, (ep s).INP, (ep s).PP, (ep s).QQ, (ep s).DP, (ep s).DQ, (ep s).QI])
      (rw := [(ep s).OUT, (ep s).ML, (ep s).SCR]) hsp]
    exact hin.ok.push_apart r hr
  · sig_post [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi,
      argRegs, reduceClassify, Loc.val]
    rw [BitVec.setWidth_append_eq_right]
    have ro := fun {R : Region} (hR : R ∈ [(ep s).N, (ep s).E, (ep s).D, (ep s).INP, (ep s).PP, (ep s).QQ,
        (ep s).DP, (ep s).DQ, (ep s).QI]) =>
      entered_ro (F := frameBytes) (A := 76) (C := 3440) (argv := (ep s).argv)
        (rw := [(ep s).OUT, (ep s).ML, (ep s).SCR]) hin.ok hsp hR
    have hD : dB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3))
        (stackArg s 4).toNat := ro (R := (ep s).D) (by simp)
    have hI : cB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 5))
        (stackArg s 0).toNat := ro (R := (ep s).INP) (by simp)
    have hP : pB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 7))
        (stackArg s 8).toNat := ro (R := (ep s).PP) (by simp)
    have hQ : qB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 9))
        (stackArg s 10).toNat := ro (R := (ep s).QQ) (by simp)
    have hDP : dpB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 11))
        (stackArg s 8).toNat := ro (R := (ep s).DP) (by simp)
    have hDQ : dqB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 13))
        (stackArg s 10).toNat := ro (R := (ep s).DQ) (by simp)
    have hQI : qiB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 15))
        (stackArg s 8).toNat := ro (R := (ep s).QI) (by simp)
    unfold Res at res
    rw [hD, hI, hP, hQ, hDP, hDQ, hQI] at res
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

/-- Two entry states with the same public data have the same public parameters. -/
theorem ep_eq {s₁ s₂ : State} (hp : spec.pub s₁ s₂) : ep s₁ = ep s₂ := by
  sig_pub [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi,
    argRegs, reduceClassify, Loc.val] at hp
  obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    a18⟩ := hp
  obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl) (by simp [bytesAt_length, a0])
  simp only [ep]
  rw [hsp, h0, h2, h3, a0, a1, a2, a3, a4, a5, a7, a8, a9, a10, a11, a13, a15, a17, a18]
  rw [h3, a0] at hn
  rw [a1, a2] at he
  rw [show State.addr (s₂.gpr .r3) = BitVec.setWidth 64 (s₂.gpr .r3) from rfl, hn,
    show State.addr (stackArg s₂ 1) = BitVec.setWidth 64 (stackArg s₂ 1) from rfl, he]

theorem code_ct (v : Proof.Rsa.Arm.CrtImpl) : ConstantTime isa spec.pre spec.pub (decryptCode v) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  have hep := ep_eq hp
  have hsp : s₁.sp = s₂.sp := by
    sig_pub [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi,
      argRegs, reduceClassify, Loc.val] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp)
    (fun a b h => by rw [h.1]; exact Nat.le_trans (Nat.le_add_right _ _) (spec_sp h₁)) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp (P := ep s₁) v).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_state h₁, by rw [hep]; exact entered_state h₂⟩

/-- A state that meets the shared contract: a modulus and a ciphertext of 64
bytes, `e`, `d`, `p`, `q`, `dP`, `dQ` and `qInv` of one byte, and the stack
arguments at `0x8000`. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x6800 | .r3 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 0x40 else
    if a = 0x8005 then 0x21 else
    if a = 0x8008 then 1 else
    if a = 0x800d then 0x22 else
    if a = 0x8010 then 1 else
    if a = 0x8015 then 0x30 else
    if a = 0x8018 then 0x40 else
    if a = 0x801d then 0x31 else
    if a = 0x8020 then 1 else
    if a = 0x8025 then 0x32 else
    if a = 0x8028 then 1 else
    if a = 0x802d then 0x33 else
    if a = 0x8030 then 1 else
    if a = 0x8035 then 0x34 else
    if a = 0x8038 then 1 else
    if a = 0x803d then 0x35 else
    if a = 0x8040 then 1 else
    if a = 0x8045 then 0x40 else
    if a = 0x8048 then 0x20 else
    if a = 0x8049 then 4 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x2200, 1⟩, ⟨0x3000, 64⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩,
    ⟨0x3400, 1⟩, ⟨0x3500, 1⟩, ⟨0x8000, 76⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x6800, 8⟩, ⟨0x4000, 8448⟩]

theorem sat : ∃ s, spec.pre s := by
  sig_implies_sat [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi,
    argRegs, reduceClassify, Loc.val, State.addr]
    [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords] using satState

/-- `vg_rsa_pkcs1_decrypt`, calling `vg_rsa_private_checked` over `v`, meets the shared contract. -/
theorem code_verified (v : Proof.Rsa.Arm.CrtImpl) : Verified target (decryptCode v) spec :=
  ⟨fun _ h => let ⟨t, s', he, hq⟩ := code_ok v h; ⟨t, s', he, hq.1, hq.2⟩, code_ct v, sat⟩

end VG.Proof.RsaPkcs1Enc.Arm.Dec
