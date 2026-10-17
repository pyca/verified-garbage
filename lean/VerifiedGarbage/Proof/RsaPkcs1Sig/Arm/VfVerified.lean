module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.VfBody
public import VerifiedGarbage.Proof.Framework.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSASSA-PKCS1-v1_5 verification with a precomputed public key on ARMv7: verified

The frames around the body (`wrap_ok`, `wrap_ct`), the result as the shared
contract states it, and a state that meets it (`sat`):
`vg_rsa_pkcs1_verify_precomputed`, calling any implementation `c` of
`vg_rsa_public_precomputed_checked`, is verified (`code_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm.Vf

open VG VG.Arm VG.Impl.RsaPkcs1Sig.Arm.Precomputed VG.Proof.RsaPkcs1Sig.Arm

theorem entered_state {s : State} (h : spec.pre s) :
    S (ep s) (entered frameBytes s) (entered frameBytes s) :=
  ⟨in_of_pre h, ⟨(in_of_pre h).ok, (in_of_pre h).ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem spec_sp {s : State} (h : spec.pre s) : stackBytes ≤ s.sp.toNat := by
  sig_pre [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi,
    argRegs, reduceClassify, Loc.val] at h
  exact h.1

theorem code_ok (c : PdImpl) {s : State} (h : spec.pre s) :
    WP isa (code c.name c.code) s fun t => abiPreserved s t ∧ spec.post s t := by
  have hs := spec_sp h
  have hin := in_of_pre h
  have st := entered_state h
  have hsp : 56 + frameBytes ≤ s.sp.toNat := by simp only [stackBytes] at hs; omega
  refine WP.mono (wrap_ok (by decide) (by omega) (W := (ep s).lay.W)
    (Q := fun r _ => Res (ep s) (entered frameBytes s) r) (fun r hr => ?_)
    (WP.mono ((body_vp c).wp _ _ st) fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 36) (argv := (ep s).argv)
      (ro := [(ep s).N, (ep s).E, (ep s).DIG, (ep s).SIG, (ep s).PRE]) (rw := [(ep s).SCR]) hsp]
    exact hin.ok.push_apart r hr
  · sig_post [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi,
      argRegs, reduceClassify, Loc.val]
    rw [BitVec.setWidth_append_eq_right]
    intro hp
    have hn : (Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat).length =
        (s.gpr .r1).toNat := bytesAt_length _ _ _
    have w := res _ hn hp
    have ro := fun {R : Region} (hR : R ∈ [(ep s).N, (ep s).E, (ep s).DIG, (ep s).SIG, (ep s).PRE]) =>
      entered_ro (F := frameBytes) (A := 36) (argv := (ep s).argv) (rw := [(ep s).SCR]) hin.ok hsp hR
    have hD : digB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1))
        (stackArg s 2).toNat := ro (R := (ep s).DIG) (by simp)
    have hG : sigB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3))
        (stackArg s 4).toNat := ro (R := (ep s).SIG) (by simp)
    rw [hD, hG] at w
    exact w

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

/-- Two entry states with the same public data have the same public parameters. -/
theorem ep_eq {s₁ s₂ : State} (hp : spec.pub s₁ s₂) : ep s₁ = ep s₂ := by
  sig_pub [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi,
    argRegs, reduceClassify, Loc.val] at hp
  obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hp
  obtain ⟨hab, hw⟩ := List.append_inj hl (by simp [bytesAt_length, h1, h3, a2, a4])
  have hx := map_toNat_inj hab
  obtain ⟨hx, -⟩ := List.append_inj hx (by simp [bytesAt_length, h1, h3, a2])
  obtain ⟨hx, -⟩ := List.append_inj hx (by simp [bytesAt_length, h1, h3])
  obtain ⟨-, he⟩ := List.append_inj hx (by simp [bytesAt_length, h1])
  have hw' := map_toNat_inj hw
  simp only [ep]
  rw [hsp, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8]
  rw [h2, h3] at he
  rw [a7, a8] at hw'
  rw [show State.addr (s₂.gpr .r2) = BitVec.setWidth 64 (s₂.gpr .r2) from rfl, he,
    show State.addr (stackArg s₂ 7) = BitVec.setWidth 64 (stackArg s₂ 7) from rfl, hw']

theorem code_ct (c : PdImpl) : ConstantTime isa spec.pre spec.pub (code c.name c.code) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  have hep := ep_eq hp
  have hsp : s₁.sp = s₂.sp := by
    sig_pub [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi,
      argRegs, reduceClassify, Loc.val] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp)
    (fun a b h => by rw [h.1]; have := spec_sp h₁; simp only [stackBytes] at this; omega) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp (P := ep s₁) c).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_state h₁, by rw [hep]; exact entered_state h₂⟩

/-- A state that meets the shared contract: a modulus of 64 bytes, `e` of one
byte, an empty hash value and signature, and the stack arguments at
`0x8000`. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x2000 | .r1 => 64 | .r2 => 0x2100 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8005 then 0x30 else
    if a = 0x800d then 0x31 else
    if a = 0x8015 then 0x40 else
    if a = 0x8018 then 0x20 else
    if a = 0x8019 then 4 else
    if a = 0x801d then 0x70 else
    if a = 0x8020 then 0x10 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x7000, 128⟩, ⟨0x8000, 36⟩]
  wr := [⟨0x4000, 8448⟩]

theorem sat : ∃ s, spec.pre s := by
  sig_implies_sat [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi,
    argRegs, reduceClassify, Loc.val, State.addr]
    [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using satState

/-- `vg_rsa_pkcs1_verify_precomputed`, calling `c`, meets the shared contract. -/
theorem code_verified (c : PdImpl) : Verified target (code c.name c.code) spec :=
  ⟨fun _ h => let ⟨t, s', he, hq⟩ := code_ok c h; ⟨t, s', he, hq.1, hq.2⟩, code_ct c, sat⟩

end VG.Proof.RsaPkcs1Sig.Arm.Vf
