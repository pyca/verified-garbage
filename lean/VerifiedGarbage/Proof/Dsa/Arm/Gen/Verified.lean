module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Body
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Dsa.Generation.ByteResult
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7 meets its contract

From the shared contract's precondition, the body (`body_vp`) between the
frame's allocation and release returns the status of
`Spec.Dsa.generateParametersBytes` and writes its parameters (or zeros)
(`code_ok`); two calls with the same public data have the same public
parameters, so the same trace (`code_ct`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.Rsa.Arm.Recover (VP Two)

section
variable {g1 g2 g3 : Geo}

theorem pre_preserved : ∀ r ∈ preserved, r ∈ VG.Impl.Dsa.Arm.Generation.saved.map Prod.fst := by decide

/-- The result as the contract states it. -/
theorem sRes_bytes {σ : State} (h : CIn σ) :
    Spec.Dsa.generateParametersBytes (σ.gpr .r2).toNat (σ.gpr .r3).toNat
      (Spec.Rsa.bytesAt σ.mem (BitVec.setWidth 64 (stackArg σ 0)) (stackArg σ 1).toNat)
      (Spec.Rsa.bytesAt σ.mem (BitVec.setWidth 64 (stackArg σ 2)) (stackArg σ 3).toNat)
      (Spec.Rsa.bytesAt σ.mem (BitVec.setWidth 64 (stackArg σ 4)) (stackArg σ 5).toNat) =
    (sRes (mkG σ)).map (Spec.Dsa.encodeParams (mkG σ).pLen (mkG σ).qLen) :=
  VG.Proof.Dsa.Generation.generateParametersBytes_attempt h.lens _ _ _
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact h.seedsMod)
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact h.hsMod)

theorem code_ok (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) {s : State}
    (hs : (Spec.Dsa.generateParametersContract abi 304).pre s) :
    WP isa (code g1 g2 g3) s fun t => abiPreserved s t ∧ (Spec.Dsa.generateParametersContract abi 304).post s t := by
  have hpre := cin_of_pre s hs
  have spLo := hpre.spLo
  refine WP.alloc ⟨by decide, by decide, by decide, by decide⟩ (by simp only [F]; omega)
    (WP.mono ((body_vp (G := mkG s) K1 K2 K3).wp s _ ⟨rfl, hpre, rfl⟩) fun u hu => ?_)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (pre_preserved r hr)
    exact hu.regs p hp
  · show u.sp + BitVec.ofNat 32 F = s.sp
    rw [hu.sp, BitVec.sub_add_cancel]; rfl
  sig_post [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, reduceClassify,
    Loc.val, stackArgAddr, BitVec.add_zero]
  rw [sRes_bytes hpre]
  refine ⟨?_, hu.out⟩
  rw [BitVec.setWidth_append_eq_right]
  show (u.gpr .r0).toNat = _
  rw [hu.r0]
  cases sRes (mkG s) <;> rfl

theorem map_toNat_inj {a b : List Byte} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

/-- Two calls with the same public data have the same public parameters. -/
theorem mkG_eq {s₁ s₂ : State} (h : (Spec.Dsa.generateParametersContract abi 304).pub s₁ s₂) : mkG s₁ = mkG s₂ := by
  sig_pub [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, reduceClassify,
    Loc.val, stackArgAddr, BitVec.add_zero] at h
  obtain ⟨hsp, hl, r0, r1, r2, r3, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
  simp only [List.append_assoc] at hl
  obtain ⟨hS, hl⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, a1])
  obtain ⟨hH, hW⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, a3])
  have e₁ : Spec.Rsa.bytesAt s₁.mem (State.addr (stackArg s₁ 0)) (stackArg s₁ 1).toNat =
      Spec.Rsa.bytesAt s₂.mem (State.addr (stackArg s₂ 0)) (stackArg s₂ 1).toNat := map_toNat_inj hS
  have e₂ : Spec.Rsa.bytesAt s₁.mem (State.addr (stackArg s₁ 2)) (stackArg s₁ 3).toNat =
      Spec.Rsa.bytesAt s₂.mem (State.addr (stackArg s₂ 2)) (stackArg s₂ 3).toNat := map_toNat_inj hH
  have e₃ : Spec.Rsa.bytesAt s₁.mem (State.addr (stackArg s₁ 4)) (stackArg s₁ 5).toNat =
      Spec.Rsa.bytesAt s₂.mem (State.addr (stackArg s₂ 4)) (stackArg s₂ 5).toNat := map_toNat_inj hW
  simp only [mkG]
  rw [e₁, e₂, e₃, hsp, r0, r1, r2, r3, a0, a1, a2, a3, a4, a5, a6, a7]

theorem alloc_push {s : State} (h : CIn s) : isa.push (.alloc F) s = some (allocated F s) := by
  have hsp : F ≤ s.sp.toNat := by have := h.spLo; simp only [F]; omega
  have hn : 0 < F ∧ F < 4096 ∧ F % 8 = 0 ∧ encodable (BitVec.ofNat 32 F) = true := by decide
  simp only [isa, push, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, hsp, and_self, ite_true]
  rfl

/-- The code leaks only what its contract makes public. -/
theorem code_ct (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    ConstantTime isa (Spec.Dsa.generateParametersContract abi 304).pre
      (Spec.Dsa.generateParametersContract abi 304).pub (code g1 g2 g3) := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp e₁ e₂
  have p₁ := cin_of_pre s₁ h₁
  have p₂ := cin_of_pre s₂ h₂
  have hG := mkG_eq hp
  cases e₁ with
  | frame ha₁ hb₁ _ =>
    cases e₂ with
    | frame ha₂ hb₂ _ =>
      rw [alloc_push p₁, Option.some.injEq] at ha₁
      rw [alloc_push p₂, Option.some.injEq] at ha₂
      subst ha₁ ha₂
      have hh := (body_vp (G := mkG s₁) K1 K2 K3).ct _ _ _ _ _ _
        ⟨s₁, s₂, ⟨rfl, p₁, rfl⟩, ⟨rfl, p₂, hG.symm⟩⟩ hb₁ hb₂ |>.1
      simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using hh

/-- A 1024/160 call with empty tapes: the output at `0x1000`, the tapes at
`0x5000`, `0x6000` and `0x7000`, `scratch` at `0x30000`. -/
def generateSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 276 | .r2 => 128 | .r3 => 20 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x20001 then 0x50 else if a = 0x20009 then 0x60 else if a = 0x20011 then 0x70
    else if a = 0x2001a then 0x03 else if a = 0x2001d then 0x24 else 0
  rd := [⟨0x5000, 0⟩, ⟨0x6000, 0⟩, ⟨0x7000, 0⟩, ⟨0x20000, 32⟩]
  wr := [⟨0x1000, 276⟩, ⟨0x30000, 73728⟩]

theorem generate_satisfiable : ∃ s, (Spec.Dsa.generateParametersContract abi 304).pre s := by
  sig_implies_sat [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr, stackArgAddr, BitVec.add_zero]
    [generateSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using generateSat

/-- `vg_dsa_generate_parameters` over the three geometries meets its contract. -/
theorem generate_verified (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    Verified target (code g1 g2 g3) (Spec.Dsa.generateParametersContract abi 304) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok K1 K2 K3 hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct K1 K2 K3,
    generate_satisfiable⟩

end

end VG.Proof.Dsa.Arm.Gen
