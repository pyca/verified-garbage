module

public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P384.Main
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.EcKey.P384
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P384.Lit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P384.Main
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.EcKey.P384
meta import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P384.Lit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# SEC 1 point conversion over P-384 on RISC-V: `Verified`

`compress_verified` and `decompress_verified`: from `compress_ok` and
`decompress_ok`, with the times depending only on the pointers `out`,
`public` and `scratch` (by taint tracking: every address is a pointer plus a
constant, and the only branches are the field functions' and the power's
counter), and states satisfying the preconditions.
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.EcKey.Compressed.RISCV64.P384

open VG VG.RISCV64 VG.Impl.EcKey.Compressed.RISCV64

theorem compress_rv (s : State) (hs : compRV.pre s) :
    ∃ t s', Exec isa compressP384 s t s' ∧ abiPreserved s s' ∧ compRV.post s s' := by
  obtain ⟨t, s', he, h⟩ := compress_ok hs
  exact ⟨t, s', he, h⟩

theorem compress_ct : ConstantTime isa compRV.pre compRV.pub compressP384 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩) (by taint_decide)

/-- A state satisfying the preconditions, for an output of `n` bytes and an
input of `m`. -/
def convSat (n m : Nat) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, m⟩]
  wr := [⟨0x1000, n⟩, ⟨0x8000, 8192⟩]

theorem compress_verified :
    Verified RISCV64.target compressP384 (Spec.EcKey.P384.inst.compressPublicKeyContract RISCV64.abi) :=
  Verified.of_correct compress_rv compress_ct
    { pre := by
        sig_implies_pre [Spec.EcKey.P384.inst, Spec.EcKey.Instance.compressPublicKeyContract,
          Spec.EcKey.Instance.compressPublicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, compRV,
          RISCV64.abi, RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P384.inst, Spec.EcKey.Instance.compressPublicKeyContract,
          Spec.EcKey.Instance.compressPublicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, compRV,
          RISCV64.abi, RISCV64.argRegs]
        have h' : match Spec.EcKey.compressPublicKey Spec.P384.curve (Spec.Ecdsa.bytesAt s.mem (s.gpr .a1) 97) with
            | some bs => s'.gpr .a0 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 49 = bs
            | none => s'.gpr .a0 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 49 = List.replicate 49 0 := h
        generalize hq : Spec.EcKey.compressPublicKey _ _ = q
        have hq' : Spec.EcKey.compressPublicKey Spec.P384.curve (Spec.Ecdsa.bytesAt s.mem (s.gpr .a1) 97) = q := hq
        rw [hq'] at h'
        rcases q with _ | z
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.P384.inst, Spec.EcKey.Instance.compressPublicKeyContract,
          Spec.EcKey.Instance.compressPublicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, compRV,
          RISCV64.abi, RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.P384.inst, Spec.EcKey.Instance.compressPublicKeyContract,
          Spec.EcKey.Instance.compressPublicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, compRV,
          RISCV64.abi, RISCV64.argRegs, convSat] [convSat] using (convSat 49 97) }

/-- `vg_ec_p384_decompress_public_key(out = a0, public = a1, scratch = a2)`, by
register. -/
def decRV : Contract isa where
  pre := DPre
  post := DPostC
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2

theorem decompress_rv (hL : VG.Proof.Weierstrass.Law Spec.P384.curve) (s : State) (hs : decRV.pre s) :
    ∃ t s', Exec isa decompressP384 s t s' ∧ abiPreserved s s' ∧ decRV.post s s' := by
  obtain ⟨t, s', he, h⟩ := decompress_ok hL hs
  exact ⟨t, s', he, h⟩

theorem decompress_ct : ConstantTime isa decRV.pre decRV.pub decompressP384 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩) (by taint_decide)

theorem decompress_verified (hL : VG.Proof.Weierstrass.Law Spec.P384.curve) :
    Verified RISCV64.target decompressP384 (Spec.EcKey.P384.inst.decompressPublicKeyContract RISCV64.abi) :=
  Verified.of_correct (decompress_rv hL) decompress_ct
    { pre := by
        sig_implies_pre [Spec.EcKey.P384.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
          Spec.EcKey.Instance.decompressPublicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, decRV, DPre,
          RISCV64.abi, RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P384.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
          Spec.EcKey.Instance.decompressPublicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, decRV, DPre,
          RISCV64.abi, RISCV64.argRegs]
        rcases (h : DPostC s s') with ⟨h1, Q, hm, hb⟩ | ⟨h1, hn, hb⟩
        · exact Or.inl ⟨by rw [h1]; rfl, Q, hm, hb⟩
        · exact Or.inr ⟨by rw [h1]; rfl, hn, hb⟩
      pub := by
        sig_implies_pub [Spec.EcKey.P384.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
          Spec.EcKey.Instance.decompressPublicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, decRV, DPre,
          RISCV64.abi, RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.P384.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
          Spec.EcKey.Instance.decompressPublicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, decRV, DPre,
          RISCV64.abi, RISCV64.argRegs, convSat] [convSat] using (convSat 97 49) }

end VG.Proof.EcKey.Compressed.RISCV64.P384
