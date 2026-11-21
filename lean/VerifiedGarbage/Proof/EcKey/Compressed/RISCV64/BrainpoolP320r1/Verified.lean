module

public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.EcKey.BrainpoolP320r1
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.BrainpoolP320r1.Lit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.EcKey.BrainpoolP320r1
meta import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.BrainpoolP320r1.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP320r1.MulFn
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP320r1.MulFn
public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.MainAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP320r1.Exchange
public import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP320r1.RISCV64
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.MainAll
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP320r1.Exchange
meta import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP320r1.RISCV64
meta import VerifiedGarbage.Spec.EcKey.Compressed.Contract
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
meta import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub

/-! ### `EcKey.Compressed.RISCV64.BrainpoolP320r1.Main`, which only this module used -/

section

/-!
# brainpoolP320r1's point compression and decompression on RISC-V: correctness

`vg_ec_brainpoolp320r1_compress_public_key` and `vg_ec_brainpoolp320r1_decompress_public_key`
meet their contracts by register (`compRV`, `compress_ok`; `DPre`, `DPostC`,
`decompress_ok`): the proofs of `Proof/EcKey/Compressed/RISCV64/MainAll.lean`
for every curve, over the curve's kit of ECDH.
-/

@[expose] public section


namespace VG.Proof.EcKey.Compressed.RISCV64.BrainpoolP320r1

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg VG.Impl.EcKey.Compressed.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.BrainpoolP320r1
open VG.Proof.Ecdh.RISCV64.BrainpoolP320r1
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_nil writeBytes_append)

/-- `vg_ec_brainpoolp320r1_compress_public_key(out = a0, public = a1, scratch = a2)`, by
register. -/
def compRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 41⟩
    let pk : Region := ⟨s.gpr .a1, 81⟩
    let ws : Region := ⟨s.gpr .a2, 8192⟩
    s.rd = [pk] ∧ s.wr = [out, ws] ∧ pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
      (s.gpr .a0).toNat + 41 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 81 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat % 8 = 0
  post s s' :=
    match Spec.EcKey.compressPublicKey Spec.BrainpoolP320r1.curve (bytesAt s.mem (s.gpr .a1) 81) with
    | some bs => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 41 = bs
    | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 41 = List.replicate 41 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2

/-- The contract's postcondition is the kit's. -/
theorem compPost_eq : compRV.post = kit.compPost := by kernel_rfl

/-- `vg_ec_brainpoolp320r1_compress_public_key` by register. -/
theorem compress_ok {s : State} (hs : compRV.pre s) :
    WP isa compressBrainpoolP320r1 s fun s' => abiPreserved s s' ∧ compRV.post s s' := by
  rw [compPost_eq]; exact kit.compress_ok hs

/-! ## Decompression -/

/-- `vg_ec_brainpoolp320r1_decompress_public_key(out = a0, public = a1, scratch = a2)`'s
precondition, by register. -/
def DPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .a0, 81⟩
  let pk : Region := ⟨s.gpr .a1, 41⟩
  let ws : Region := ⟨s.gpr .a2, 8192⟩
  s.rd = [pk] ∧ s.wr = [out, ws] ∧ pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
    (s.gpr .a0).toNat + 81 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 41 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a2).toNat % 8 = 0

/-- `vg_ec_brainpoolp320r1_decompress_public_key`'s postcondition, by register. -/
def DPostC (s s' : State) : Prop :=
  let bs := bytesAt s.mem (s.gpr .a1) 41
  (s'.gpr .a0 = 1 ∧ ∃ Q, Spec.EcKey.matchesCompressedPublicKey Spec.BrainpoolP320r1.curve bs Q ∧
      bytesAt s'.mem (s.gpr .a0) 81 = Spec.EcKey.encodePoint Q) ∨
    (s'.gpr .a0 = 0 ∧ (¬ ∃ Q, Spec.EcKey.matchesCompressedPublicKey Spec.BrainpoolP320r1.curve bs Q) ∧
      bytesAt s'.mem (s.gpr .a0) 81 = List.replicate 81 0)

/-- `vg_ec_brainpoolp320r1_decompress_public_key` by register. -/
theorem decompress_ok (hL : VG.Proof.Weierstrass.Law W) {s : State} (hs : DPre s) :
    WP isa decompressBrainpoolP320r1 s fun s' => abiPreserved s s' ∧ DPostC s s' :=
  kit.decompress_ok (by decide) hL hs

end VG.Proof.EcKey.Compressed.RISCV64.BrainpoolP320r1

end

end

/-!
# SEC 1 point conversion over brainpoolP320r1 on RISC-V: `Verified`

`compress_verified` and `decompress_verified`: from `compress_ok` and
`decompress_ok`, with the times depending only on the pointers `out`,
`public` and `scratch` (by taint tracking: every address is a pointer plus a
constant, and the only branches are the field functions' and the power's
counter), and states satisfying the preconditions.
-/

@[expose] public section


namespace VG.Proof.EcKey.Compressed.RISCV64.BrainpoolP320r1

open VG VG.RISCV64 VG.Impl.EcKey.Compressed.RISCV64

theorem compress_rv (s : State) (hs : compRV.pre s) :
    ∃ t s', Exec isa compressBrainpoolP320r1 s t s' ∧ abiPreserved s s' ∧ compRV.post s s' := by
  obtain ⟨t, s', he, h⟩ := compress_ok hs
  exact ⟨t, s', he, h⟩

theorem compress_ct : ConstantTime isa compRV.pre compRV.pub compressBrainpoolP320r1 :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩)
    (by taint_decide_sum [VG.Proof.Ecdsa.RISCV64.BrainpoolP320r1.pMulSum,
      VG.Proof.Ecdsa.RISCV64.BrainpoolP320r1.pAddSum, VG.Proof.Ecdsa.RISCV64.BrainpoolP320r1.pSubSum])

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
    Verified RISCV64.target compressBrainpoolP320r1 (Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyContract RISCV64.abi) :=
  Verified.of_correct compress_rv compress_ct
    { pre := by
        sig_implies_pre [Spec.EcKey.BrainpoolP320r1.inst, Spec.EcKey.Instance.compressPublicKeyContract,
          Spec.EcKey.Instance.compressPublicKeySig, Spec.BrainpoolP320r1.curve, Spec.EcKey.scratchWords, compRV,
          RISCV64.abi, RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.BrainpoolP320r1.inst, Spec.EcKey.Instance.compressPublicKeyContract,
          Spec.EcKey.Instance.compressPublicKeySig, Spec.BrainpoolP320r1.curve, Spec.EcKey.scratchWords, compRV,
          RISCV64.abi, RISCV64.argRegs]
        have h' := h
        dsimp only [compRV] at h'
        generalize hq : Spec.EcKey.compressPublicKey _ _ = q
        have hq' : Spec.EcKey.compressPublicKey Spec.BrainpoolP320r1.curve (Spec.Ecdsa.bytesAt s.mem (s.gpr .a1) 81) = q := hq
        rw [hq'] at h'
        rcases q with _ | z
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.BrainpoolP320r1.inst, Spec.EcKey.Instance.compressPublicKeyContract,
          Spec.EcKey.Instance.compressPublicKeySig, Spec.BrainpoolP320r1.curve, Spec.EcKey.scratchWords, compRV,
          RISCV64.abi, RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.BrainpoolP320r1.inst, Spec.EcKey.Instance.compressPublicKeyContract,
          Spec.EcKey.Instance.compressPublicKeySig, Spec.BrainpoolP320r1.curve, Spec.EcKey.scratchWords, compRV,
          RISCV64.abi, RISCV64.argRegs, convSat] [convSat] using (convSat 41 81) }

/-- `vg_ec_brainpoolp320r1_decompress_public_key(out = a0, public = a1, scratch = a2)`, by
register. -/
def decRV : Contract isa where
  pre := DPre
  post := DPostC
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2

theorem decompress_rv (hL : VG.Proof.Weierstrass.Law Spec.BrainpoolP320r1.curve) (s : State) (hs : decRV.pre s) :
    ∃ t s', Exec isa decompressBrainpoolP320r1 s t s' ∧ abiPreserved s s' ∧ decRV.post s s' := by
  obtain ⟨t, s', he, h⟩ := decompress_ok hL hs
  exact ⟨t, s', he, h⟩

theorem decompress_ct : ConstantTime isa decRV.pre decRV.pub decompressBrainpoolP320r1 :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩)
    (by taint_decide_sum [VG.Proof.Ecdsa.RISCV64.BrainpoolP320r1.pMulSum,
      VG.Proof.Ecdsa.RISCV64.BrainpoolP320r1.pAddSum, VG.Proof.Ecdsa.RISCV64.BrainpoolP320r1.pSubSum])

theorem decompress_verified (hL : VG.Proof.Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    Verified RISCV64.target decompressBrainpoolP320r1 (Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyContract RISCV64.abi) :=
  Verified.of_correct (decompress_rv hL) decompress_ct
    { pre := by
        sig_implies_pre [Spec.EcKey.BrainpoolP320r1.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
          Spec.EcKey.Instance.decompressPublicKeySig, Spec.BrainpoolP320r1.curve, Spec.EcKey.scratchWords, decRV, DPre,
          RISCV64.abi, RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.BrainpoolP320r1.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
          Spec.EcKey.Instance.decompressPublicKeySig, Spec.BrainpoolP320r1.curve, Spec.EcKey.scratchWords, decRV, DPre,
          RISCV64.abi, RISCV64.argRegs]
        rcases (h : DPostC s s') with ⟨h1, Q, hm, hb⟩ | ⟨h1, hn, hb⟩
        · exact Or.inl ⟨by rw [h1]; rfl, Q, hm, hb⟩
        · exact Or.inr ⟨by rw [h1]; rfl, hn, hb⟩
      pub := by
        sig_implies_pub [Spec.EcKey.BrainpoolP320r1.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
          Spec.EcKey.Instance.decompressPublicKeySig, Spec.BrainpoolP320r1.curve, Spec.EcKey.scratchWords, decRV, DPre,
          RISCV64.abi, RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.BrainpoolP320r1.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
          Spec.EcKey.Instance.decompressPublicKeySig, Spec.BrainpoolP320r1.curve, Spec.EcKey.scratchWords, decRV, DPre,
          RISCV64.abi, RISCV64.argRegs, convSat] [convSat] using (convSat 81 41) }

/-- `vg_ec_brainpoolp320r1_compress_public_key` as emitted, cleanup included
(`Impl.EcKey.Compressed.RISCV64.Fn.compressBrainpoolP320r1`), meets its contract in constant
time and returns without secret residue. -/
theorem compress_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.EcKey.Compressed.RISCV64.Fn.compressBrainpoolP320r1
      (Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyContract RISCV64.abi) 32 :=
  RISCV64.Scrub.verifiedScrubbedAll (api := Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyApi) (W := 0)
    { code := compressBrainpoolP320r1, verified := compress_verified }
    (EcKey.RISCV64.Scrub.compressOut _ _ []) (by dsimp only; lit_decide)

/-- `vg_ec_brainpoolp320r1_decompress_public_key` as emitted, cleanup included
(`Impl.EcKey.Compressed.RISCV64.Fn.decompressBrainpoolP320r1`), meets its contract in
constant time and returns without secret residue. -/
theorem decompress_scrubbed (hL : VG.Proof.Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    VerifiedScrubbed RISCV64.target Impl.EcKey.Compressed.RISCV64.Fn.decompressBrainpoolP320r1
      (Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyContract RISCV64.abi) 32 :=
  RISCV64.Scrub.verifiedScrubbedAll (api := Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyApi) (W := 0)
    { code := decompressBrainpoolP320r1, verified := decompress_verified hL }
    (EcKey.RISCV64.Scrub.decompressOut _ _ []) (by dsimp only; lit_decide)

end VG.Proof.EcKey.Compressed.RISCV64.BrainpoolP320r1
