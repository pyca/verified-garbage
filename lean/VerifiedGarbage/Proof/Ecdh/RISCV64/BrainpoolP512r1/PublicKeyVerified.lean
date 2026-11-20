module

public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP512r1.EcdhLit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP512r1.EcdhLit
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.MulVerified
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.MulVerified
import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.MulFn
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.MulFn
public import VerifiedGarbage.Proof.Ecdh.RISCV64.PublicKeyAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP512r1.Exchange
public import VerifiedGarbage.Spec.EcKey
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.RISCV64
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.PublicKeyAll
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP512r1.Exchange
meta import VerifiedGarbage.Spec.EcKey
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
meta import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
meta import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.RISCV64

/-! ### `Ecdh.RISCV64.BrainpoolP512r1.PublicKey`, which only this module used -/

section

/-!
# brainpoolP512r1's public keys on RISC-V: correctness

The curve's `PkKit` for `Proof/Ecdh/RISCV64/PublicKeyAll.lean` (`[d]G` by the ladder, as in ECDH),
and what that proof gives of `publicKeyBrainpoolP512r1`: it meets its contract by
register (`pkRV`), given the group law (`pk_rv`); and the point written to
`out` (`pointOut_ok`), which the compressed keys use too.
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.BrainpoolP512r1

-- `p`, below `2^512`, is evaluated.
set_option exponentiation.threshold 1024

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_nil writeBytes_append)

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point W) :=
  Spec.EcKey.publicKey Spec.BrainpoolP512r1.curve (ofBytes (bytesAt m d 64))

def pkRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 129⟩
    let d : Region := ⟨s.gpr .a1, 64⟩
    let scratch : Region := ⟨s.gpr .a2, 8192⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      (s.gpr .a0).toNat + 129 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat % 8 = 0
  post s s' :=
    match pk s.mem (s.gpr .a1) with
    | some (.affine x y) => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 129 = Spec.EcKey.encodePoint (.affine x y)
    | _ => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 129 = List.replicate 129 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2

/-- The curve's kit for its public key. -/
def pkit : PkKit where
  E := kit
  gmulN := kit.mulN
  gmulC := kit.mulC
  GT0 := fun _ => True
  GT := fun _ _ => True
  gt_start := fun _ _ => trivial
  gt_frame := fun _ _ _ _ _ => trivial
  tailG_ok := fun hL _ _ hw h3 a1 a2 a3 a4 a5 a6 a7 a8 hx hy _ _ =>
    kit.tailG_of_tail hL hw h3 a1 a2 a3 a4 a5 a6 a7 a8 hx hy

/-- `pointOut`: `04 ‖ x ‖ y` from the slots `xo` and `yo` (or zeros, by the
mask `a7`, which the flag holds) to `out`, the flag's low bit to `a0`, and
the saved registers restored. -/
theorem pointOut_ok {s : State} {base out : Addr} (hw : WsReg s base) (h2 : s.gpr .s2 = out)
    (hfit : out.toNat + 129 ≤ 2 ^ 64)
    (hout : ∀ i < 129, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hdis : (⟨out, 129⟩ : Region).Disjoint ⟨base, 8192⟩)
    {B : Bool} (ha7 : s.gpr .a7 = maskOf B) (hfl : word s.mem base FL = maskOf B)
    {xo yo : Nat} (hxo : xo < 44) (hyo : yo < 44) (hxo' : xo < 41) (hyo' : yo < 41) :
    WP isa (.block (pointOut brainpoolp512r1 xo yo)) s fun s' =>
      s'.gpr .a0 = (if B then 1 else 0) ∧
      bytesAt s'.mem out 129 = (if B then 4 else 0) ::
        (toBytes 64 (if B then sv base s xo else 0) ++ toBytes 64 (if B then sv base s yo else 0)) ∧
      s'.gpr .s0 = word s.mem base 0 ∧ s'.gpr .s1 = word s.mem base 8 ∧ s'.gpr .s2 = word s.mem base 16 ∧
      s'.gpr .ra = word s.mem base 24 ∧ s'.gpr .s3 = word s.mem base 32 ∧
      (∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  rw [pointOut, show brainpoolp512r1.C.len = 8 * brainpoolp512r1.n from rfl, storeLen_mul, storeLen_mul]
  exact kit.pointOut_ok hw h2 hfit hout hdis ha7 hfl (by omega_using [hxo, hxo']) (by omega_using [hyo, hyo'])

/-- The contract's postcondition is the kit's. -/
theorem post_eq : pkRV.post = kit.pkPost := by kernel_rfl

theorem pk_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : pkRV.pre s) :
    ∃ t s', Exec isa publicKeyBrainpoolP512r1 s t s' ∧ abiPreserved s s' ∧ pkRV.post s s' := by
  obtain ⟨hrd, hwr, hod, hdd, hfo, hfd, hfs, hal⟩ := hs
  obtain ⟨t, s', he, hp, hq⟩ := pkit.pk_ok hL
    ⟨by rw [hrd]; exact List.mem_singleton_self _, hwr, hod, hdd, hfo, hfd, hfs, hal, trivial⟩
  exact ⟨t, s', he, hp, (congrFun (congrFun post_eq s) s').mpr hq⟩

end VG.Proof.Ecdh.RISCV64.BrainpoolP512r1

end

end

/-!
# brainpoolP512r1's public keys on RISC-V: `Verified`

`pk_rv` with the function's constant time, by taint tracking (only the
pointers, in `a0`–`a2`, public).
-/

@[expose] public section

-- `p`, below `2^512`, is evaluated.
set_option exponentiation.threshold 1024

namespace VG.Proof.Ecdh.RISCV64.BrainpoolP512r1

open VG VG.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1

theorem pk_ct : ConstantTime isa pkRV.pre pkRV.pub publicKeyBrainpoolP512r1 :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩)
    (by taint_decide_sum [VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1.mulSum,
      VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1.pMulSum])

/-- A state satisfying the precondition. -/
def pkSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 129⟩, ⟨0x8000, 8192⟩]

theorem pk_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target publicKeyBrainpoolP512r1 (Spec.EcKey.BrainpoolP512r1.inst.publicKeyContract RISCV64.abi) :=
  Verified.of_correct (pk_rv hL) pk_ct
    { pre := by
        sig_implies_pre [Spec.EcKey.BrainpoolP512r1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.BrainpoolP512r1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs]
        have h' : match pk s.mem (s.gpr .a1) with
            | some (.affine x y) => s'.gpr .a0 = 1 ∧
                Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 129 = Spec.EcKey.encodePoint (.affine x y)
            | _ => s'.gpr .a0 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 129 = List.replicate 129 0 := h
        generalize hq : Spec.EcKey.publicKey _ _ = q
        have hq' : pk s.mem (s.gpr .a1) = q := hq
        rw [hq'] at h'
        rcases q with _ | _ | ⟨x, y⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.BrainpoolP512r1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.BrainpoolP512r1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs] [pkSat] using pkSat }

/-- `vg_ec_brainpoolp512r1_public_key` as emitted, cleanup included
(`Impl.Ecdh.RISCV64.Fn.publicKeyBrainpoolP512r1`), meets its contract in constant time and
returns without secret residue. -/
theorem publicKey_scrubbed (hL : VG.Proof.Weierstrass.Law W) :
    VerifiedScrubbed RISCV64.target Impl.Ecdh.RISCV64.Fn.publicKeyBrainpoolP512r1
      (Spec.EcKey.BrainpoolP512r1.inst.publicKeyContract RISCV64.abi) 32 :=
  RISCV64.Scrub.verifiedScrubbed (api := Spec.EcKey.BrainpoolP512r1.publicKeyApi) (W := 0)
    { code := publicKeyBrainpoolP512r1, verified := pk_verified hL }
    (EcKey.RISCV64.Scrub.publicKeyOut _ _ []) (by dsimp only; lit_decide)

end VG.Proof.Ecdh.RISCV64.BrainpoolP512r1
