module

public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.EcKey.P192
import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.EcdhLit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.EcKey.P192
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.EcdhLit
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdh.RISCV64.PublicKeyAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.Exchange
public import VerifiedGarbage.Spec.EcKey
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
public import VerifiedGarbage.Impl.Ecdh.P192.RISCV64
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.PublicKeyAll
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.Exchange
meta import VerifiedGarbage.Spec.EcKey
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
meta import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
meta import VerifiedGarbage.Impl.Ecdh.P192.RISCV64

/-! ### `Ecdh.RISCV64.P192.PublicKey`, which only this module used -/

section

/-!
# P-192's public keys on RISC-V: correctness

The curve's `PkKit` for `Proof/Ecdh/RISCV64/PublicKeyAll.lean` (`[d]G` by the ladder, as in ECDH),
and what that proof gives of `publicKeyP192`: it meets its contract by
register (`pkRV`), given the group law (`pk_rv`); and the point written to
`out` (`pointOut_ok`), which the compressed keys use too.
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.P192

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.P192
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_nil writeBytes_append)

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point W) :=
  Spec.EcKey.publicKey Spec.P192.curve (ofBytes (bytesAt m d 24))

def pkRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 49⟩
    let d : Region := ⟨s.gpr .a1, 24⟩
    let scratch : Region := ⟨s.gpr .a2, 8192⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      (s.gpr .a0).toNat + 49 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 24 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat % 8 = 0
  post s s' :=
    match pk s.mem (s.gpr .a1) with
    | some (.affine x y) => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 49 = Spec.EcKey.encodePoint (.affine x y)
    | _ => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 49 = List.replicate 49 0
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
    (hfit : out.toNat + 49 ≤ 2 ^ 64)
    (hout : ∀ i < 49, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hdis : (⟨out, 49⟩ : Region).Disjoint ⟨base, 8192⟩)
    {B : Bool} (ha7 : s.gpr .a7 = maskOf B) (hfl : word s.mem base FL = maskOf B)
    {xo yo : Nat} (hxo : xo < 44) (hyo : yo < 44) (hxo' : xo < 41) (hyo' : yo < 41) :
    WP isa (.block (pointOut192 xo yo)) s fun s' =>
      s'.gpr .a0 = (if B then 1 else 0) ∧
      bytesAt s'.mem out 49 = (if B then 4 else 0) ::
        (toBytes 24 (if B then sv base s xo else 0) ++ toBytes 24 (if B then sv base s yo else 0)) ∧
      s'.gpr .s0 = word s.mem base 0 ∧ s'.gpr .s1 = word s.mem base 8 ∧ s'.gpr .s2 = word s.mem base 16 ∧
      s'.gpr .ra = word s.mem base 24 ∧ s'.gpr .s3 = word s.mem base 32 ∧
      (∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp :=
  kit.pointOut_ok hw h2 hfit hout hdis ha7 hfl (by omega_using [hxo, hxo']) (by omega_using [hyo, hyo'])

/-- The contract's postcondition is the kit's. -/
theorem post_eq : pkRV.post = kit.pkPost := by kernel_rfl

theorem pk_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : pkRV.pre s) :
    ∃ t s', Exec isa publicKeyP192 s t s' ∧ abiPreserved s s' ∧ pkRV.post s s' := by
  obtain ⟨hrd, hwr, hod, hdd, hfo, hfd, hfs, hal⟩ := hs
  obtain ⟨t, s', he, hp, hq⟩ := pkit.pk_ok hL
    ⟨by rw [hrd]; exact List.mem_singleton_self _, hwr, hod, hdd, hfo, hfd, hfs, hal, trivial⟩
  exact ⟨t, s', he, hp, (congrFun (congrFun post_eq s) s').mpr hq⟩

end VG.Proof.Ecdh.RISCV64.P192

end

end

/-!
# P-192's public keys on RISC-V: `Verified`

`pk_rv` with the function's constant time, by taint tracking (only the
pointers, in `a0`–`a2`, public).
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.P192

open VG VG.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Proof.Ecdsa.RISCV64.P192

theorem pk_ct : ConstantTime isa pkRV.pre pkRV.pub publicKeyP192 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩) (by taint_decide)

/-- A state satisfying the precondition. -/
def pkSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 24⟩]
  wr := [⟨0x1000, 49⟩, ⟨0x8000, 8192⟩]

theorem pk_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target publicKeyP192 (Spec.EcKey.P192.inst.publicKeyContract RISCV64.abi) :=
  Verified.of_correct (pk_rv hL) pk_ct
    { pre := by
        sig_implies_pre [Spec.EcKey.P192.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P192.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P192.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P192.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs]
        have h' : match pk s.mem (s.gpr .a1) with
            | some (.affine x y) => s'.gpr .a0 = 1 ∧
                Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 49 = Spec.EcKey.encodePoint (.affine x y)
            | _ => s'.gpr .a0 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 49 = List.replicate 49 0 := h
        generalize hq : Spec.EcKey.publicKey _ _ = q
        have hq' : pk s.mem (s.gpr .a1) = q := hq
        rw [hq'] at h'
        rcases q with _ | _ | ⟨x, y⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.P192.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P192.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.P192.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P192.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs] [pkSat] using pkSat }

/-- `vg_ec_p192_public_key` as emitted, cleanup included
(`Impl.Ecdh.RISCV64.Fn.publicKeyP192`), meets its contract in constant time and
returns without secret residue. -/
theorem publicKey_scrubbed (hL : VG.Proof.Weierstrass.Law W) :
    VerifiedScrubbed RISCV64.target Impl.Ecdh.RISCV64.Fn.publicKeyP192
      (Spec.EcKey.P192.inst.publicKeyContract RISCV64.abi) 32 :=
  RISCV64.Scrub.verifiedScrubbed (api := Spec.EcKey.P192.publicKeyApi) (W := 0)
    { code := publicKeyP192, verified := pk_verified hL }
    (EcKey.RISCV64.Scrub.publicKeyOut _ _ []) (by dsimp only; lit_decide)

end VG.Proof.Ecdh.RISCV64.P192
