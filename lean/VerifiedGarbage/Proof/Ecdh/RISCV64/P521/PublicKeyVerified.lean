module

public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public import VerifiedGarbage.Spec.EcKey.P521
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.EcdhLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Spec.EcKey.P521
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.EcdhLit
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.CombVerified
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.CombVerified
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Field.Verified
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Field.Verified
public import VerifiedGarbage.Proof.Ecdh.RISCV64.PublicKeyAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.Exchange
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.Tail
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Spec.EcKey
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
public import VerifiedGarbage.Impl.Ecdh.P521.RISCV64
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.PublicKeyAll
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.Exchange
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.Tail
meta import VerifiedGarbage.Proof.Framework.RISCV64.Consts
meta import VerifiedGarbage.Spec.EcKey
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
meta import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
meta import VerifiedGarbage.Impl.Ecdh.P521.RISCV64

/-! ### `Ecdh.RISCV64.P521.PublicKey`, which only this module used -/

section

/-!
# P-521's public keys on RISC-V: correctness

The curve's `PkKit` for `Proof/Ecdh/RISCV64/PublicKeyAll.lean` (`[d]G` by the comb, whose table the state holds (`pkRVC`)),
and what that proof gives of `publicKeyP521`: it meets its contract by
register (`pkRV`), given the group law (`pk_rv`); and the point written to
`out` (`pointOut_ok`), which the compressed keys use too.
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.P521

-- `p`, below `2^521`, is evaluated.
set_option exponentiation.threshold 1024

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.P521
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_nil writeBytes_append)

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point W) :=
  Spec.EcKey.publicKey Spec.P521.curve (ofBytes (bytesAt m d 66))

def pkRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 133⟩
    let d : Region := ⟨s.gpr .a1, 66⟩
    let scratch : Region := ⟨s.gpr .a2, 8192⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      (s.gpr .a0).toNat + 133 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 66 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat % 8 = 0
  post s s' :=
    match pk s.mem (s.gpr .a1) with
    | some (.affine x y) => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 133 = Spec.EcKey.encodePoint (.affine x y)
    | _ => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 133 = List.replicate 133 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2

/-- `pkRV` with the comb's table (`abi.withConsts`): `pkRV` for the state
without it, and what the table adds. -/
def pkRVC : Contract isa where
  pre s := pkRV.pre (stripConsts Impl.Ecdsa.RISCV64.CombU.p521CombConsts s) ∧
    ConstsOk Impl.Ecdsa.RISCV64.CombU.p521CombConsts 0 s
  post := pkRV.post
  pub s₁ s₂ := pkRV.pub s₁ s₂ ∧ s₁.syms Impl.Ecdsa.RISCV64.CombU.p521Sym = s₂.syms Impl.Ecdsa.RISCV64.CombU.p521Sym

/-- The curve's kit for its public key. -/
def pkit : PkKit where
  E := kit
  gmulN := VG.Impl.Ecdsa.RISCV64.CombU.mulGP521Name
  gmulC := VG.Impl.Ecdsa.RISCV64.CombU.mulGP521
  GT0 := fun s => ConstsOk Impl.Ecdsa.RISCV64.CombU.p521CombConsts 0 s
  GT := VG.Proof.Ecdsa.RISCV64.P521.Comb.TabAt
  gt_start := fun hk hw => VG.Proof.Ecdsa.RISCV64.P521.Comb.tabAt_of_consts hk hw
  gt_frame := fun hk h sy rd F => h.of_frame sy rd F (VG.Proof.Ecdsa.RISCV64.P521.Comb.tab_wr_of_consts hk)
  tailG_ok := fun hL _ _ hw h3 a1 a2 a3 a4 a5 a6 a7 a8 hx hy _ hT =>
    VG.Proof.Ecdsa.RISCV64.P521.Comb.tailG_ok hL hw h3 ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ hx hy hT

/-- `pointOut`: `04 ‖ x ‖ y` from the slots `xo` and `yo` (or zeros, by the
mask `a7`, which the flag holds) to `out`, the flag's low bit to `a0`, and
the saved registers restored. -/
theorem pointOut_ok {s : State} {base out : Addr} (hw : WsReg s base) (h2 : s.gpr .s2 = out)
    (hfit : out.toNat + 133 ≤ 2 ^ 64)
    (hout : ∀ i < 133, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hdis : (⟨out, 133⟩ : Region).Disjoint ⟨base, 8192⟩)
    {B : Bool} (ha7 : s.gpr .a7 = maskOf B) (hfl : word s.mem base FL = maskOf B)
    {xo yo : Nat} (hxo : xo < 44) (hyo : yo < 44) (hxo' : xo < 41) (hyo' : yo < 41) :
    WP isa (.block (pointOut p521 xo yo)) s fun s' =>
      s'.gpr .a0 = (if B then 1 else 0) ∧
      bytesAt s'.mem out 133 = (if B then 4 else 0) ::
        (toBytes 66 (if B then sv base s xo else 0) ++ toBytes 66 (if B then sv base s yo else 0)) ∧
      s'.gpr .s0 = word s.mem base 0 ∧ s'.gpr .s1 = word s.mem base 8 ∧ s'.gpr .s2 = word s.mem base 16 ∧
      s'.gpr .ra = word s.mem base 24 ∧ s'.gpr .s3 = word s.mem base 32 ∧
      (∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp :=
  kit.pointOut_ok hw h2 hfit hout hdis ha7 hfl (by omega_using [hxo, hxo']) (by omega_using [hyo, hyo'])

/-- The contract's postcondition is the kit's. -/
theorem post_eq : pkRV.post = kit.pkPost := by kernel_rfl

theorem pk_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : pkRVC.pre s) :
    ∃ t s', Exec isa publicKeyP521 s t s' ∧ abiPreserved s s' ∧ pkRVC.post s s' := by
  obtain ⟨⟨hrd, hwr, hod, hdd, hfo, hfd, hfs, hal⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr] at hrd hwr hod hdd hfo hfd hfs hal
  obtain ⟨t, s', he, hp, hq⟩ := pkit.pk_ok hL
    ⟨stripConsts_rd_mem (by rw [hrd]; exact List.mem_singleton_self _), hwr, hod, hdd, hfo, hfd, hfs, hal, hk⟩
  exact ⟨t, s', he, hp, (congrFun (congrFun post_eq s) s').mpr hq⟩

end VG.Proof.Ecdh.RISCV64.P521

end

end

/-!
# P-521's public keys on RISC-V: `Verified`

`pk_rv` with the function's constant time, by taint tracking (only the
pointers, in `a0`–`a2`, and the comb's table's address public), under
`abi.withConsts` of the comb's table (`pkRVC_implies`, from `pkRV_implies`).
-/

@[expose] public section

-- `p`, below `2^521`, is evaluated.
set_option exponentiation.threshold 1024

namespace VG.Proof.Ecdh.RISCV64.P521

open VG VG.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Proof.Ecdsa.RISCV64.P521

theorem pk_ct : ConstantTime isa pkRVC.pre pkRVC.pub publicKeyP521 :=
  VG.Taint.constantTime_of_exists (A := taintSym [Impl.Ecdsa.RISCV64.CombU.p521Sym]) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ ⟨⟨hsp, h0, h1, h2⟩, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    (by taint_decide_sum [VG.Proof.Ecdsa.RISCV64.P521.Comb.mulGSum, VG.Proof.Ecdsa.RISCV64.P521.Comb.pMulSymSum])

/-- A state satisfying the precondition. -/
def pkSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 66⟩]
  wr := [⟨0x1000, 133⟩, ⟨0x8000, 8192⟩]

theorem pkRV_implies : pkRV.Implies (Spec.EcKey.P521.inst.publicKeyContract RISCV64.abi) :=
    { pre := by
        sig_implies_pre [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs]
        have h' : match pk s.mem (s.gpr .a1) with
            | some (.affine x y) => s'.gpr .a0 = 1 ∧
                Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 133 = Spec.EcKey.encodePoint (.affine x y)
            | _ => s'.gpr .a0 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 133 = List.replicate 133 0 := h
        generalize hq : Spec.EcKey.publicKey _ _ = q
        have hq' : pk s.mem (s.gpr .a1) = q := hq
        rw [hq'] at h'
        rcases q with _ | _ | ⟨x, y⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs] [pkSat] using pkSat }

/-- A state satisfying the precondition with the table. -/
def pkSatC : State :=
  { pkSat with mem := VG.Proof.Ecdsa.RISCV64.P521.Comb.combSatMem, rd := pkSat.rd ++ [⟨0x100000, 764928⟩], syms := fun _ => 0x100000 }

theorem pk_sat : (Spec.EcKey.P521.inst.publicKeyContract
    (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.CombU.p521CombConsts)).pre pkSatC := by
  have hl := VG.Proof.Ecdsa.RISCV64.P521.Comb.combWords_length
  have held := VG.Proof.Ecdsa.RISCV64.P521.Comb.combSatMem_held
  rw [show Impl.Ecdsa.RISCV64.CombU.p521CombConsts = [(Impl.Ecdsa.RISCV64.CombU.p521Sym,
    Impl.Ecdsa.RISCV64.CombU.p521CombWords)] from rfl]
  obtain ⟨W', eW⟩ : ∃ W, Impl.Ecdsa.RISCV64.CombU.p521CombWords = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : pkSatC = s
  sig_pre [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract, Spec.EcKey.Instance.publicKeySig,
    Spec.P521.curve, Spec.EcKey.scratchWords, RISCV64.abi, RISCV64.argRegs, Abi.withConsts, Abi.constRegions,
    Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨by decide, rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, rfl, rfl,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide⟩
  change r ∈ [⟨0x1000, 133⟩, ⟨0x8000, 8192⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)

theorem pkRVC_implies :
    pkRVC.Implies (Spec.EcKey.P521.inst.publicKeyContract
      (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.CombU.p521CombConsts)) :=
  { pre := fun _ hs => ⟨pkRV_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr (pkRV_implies.post (stripConsts _ s) s'
      (pre_consts.mp hs).1 hp)
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨pkRV_implies.pub (stripConsts _ s₁) (stripConsts _ s₂)
        (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
    sat := ⟨pkSatC, pk_sat⟩ }

theorem pk_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target publicKeyP521 (Spec.EcKey.P521.inst.publicKeyContract
      (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.CombU.p521CombConsts)) :=
  Verified.of_correct (pk_rv hL) pk_ct pkRVC_implies

/-- `vg_ec_p521_public_key` as emitted, cleanup included
(`Impl.Ecdh.RISCV64.Fn.publicKeyP521`), meets its contract in constant time and
returns without secret residue. -/
theorem publicKey_scrubbed (hL : VG.Proof.Weierstrass.Law W) :
    VerifiedScrubbed RISCV64.target Impl.Ecdh.RISCV64.Fn.publicKeyP521
      (Spec.EcKey.P521.inst.publicKeyContract (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.CombU.p521CombConsts)) 32 :=
  RISCV64.Scrub.verifiedScrubbed (api := Spec.EcKey.P521.publicKeyApi) (W := 0)
    { code := publicKeyP521, verified := pk_verified hL }
    (EcKey.RISCV64.Scrub.publicKeyOut _ _ Impl.Ecdsa.RISCV64.CombU.p521CombConsts) (by dsimp only; lit_decide)

end VG.Proof.Ecdh.RISCV64.P521
