module

public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP256r1.EcdhLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP256r1.EcdhLit
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdh.RISCV64.PublicKeyAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP256r1.Exchange
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP256r1.Tail
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.CombVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Spec.EcKey
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.PublicKeyAll
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP256r1.Exchange
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP256r1.Tail
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP256r1.CombVerified
meta import VerifiedGarbage.Proof.Framework.RISCV64.Consts
meta import VerifiedGarbage.Spec.EcKey
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes

/-! ### `Ecdh.RISCV64.BrainpoolP256r1.PublicKey`, which only this module used -/

section

/-!
# brainpoolP256r1's public keys on RISC-V: correctness

The curve's `PkKit` for `Proof/Ecdh/RISCV64/PublicKeyAll.lean` (`[d]G` by the comb, whose table the state holds (`pkRVC`)),
and what that proof gives of `publicKeyBrainpoolP256r1`: it meets its contract by
register (`pkRV`), given the group law (`pk_rv`); and the point written to
`out` (`pointOut_ok`), which the compressed keys use too.
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.BrainpoolP256r1

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_nil writeBytes_append)

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point W) :=
  Spec.EcKey.publicKey Spec.BrainpoolP256r1.curve (ofBytes (bytesAt m d 32))

def pkRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 65⟩
    let d : Region := ⟨s.gpr .a1, 32⟩
    let scratch : Region := ⟨s.gpr .a2, 8192⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      (s.gpr .a0).toNat + 65 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat % 8 = 0
  post s s' :=
    match pk s.mem (s.gpr .a1) with
    | some (.affine x y) => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 65 = Spec.EcKey.encodePoint (.affine x y)
    | _ => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 65 = List.replicate 65 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2

/-- `pkRV` with the comb's table (`abi.withConsts`): `pkRV` for the state
without it, and what the table adds. -/
def pkRVC : Contract isa where
  pre s := pkRV.pre (stripConsts Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1CombConsts s) ∧
    ConstsOk Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1CombConsts 0 s
  post := pkRV.post
  pub s₁ s₂ := pkRV.pub s₁ s₂ ∧
    s₁.syms Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1Sym = s₂.syms Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1Sym

/-- The curve's kit for its public key. -/
def pkit : PkKit where
  E := kit
  gmulN := VG.Impl.Ecdsa.RISCV64.Comb.mulGBrainpoolP256r1Name
  gmulC := VG.Impl.Ecdsa.RISCV64.Comb.mulGBrainpoolP256r1
  GT0 := fun s => ConstsOk Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1CombConsts 0 s
  GT := Ecdsa.RISCV64.BrainpoolP256r1.Comb.TabAt
  gt_start := fun hk hw => Ecdsa.RISCV64.BrainpoolP256r1.Comb.tabAt_of_consts hk hw
  gt_frame := fun hk h sy rd F => h.of_frame sy rd F (Ecdsa.RISCV64.BrainpoolP256r1.Comb.tab_wr_of_consts hk)
  tailG_ok := fun hL _ _ hw h3 a1 a2 a3 a4 a5 a6 a7 a8 hx hy _ hT =>
    Ecdsa.RISCV64.BrainpoolP256r1.Comb.tailG_ok hL hw h3 ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ hx hy hT

/-- `pointOut`: `04 ‖ x ‖ y` from the slots `xo` and `yo` (or zeros, by the
mask `a7`, which the flag holds) to `out`, the flag's low bit to `a0`, and
the saved registers restored. -/
theorem pointOut_ok {s : State} {base out : Addr} (hw : WsReg s base) (h2 : s.gpr .s2 = out)
    (hfit : out.toNat + 65 ≤ 2 ^ 64)
    (hout : ∀ i < 65, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hdis : (⟨out, 65⟩ : Region).Disjoint ⟨base, 8192⟩)
    {B : Bool} (ha7 : s.gpr .a7 = maskOf B) (hfl : word s.mem base FL = maskOf B)
    {xo yo : Nat} (hxo : xo < 44) (hyo : yo < 44) :
    WP isa (.block (pointOut brainpoolp256r1 xo yo)) s fun s' =>
      s'.gpr .a0 = (if B then 1 else 0) ∧
      bytesAt s'.mem out 65 = (if B then 4 else 0) ::
        (toBytes 32 (if B then sv base s xo else 0) ++ toBytes 32 (if B then sv base s yo else 0)) ∧
      s'.gpr .s0 = word s.mem base 0 ∧ s'.gpr .s1 = word s.mem base 8 ∧ s'.gpr .s2 = word s.mem base 16 ∧
      s'.gpr .ra = word s.mem base 24 ∧ s'.gpr .s3 = word s.mem base 32 ∧
      (∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  rw [pointOut, show brainpoolp256r1.C.len = 8 * brainpoolp256r1.n from rfl, storeLen_mul, storeLen_mul]
  exact kit.pointOut_ok hw h2 hfit hout hdis ha7 hfl (by omega_using [hxo]) (by omega_using [hyo])

/-- The contract's postcondition is the kit's. -/
theorem post_eq : pkRV.post = kit.pkPost := by kernel_rfl

theorem pk_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : pkRVC.pre s) :
    ∃ t s', Exec isa publicKeyBrainpoolP256r1 s t s' ∧ abiPreserved s s' ∧ pkRVC.post s s' := by
  obtain ⟨⟨hrd, hwr, hod, hdd, hfo, hfd, hfs, hal⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr] at hrd hwr hod hdd hfo hfd hfs hal
  obtain ⟨t, s', he, hp, hq⟩ := pkit.pk_ok hL
    ⟨stripConsts_rd_mem (by rw [hrd]; exact List.mem_singleton_self _), hwr, hod, hdd, hfo, hfd, hfs, hal, hk⟩
  exact ⟨t, s', he, hp, (congrFun (congrFun post_eq s) s').mpr hq⟩

end VG.Proof.Ecdh.RISCV64.BrainpoolP256r1

end

end

/-!
# brainpoolP256r1's public keys on RISC-V: `Verified`

`pk_rv` with the function's constant time, by taint tracking (only the
pointers, in `a0`–`a2`, and the comb's table's address public), under
`abi.withConsts` of the comb's table (`pkRVC_implies`, from `pkRV_implies`).
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.BrainpoolP256r1

open VG VG.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1

theorem pk_ct : ConstantTime isa pkRVC.pre pkRVC.pub publicKeyBrainpoolP256r1 :=
  VG.Taint.constantTime (A := taintSym [Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1Sym]) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ ⟨⟨hsp, h0, h1, h2⟩, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

/-- A state satisfying the precondition. -/
def pkSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 65⟩, ⟨0x8000, 8192⟩]

theorem pkRV_implies : pkRV.Implies (Spec.EcKey.BrainpoolP256r1.inst.publicKeyContract RISCV64.abi) :=
    { pre := by
        sig_implies_pre [Spec.EcKey.BrainpoolP256r1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.BrainpoolP256r1.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.BrainpoolP256r1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.BrainpoolP256r1.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs]
        have h' : match pk s.mem (s.gpr .a1) with
            | some (.affine x y) => s'.gpr .a0 = 1 ∧
                Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 65 = Spec.EcKey.encodePoint (.affine x y)
            | _ => s'.gpr .a0 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 65 = List.replicate 65 0 := h
        generalize hq : Spec.EcKey.publicKey _ _ = q
        have hq' : pk s.mem (s.gpr .a1) = q := hq
        rw [hq'] at h'
        rcases q with _ | _ | ⟨x, y⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.BrainpoolP256r1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.BrainpoolP256r1.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.BrainpoolP256r1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.BrainpoolP256r1.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs] [pkSat] using pkSat }

/-- A state satisfying the precondition with the table. -/
def pkSatC : State :=
  { pkSat with
    mem := VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1.Comb.combSatMem
    rd := pkSat.rd ++ [⟨0x100000, 151552⟩]
    syms := fun _ => 0x100000 }

theorem pk_sat : (Spec.EcKey.BrainpoolP256r1.inst.publicKeyContract
    (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1CombConsts)).pre pkSatC := by
  have hl := VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1.Comb.combWords_length
  have held := VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1.Comb.combSatMem_held
  rw [show Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1CombConsts = [(Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1Sym,
    Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1CombWords)] from rfl]
  obtain ⟨W', eW⟩ : ∃ W, Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1CombWords = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : pkSatC = s
  sig_pre [Spec.EcKey.BrainpoolP256r1.inst, Spec.EcKey.Instance.publicKeyContract, Spec.EcKey.Instance.publicKeySig,
    Spec.BrainpoolP256r1.curve, Spec.EcKey.scratchWords, RISCV64.abi, RISCV64.argRegs, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨by decide, rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, rfl, rfl,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide⟩
  change r ∈ [⟨0x1000, 65⟩, ⟨0x8000, 8192⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)

theorem pkRVC_implies :
    pkRVC.Implies (Spec.EcKey.BrainpoolP256r1.inst.publicKeyContract
      (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1CombConsts)) :=
  { pre := fun _ hs => ⟨pkRV_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr (pkRV_implies.post (stripConsts _ s) s'
      (pre_consts.mp hs).1 hp)
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨pkRV_implies.pub (stripConsts _ s₁) (stripConsts _ s₂)
        (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
    sat := ⟨pkSatC, pk_sat⟩ }

theorem pk_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target publicKeyBrainpoolP256r1 (Spec.EcKey.BrainpoolP256r1.inst.publicKeyContract
      (RISCV64.abi.withConsts Impl.Ecdsa.RISCV64.Comb.brainpoolP256r1CombConsts)) :=
  Verified.of_correct (pk_rv hL) pk_ct pkRVC_implies

end VG.Proof.Ecdh.RISCV64.BrainpoolP256r1
