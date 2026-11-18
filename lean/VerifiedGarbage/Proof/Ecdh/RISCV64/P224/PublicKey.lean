module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.PublicKeyAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.Exchange
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.Tail
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.CombVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Spec.EcKey
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# P-224's public keys on RISC-V: correctness

The curve's `PkKit` for `Proof/Ecdh/RISCV64/PublicKeyAll.lean` (`[d]G` by the comb, whose table the state holds (`pkRVC`)),
and what that proof gives of `publicKeyP224`: it meets its contract by
register (`pkRV`), given the group law (`pk_rv`); and the point written to
`out` (`pointOut_ok`), which the compressed keys use too.
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.P224

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.P224
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_nil writeBytes_append)

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point W) :=
  Spec.EcKey.publicKey Spec.P224.curve (ofBytes (bytesAt m d 28))

def pkRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 57⟩
    let d : Region := ⟨s.gpr .a1, 28⟩
    let scratch : Region := ⟨s.gpr .a2, 8192⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      (s.gpr .a0).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 28 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat % 8 = 0
  post s s' :=
    match pk s.mem (s.gpr .a1) with
    | some (.affine x y) => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 57 = Spec.EcKey.encodePoint (.affine x y)
    | _ => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 57 = List.replicate 57 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2

/-- `pkRV` with the comb's table (`abi.withConsts`): `pkRV` for the state
without it, and what the table adds. -/
def pkRVC : Contract isa where
  pre s := pkRV.pre (stripConsts Impl.Ecdsa.RISCV64.Comb.p224CombConsts s) ∧
    ConstsOk Impl.Ecdsa.RISCV64.Comb.p224CombConsts 0 s
  post := pkRV.post
  pub s₁ s₂ := pkRV.pub s₁ s₂ ∧ s₁.syms Impl.Ecdsa.RISCV64.Comb.p224Sym = s₂.syms Impl.Ecdsa.RISCV64.Comb.p224Sym

/-- The curve's kit for its public key. -/
def pkit : PkKit where
  E := kit
  gmulN := VG.Impl.Ecdsa.RISCV64.Comb.mulGP224Name
  gmulC := VG.Impl.Ecdsa.RISCV64.Comb.mulGP224
  GT0 := fun s => ConstsOk Impl.Ecdsa.RISCV64.Comb.p224CombConsts 0 s
  GT := Ecdsa.RISCV64.P224.Comb.TabAt
  gt_start := fun hk hw => Ecdsa.RISCV64.P224.Comb.tabAt_of_consts hk hw
  gt_frame := fun hk h sy rd F => h.of_frame sy rd F (Ecdsa.RISCV64.P224.Comb.tab_wr_of_consts hk)
  tailG_ok := fun hL _ _ hw h3 a1 a2 a3 a4 a5 a6 a7 a8 hx hy hbp hT =>
    Ecdsa.RISCV64.P224.Comb.tailG_ok hL hw h3 ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ hx hy hbp hT
  tail_one := by decide
  affine_ok := fun hw hacc hone =>
    affine_ok hw (t := YM) (o := YO) (a := RY) (by decide) (by decide) (by decide) (by decide) hacc hone

/-- `pointOut`: `04 ‖ x ‖ y` from the slots `xo` and `yo` (or zeros, by the
mask `a7`, which the flag holds) to `out`, the flag's low bit to `a0`, and
the saved registers restored. -/
theorem pointOut_ok {s : State} {base out : Addr} (hw : WsReg s base) (h2 : s.gpr .s2 = out)
    (hfit : out.toNat + 57 ≤ 2 ^ 64)
    (hout : ∀ i < 57, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hdis : (⟨out, 57⟩ : Region).Disjoint ⟨base, 8192⟩)
    {B : Bool} (ha7 : s.gpr .a7 = maskOf B) (hfl : word s.mem base FL = maskOf B)
    {xo yo : Nat} (hxo : xo < 44) (hyo : yo < 44) (hxo' : xo < 41) (hyo' : yo < 41) :
    WP isa (.block (pointOut224 xo yo)) s fun s' =>
      s'.gpr .a0 = (if B then 1 else 0) ∧
      bytesAt s'.mem out 57 = (if B then 4 else 0) ::
        (toBytes 28 (if B then sv base s xo else 0) ++ toBytes 28 (if B then sv base s yo else 0)) ∧
      s'.gpr .s0 = word s.mem base 0 ∧ s'.gpr .s1 = word s.mem base 8 ∧ s'.gpr .s2 = word s.mem base 16 ∧
      s'.gpr .ra = word s.mem base 24 ∧ s'.gpr .s3 = word s.mem base 32 ∧
      (∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp :=
  kit.pointOut_ok hw h2 hfit hout hdis ha7 hfl (by omega_using [hxo, hxo']) (by omega_using [hyo, hyo'])

/-- The contract's postcondition is the kit's. -/
theorem post_eq : pkRV.post = kit.pkPost := by kernel_rfl

theorem pk_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : pkRVC.pre s) :
    ∃ t s', Exec isa publicKeyP224 s t s' ∧ abiPreserved s s' ∧ pkRVC.post s s' := by
  obtain ⟨⟨hrd, hwr, hod, hdd, hfo, hfd, hfs, hal⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr] at hrd hwr hod hdd hfo hfd hfs hal
  obtain ⟨t, s', he, hp, hq⟩ := pkit.pk_ok hL
    ⟨stripConsts_rd_mem (by rw [hrd]; exact List.mem_singleton_self _), hwr, hod, hdd, hfo, hfd, hfs, hal, hk⟩
  exact ⟨t, s', he, hp, (congrFun (congrFun post_eq s) s').mpr hq⟩

end VG.Proof.Ecdh.RISCV64.P224
