module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.SignAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.Exchange
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.Tail
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.P224
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.CombVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Spec.Ecdsa
public import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.MulFn
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P224Field.Lit

/-!
# ECDSA signatures over P-224 on RISC-V: correctness

`vg_ecdsa_p224_sign` meets its contract by register (`signRV`, with the comb's table (`signRVC`)),
given the group law (`sign_rv`). The proof is the one of every curve, `SignAll.Kit.sign_ok`
(`Proof/Ecdsa/RISCV64/SignAll.lean`), from what `skit` says of this one: ECDH's kit, the functions
modulo `n` (`order_ok`) and the chain of `n - 2` (`chainN_ok`); `R = [k]G` is the comb's (`Comb.tailG_ok`).
Here are also the statements about this curve that other modules use.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P224

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg VG.Impl.Ecdsa.RISCV64.Sign
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdh.RISCV64.P224
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt hashToInt)
open VG.WriteBytes (writeBytes)

/-- The functions of `n` meet the contracts by register. -/
theorem order_ok : FieldOk p224Order :=
  ⟨P224Field.mul_rv_n, P224Field.add_rv_n, P224Field.sub_rv_n,
    Impl.Ecdsa.RISCV64.p224MulN_noFrames,
    Impl.Ecdsa.RISCV64.p224AddN_noFrames, Impl.Ecdsa.RISCV64.p224SubN_noFrames,
    P224Field.mulA_rv_n, P224Field.addA_rv_n, P224Field.subA_rv_n,
    Impl.Ecdsa.RISCV64.p224MulNA_noFrames,
    Impl.Ecdsa.RISCV64.p224AddNA_noFrames, Impl.Ecdsa.RISCV64.p224SubNA_noFrames⟩

instance : NeZero p224Order.S.m := ⟨by decide⟩

instance : NeZero W.n := ⟨by decide⟩

theorem n_odd : W.n % 2 = 1 := by decide

/-- The chain is `n - 2`'s. -/
theorem chainN_ok : ChainOkR (Cfg.chainN p224) (W.n - 2) := ChainOkR.of_check (by lit_decide)

/-- The signature of `digest` with the private key at `d` and the secret
number at `k`, as the specification computes it. -/
abbrev sg (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith W (ofBytes (bytesAt m d 28)) (hashToInt W (bytesAt m digest 28)) (ofBytes (bytesAt m k 28))

def signRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 56⟩
    let d : Region := ⟨s.gpr .a1, 28⟩
    let digest : Region := ⟨s.gpr .a2, 28⟩
    let k : Region := ⟨s.gpr .a3, 28⟩
    let scratch : Region := ⟨s.gpr .a4, 8192⟩
    s.rd = [d, digest, k] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      digest.Disjoint scratch ∧ k.Disjoint scratch ∧ (s.gpr .a0).toNat + 56 ≤ 2 ^ 64 ∧
      (s.gpr .a1).toNat + 28 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 28 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 28 ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat + 8192 ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat % 8 = 0
  post s s' :=
    match sg s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) with
    | some rs => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 56 = Spec.Ecdsa.encode W rs
    | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 56 = List.replicate 56 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4

/-- `signRV` with the comb's table (`abi.withConsts`): `signRV` for the state
without it, and what the table adds. -/
def signRVC : Contract isa where
  pre s := signRV.pre (stripConsts Impl.Ecdsa.RISCV64.Comb.p224CombConsts s) ∧
    ConstsOk Impl.Ecdsa.RISCV64.Comb.p224CombConsts 0 s
  post := signRV.post
  pub s₁ s₂ := signRV.pub s₁ s₂ ∧ s₁.syms Impl.Ecdsa.RISCV64.Comb.p224Sym = s₂.syms Impl.Ecdsa.RISCV64.Comb.p224Sym

theorem nconsts_lt : ∀ e ∈ Cfg.nConsts p224, e.2 < 2 ^ 256 := by decide

/-- What the proofs shared by every curve (`SignAll.lean`) need of this one: ECDH's kit, and the
functions modulo `n`. -/
def skit : SignAll.Kit where
  toKit := VG.Proof.Ecdh.RISCV64.P224.kit
  FN := p224Order
  order_ok := order_ok
  FNk := rfl
  FNm := rfl
  n_odd := n_odd
  pn := by decide
  nBits := by decide
  chainN_ok := chainN_ok
  nconsts_lt := nconsts_lt

theorem sign_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : signRVC.pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.P224.signP224 s t s' ∧ abiPreserved s s' ∧ signRVC.post s s' := by
  obtain ⟨hs₀, hk⟩ := hs
  obtain ⟨hrd, hwr, hod, hdd, hed, hkd, hfo, hfd, hfe, hfk, hfs, hal⟩ := hs₀
  simp only [stripConsts_gpr, stripConsts_wr] at hrd hwr hod hdd hed hkd hfo hfd hfe hfk hfs hal
  obtain ⟨t, s', he, h⟩ := skit.sign_ok hL (s := s)
    ⟨stripConsts_rd_mem (by rw [hrd]; exact .head _), stripConsts_rd_mem (by rw [hrd]; exact .tail _ (.head _)),
      stripConsts_rd_mem (by rw [hrd]; exact .tail _ (.tail _ (.head _))), hwr, hod, hdd, hed, hkd, hfo, hfd, hfe, hfk,
      hfs, hal⟩
    fun s₁ S sy₁ F₁ => Comb.tailG_ok hL S.ws S.s3
      ⟨S.tc.mp, S.tc.mn, S.tc.zero, S.tc.one, S.tc.onep, S.tc.ap, S.tc.b3p, S.tc.expp⟩ S.rx S.ry S.bp
      ((Comb.tabAt_of_consts hk (by rw [hwr]; simp)).of_frame sy₁ S.rd F₁ (Comb.tab_wr_of_consts hk))
  exact ⟨t, s', he, h⟩

end VG.Proof.Ecdsa.RISCV64.P224
