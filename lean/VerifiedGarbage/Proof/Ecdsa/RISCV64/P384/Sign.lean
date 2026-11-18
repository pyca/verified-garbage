module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.SignAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.Exchange
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.Tail
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.CombVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Sign
public import VerifiedGarbage.Spec.Ecdsa
public import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Order.Verified
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Order.Lit
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb
meta import VerifiedGarbage.Impl.Weierstrass.Layout.Mont
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Order.Lit

/-!
# ECDSA signatures over P-384 on RISC-V: correctness

`vg_ecdsa_p384_sign` meets its contract by register (`signRV`, with the comb's table (`signRVC`)),
given the group law (`sign_rv`). The proof is the one of every curve, `SignAll.Kit.sign_ok`
(`Proof/Ecdsa/RISCV64/SignAll.lean`), from what `skit` says of this one: ECDH's kit, the functions
modulo `n` (`order_ok`) and the chain of `n - 2` (`chainN_ok`); `R = [k]G` is the comb's (`Comb.tailG_ok`).
Here are also the statements about this curve that other modules use.
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.

set_option exponentiation.threshold 512

namespace VG.Proof.Ecdsa.RISCV64.P384

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg VG.Impl.Ecdsa.RISCV64.Sign
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdh.RISCV64.P384
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt hashToInt)
open VG.WriteBytes (writeBytes)

/-- The functions of `n` meet the contracts by register. -/
theorem order_ok : FieldOk p384Order :=
  ⟨P384Order.mul_rv, P384Order.add_rv, P384Order.sub_rv,
    Impl.Weierstrass.RISCV64.P384Order.mulFn_noFrames,
    Impl.Weierstrass.RISCV64.P384Order.addFn_noFrames, Impl.Weierstrass.RISCV64.P384Order.subFn_noFrames,
    P384Order.mulA_rv, P384Order.addA_rv, P384Order.subA_rv,
    Impl.Weierstrass.RISCV64.P384Order.mulFnA_noFrames,
    Impl.Weierstrass.RISCV64.P384Order.addFnA_noFrames, Impl.Weierstrass.RISCV64.P384Order.subFnA_noFrames⟩

instance : NeZero p384Order.S.m := ⟨by decide⟩

instance : NeZero W.n := ⟨by decide⟩

theorem n_odd : W.n % 2 = 1 := by decide

/-- The chain is `n - 2`'s. -/
theorem chainN_ok : ChainOkR (Cfg.chainN p384) (W.n - 2) := ChainOkR.of_check (by lit_decide)

/-- The signature of `digest` with the private key at `d` and the secret
number at `k`, as the specification computes it. -/
abbrev sg (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith W (ofBytes (bytesAt m d 48)) (hashToInt W (bytesAt m digest 48)) (ofBytes (bytesAt m k 48))

def signRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 96⟩
    let d : Region := ⟨s.gpr .a1, 48⟩
    let digest : Region := ⟨s.gpr .a2, 48⟩
    let k : Region := ⟨s.gpr .a3, 48⟩
    let scratch : Region := ⟨s.gpr .a4, 8192⟩
    s.rd = [d, digest, k] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      digest.Disjoint scratch ∧ k.Disjoint scratch ∧ (s.gpr .a0).toNat + 96 ≤ 2 ^ 64 ∧
      (s.gpr .a1).toNat + 48 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 48 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 48 ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat + 8192 ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat % 8 = 0
  post s s' :=
    match sg s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) with
    | some rs => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 96 = Spec.Ecdsa.encode W rs
    | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 96 = List.replicate 96 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4

/-- `signRV` with the comb's table (`abi.withConsts`): `signRV` for the state
without it, and what the table adds. -/
def signRVC : Contract isa where
  pre s := signRV.pre (stripConsts Impl.Ecdsa.RISCV64.Comb.p384CombConsts s) ∧
    ConstsOk Impl.Ecdsa.RISCV64.Comb.p384CombConsts 0 s
  post := signRV.post
  pub s₁ s₂ := signRV.pub s₁ s₂ ∧ s₁.syms Impl.Ecdsa.RISCV64.Comb.p384Sym = s₂.syms Impl.Ecdsa.RISCV64.Comb.p384Sym

theorem nconsts_lt : ∀ e ∈ Cfg.nConsts p384, e.2 < 2 ^ 384 := by decide

/-- What the proofs shared by every curve (`SignAll.lean`) need of this one: ECDH's kit, and the
functions modulo `n`. -/
def skit : SignAll.Kit where
  toKit := VG.Proof.Ecdh.RISCV64.P384.kit
  FN := p384Order
  order_ok := order_ok
  FNk := rfl
  FNm := rfl
  n_odd := n_odd
  pn := by decide
  nBits := by decide
  chainN_ok := chainN_ok
  nconsts_lt := nconsts_lt

theorem sign_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : signRVC.pre s) :
    ∃ t s', Exec isa signP384 s t s' ∧ abiPreserved s s' ∧ signRVC.post s s' := by
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

/-! The constant-time analyses of the calls of the functions of P-384's `n` from their arguments,
with the comb's table public, each done once for every check of code that calls it
(`taint_decide_sum`), which keep what is public of `s0`–`s11`: the functions write none of them. -/

taint_summary nMulSymSum : (taintSym [Impl.Ecdsa.RISCV64.Comb.p384Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.p384n.fn "mul") Impl.Weierstrass.RISCV64.P384Order.mulFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])

taint_summary nAddSymSum : (taintSym [Impl.Ecdsa.RISCV64.Comb.p384Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.p384n.fn "add") Impl.Weierstrass.RISCV64.P384Order.addFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])

taint_summary nSubSymSum : (taintSym [Impl.Ecdsa.RISCV64.Comb.p384Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.p384n.fn "sub") Impl.Weierstrass.RISCV64.P384Order.subFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])

end VG.Proof.Ecdsa.RISCV64.P384
