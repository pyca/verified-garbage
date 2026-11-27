module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.SignAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.Exchange
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.Tail
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Tail
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Sign
public import VerifiedGarbage.Spec.Ecdsa
public import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Order.Lit
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Order.Fn
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Verified
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.FieldRV
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Impl.Weierstrass.RISCV64.P256Order
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Order.Fn
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Verified

/-! ### `Weierstrass.RISCV64.P256Order.Verified`, which only this module used -/

section

/-!
# Arithmetic modulo P-256's order on RISC-V: verified

As the functions modulo `p` (`Proof/Weierstrass/RISCV64/P256Field/Verified.lean`),
whose lemmas this uses: each function meets a contract by register from
`fn_ok`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P256Order

open VG VG.RISCV64
open VG.Impl.Weierstrass.RISCV64.P256Field (fn)
open VG.Proof.Weierstrass.RISCV64.P256Field (numAt_d4 keeps_of_frame fn_ct read_zero satWs CoreOk fn_ok d4)
open VG.Impl.Weierstrass.RISCV64.P256Order (mulFn addFn subFn)
open VG.Impl.Weierstrass.Mont (numAt Keeps p256n Fits)
open VG.Proof.Weierstrass.RISCV64 (offArg rvPre arg res rvPub mulRV addRV subRV)

theorem n_eq : p256n.m = N := by decide

/-- `fn core` meets a contract by register, from `fn_ok`. -/
theorem fn_rv {core : Prog isa} {pre : Nat → Nat → Prop} {res : Nat → Nat → Nat → Prop}
    (hcore : CoreOk core pre res) {s : State} (hs : rvPre p256n s) (hp : pre (arg p256n s .a2) (arg p256n s .a3)) :
    ∃ t s', Exec isa (fn core) s t s' ∧ abiPreserved s s' ∧
      res (arg p256n s .a2) (arg p256n s .a3) (numAt s'.mem (s.gpr .a0) (offArg s .a1) 4) ∧
      Keeps 4 (s.gpr .a0) (offArg s .a1) s.mem s'.mem := by
  obtain ⟨-, hwr, hfit, ⟨fo, fa, fb⟩, hal⟩ := hs
  simp only [Fits, VG.Proof.Weierstrass.RISCV64.rvOwn_le (show p256n.k ≤ 6 by decide), Impl.Weierstrass.Mont.ownAt,
    Impl.Weierstrass.Mont.ownBytes] at fo fa fb
  simp only [arg, show p256n.k = 4 from rfl, numAt_d4] at hp ⊢
  obtain ⟨t, s', he, v, f, g, -, -, sp⟩ := fn_ok hcore rfl hal (by rw [hwr]; simp) hfit fo fa fb hp
  refine ⟨t, s', he, ⟨fun r hr => g r (by revert hr; revert r; decide), sp, g _ (by decide)⟩, v,
    keeps_of_frame fo f⟩

theorem mul_rv (s : State) (hs : (mulRV p256n).pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ (mulRV p256n).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fn_rv (@mulCore_core) hs.1 (by rw [← n_eq]; exact hs.2)
  exact ⟨t, s', he, a, by rw [n_eq]; exact v1, by rw [n_eq]; exact v2, k⟩

theorem add_rv (s : State) (hs : (addRV p256n).pre s) :
    ∃ t s', Exec isa addFn s t s' ∧ abiPreserved s s' ∧ (addRV p256n).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv (@addCore_core) hs.1 (by rw [← n_eq]; exact hs.2)
  exact ⟨t, s', he, a, by rw [n_eq]; exact v, k⟩

theorem sub_rv (s : State) (hs : (subRV p256n).pre s) :
    ∃ t s', Exec isa subFn s t s' ∧ abiPreserved s s' ∧ (subRV p256n).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv (@subCore_core) hs.1 (by rw [← n_eq]; exact hs.2)
  exact ⟨t, s', he, a, by rw [n_eq]; exact v, k⟩

theorem mulA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV p256n)).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.P256Order.mulFnA s t s' ∧ abiPreserved s s' ∧ (mulRV p256n).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ :=
    P256Field.fnA_rv rfl (@mulCore_core) hs.1.1 hs.2 (by rw [← n_eq]; exact hs.1.2)
  exact ⟨t, s', he, a, by rw [n_eq]; exact v1, by rw [n_eq]; exact v2, k⟩

theorem addA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV p256n)).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.P256Order.addFnA s t s' ∧ abiPreserved s s' ∧ (addRV p256n).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := P256Field.fnA_rv rfl (@addCore_core) hs.1.1 hs.2 (by rw [← n_eq]; exact hs.1.2)
  exact ⟨t, s', he, a, by rw [n_eq]; exact v, k⟩

theorem subA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV p256n)).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.P256Order.subFnA s t s' ∧ abiPreserved s s' ∧ (subRV p256n).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := P256Field.fnA_rv rfl (@subCore_core) hs.1.1 hs.2 (by rw [← n_eq]; exact hs.1.2)
  exact ⟨t, s', he, a, by rw [n_eq]; exact v, k⟩


end VG.Proof.Weierstrass.RISCV64.P256Order

end

end

/-!
# ECDSA signatures over P-256 on RISC-V: correctness

`vg_ecdsa_p256_sign` meets its contract by register (`signRV`, with the comb's table (`signRVC`)),
given the group law (`sign_rv`). The proof is the one of every curve, `SignAll.Kit.sign_ok`
(`Proof/Ecdsa/RISCV64/SignAll.lean`), from what `skit` says of this one: ECDH's kit, the functions
modulo `n` (`order_ok`) and the chain of `n - 2` (`chainN_ok`); `R = [k]G` is the comb's (`Comb.tailG_ok`).
Here are also the statements about this curve that other modules use.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P256

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg VG.Impl.Ecdsa.RISCV64.Sign
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdh.RISCV64.P256
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt hashToInt)
open VG.WriteBytes (writeBytes)

/-- The functions of `n` meet the contracts by register. -/
theorem order_ok : FieldOk p256Order :=
  ⟨P256Order.mul_rv, P256Order.add_rv, P256Order.sub_rv,
    Impl.Weierstrass.RISCV64.P256Order.mulFn_noFrames,
    Impl.Weierstrass.RISCV64.P256Order.addFn_noFrames, Impl.Weierstrass.RISCV64.P256Order.subFn_noFrames,
    P256Order.mulA_rv, P256Order.addA_rv, P256Order.subA_rv,
    Impl.Weierstrass.RISCV64.P256Order.mulFnA_noFrames,
    Impl.Weierstrass.RISCV64.P256Order.addFnA_noFrames, Impl.Weierstrass.RISCV64.P256Order.subFnA_noFrames⟩

instance : NeZero p256Order.S.m := ⟨by decide⟩

instance : NeZero W.n := ⟨by decide⟩

theorem n_odd : W.n % 2 = 1 := by decide

/-- The chain is `n - 2`'s. -/
theorem chainN_ok : ChainOkR (Cfg.chainN p256) (W.n - 2) := ChainOkR.of_check (by lit_decide)

/-- The signature of `digest` with the private key at `d` and the secret
number at `k`, as the specification computes it. -/
abbrev sg (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith W (ofBytes (bytesAt m d 32)) (hashToInt W (bytesAt m digest 32)) (ofBytes (bytesAt m k 32))

def signRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 64⟩
    let d : Region := ⟨s.gpr .a1, 32⟩
    let digest : Region := ⟨s.gpr .a2, 32⟩
    let k : Region := ⟨s.gpr .a3, 32⟩
    let scratch : Region := ⟨s.gpr .a4, 8192⟩
    s.rd = [d, digest, k] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      digest.Disjoint scratch ∧ k.Disjoint scratch ∧ (s.gpr .a0).toNat + 64 ≤ 2 ^ 64 ∧
      (s.gpr .a1).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 32 ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat + 8192 ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat % 8 = 0
  post s s' :=
    match sg s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) with
    | some rs => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 64 = Spec.Ecdsa.encode W rs
    | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 64 = List.replicate 64 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4

/-- `signRV` with the comb's table (`abi.withConsts`): `signRV` for the state
without it, and what the table adds. -/
def signRVC : Contract isa where
  pre s := signRV.pre (stripConsts Impl.Ecdsa.RISCV64.Comb.p256CombConsts s) ∧
    ConstsOk Impl.Ecdsa.RISCV64.Comb.p256CombConsts 0 s
  post := signRV.post
  pub s₁ s₂ := signRV.pub s₁ s₂ ∧ s₁.syms Impl.Ecdsa.RISCV64.Comb.p256Sym = s₂.syms Impl.Ecdsa.RISCV64.Comb.p256Sym

theorem nconsts_lt : ∀ e ∈ Cfg.nConsts p256, e.2 < 2 ^ 256 := by decide

/-- What the proofs shared by every curve (`SignAll.lean`) need of this one: ECDH's kit, and the
functions modulo `n`. -/
def skit : SignAll.Kit where
  toKit := VG.Proof.Ecdh.RISCV64.P256.kit
  FN := p256Order
  order_ok := order_ok
  FNk := rfl
  FNm := rfl
  n_odd := n_odd
  pn := by decide
  nBits := by decide
  chainN_ok := chainN_ok
  nconsts_lt := nconsts_lt

theorem sign_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : signRVC.pre s) :
    ∃ t s', Exec isa signP256 s t s' ∧ abiPreserved s s' ∧ signRVC.post s s' := by
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

end VG.Proof.Ecdsa.RISCV64.P256
