module

public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Config
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.EcKey.AArch64.Secp256k1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Config
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Proof.EcKey.AArch64.Secp256k1.Lit
public import VerifiedGarbage.Impl.EcKey.Secp256k1.AArch64
public import VerifiedGarbage.Proof.EcKey.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Main
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Impl.EcKey.Secp256k1.AArch64
meta import VerifiedGarbage.Proof.EcKey.AArch64.Main
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Main
meta import VerifiedGarbage.Proof.EcKey.PublicKey
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Spec.EcKey.Secp256k1
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.EcKey.Secp256k1
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.Contract

/-! ### `EcKey.AArch64.Secp256k1.Contract`, which only this module used -/

section

/-!
# secp256k1 public keys on AArch64: the contract the proof is written against

The facts of `Spec.EcKey.Secp256k1.inst.publicKeyContract` for AArch64, by name:
`vg_ec_secp256k1_public_key(out = x0, d = x1, scratch = x2)`, the result in `w0`.
-/

@[expose] public section

namespace VG.Proof.EcKey.AArch64.Secp256k1

open VG VG.AArch64 Spec.Weierstrass Spec.EcKey

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.Secp256k1.curve) :=
  publicKey Spec.Secp256k1.curve (ofBytes (bytesAt m d 32))

def pkAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 65⟩
    let d : Region := ⟨s.gpr .x1, 32⟩
    let scratch : Region := ⟨s.gpr .x2, 8192⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ out.Disjoint d ∧ d.Disjoint scratch ∧
      (s.gpr .x0).toNat + 65 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match pk s.mem (s.gpr .x1) with
    | some (.affine x y) => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 65 = encodePoint (.affine x y)
    | _ => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 65 = List.replicate 65 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 65⟩, ⟨0x8000, 8192⟩]

theorem implies : pkAArch64.Implies (Spec.EcKey.Secp256k1.inst.publicKeyContract AArch64.abi) := by
  exact
    { pre := by
        sig_implies_pre [Spec.EcKey.Secp256k1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.Secp256k1.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, pkAArch64, pk]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.Secp256k1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.Secp256k1.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, pkAArch64, pk]
        simp only [pkAArch64, pk, Spec.Secp256k1.curve] at h
        revert h
        generalize publicKey _ _ = q
        rcases q with _ | _ | ⟨x, y⟩ <;> exact id
      pub := by
        sig_implies_pub [Spec.EcKey.Secp256k1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.Secp256k1.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, pkAArch64, pk]
      sat := by
        sig_implies_sat [Spec.EcKey.Secp256k1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.Secp256k1.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, satState] [satState] using satState }

end VG.Proof.EcKey.AArch64.Secp256k1

end

end

/-! ### `EcKey.AArch64.Secp256k1.Main`, which only this module used -/

section

/-! # secp256k1 public-key derivation without constant tables -/

@[expose] public section

namespace VG.Proof.EcKey.AArch64.Secp256k1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.Secp256k1
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

structure PkPre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x1, c.C.len⟩]
  wr : s.wr = [⟨s.gpr .x0, 1 + 2 * c.C.len⟩, ⟨s.gpr .x2, size⟩]
  out_sc : Region.Disjoint ⟨s.gpr .x0, 1 + 2 * c.C.len⟩ ⟨s.gpr .x2, size⟩
  out_d : Region.Disjoint ⟨s.gpr .x0, 1 + 2 * c.C.len⟩ ⟨s.gpr .x1, c.C.len⟩
  d_sc : Region.Disjoint ⟨s.gpr .x1, c.C.len⟩ ⟨s.gpr .x2, size⟩
  out_fit : (s.gpr .x0).toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64
  sc_fit : (s.gpr .x2).toNat + size ≤ 2 ^ 64


theorem publicKeyWithStage_ok {c : Cfg} (hc : BaseCfgOk c) (hC : Law c.C)
    (mulCode : Prog isa)
    (hmul : ∀ {s₀ : State} {base : Addr} {s : State}, St₁ c none s₀ base s →
      WP isa (.seq mulCode (.seq c.pPow (.block []))) s (St₂ c none s₀ base))
    {s₀ : State} (hp : PkPre c s₀) :
    WP isa (Impl.EcKey.AArch64.Cfg.publicKeyWith c mulCode) s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ PkPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine WP.seq (WP.mono_syms (args_ok s₀) fun s₁ ⟨x4₁, x3₁, x2₁, k₁⟩ sy₁ => ?_)
  have x1₁ : s₁.gpr .x1 = s₀.gpr .x1 := k₁.gpr _ (by decide)
  have x0₁ : s₁.gpr .x0 = s₀.gpr .x0 := k₁.gpr _ (by decide)
  have hp₁ : SetupPre c s₁ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [k₁.wr, hp.wr, x4₁]; simp
    · rw [x3₁]; exact inRegions_words (by rw [k₁.rd, hp.rd]; simp) (by have := hc.len_hi; have := hc.n10; omega_arith)
    · rw [x1₁]; exact inRegions_words (by rw [k₁.rd, hp.rd]; simp) (by have := hc.len_hi; have := hc.n10; omega_arith)
    · rw [x2₁]; exact inRegions_words (by rw [k₁.rd, hp.rd]; simp) (by have := hc.len_hi; have := hc.n10; omega_arith)
    · rw [x1₁, x4₁]; exact hp.d_sc
    · rw [x2₁, x4₁]; exact hp.d_sc
    · rw [x3₁, x4₁]; exact hp.d_sc
    · rw [x4₁]; exact hp.sc_fit
  obtain ⟨t, s₂N, ex', S₂⟩ := stage₁ hc (.inl rfl) hp₁
    (rest := .seq mulCode (.seq c.pPow (.block [])))
    (Q := St₂ c none s₁ (s₁.gpr .x4)) fun _ S₁ =>
      hmul S₁
  rw [x4₁] at S₂
  let sN := s₁
  let s₂ := s₂N
  have g : ∀ r, sN.gpr r = s₁.gpr r := fun _ => rfl
  have mN : sN.mem = s₀.mem := k₁.mem
  have g₂ : s₂.gpr = s₂N.gpr := rfl
  have m₂ : s₂.mem = s₂N.mem := rfl
  have w₂ : s₂.wr = s₁.wr := S₂.wr
  have hwr₁ : s₁.wr = [⟨s₀.gpr .x0, 1 + 2 * c.C.len⟩, ⟨s₀.gpr .x2, size⟩] := by rw [k₁.wr, hp.wr]
  have sv₂ : ∀ i, sv c (s₀.gpr .x2) s₂ i = sv c (s₀.gpr .x2) s₂N i := fun _ => rfl
  have hs₂' : Scr s₂ (s₀.gpr .x2) size := S₂.scr
  have F₂ : Fixed c (s₀.gpr .x2) sN.gpr s₂.mem := S₂.fixed
  obtain ⟨t', s', exm, xv, yv, hxl, hx, hyl, hy, bytes, rax, saved⟩ :=
    middle_ok hc hs₂' F₂ (by rw [sv₂]; exact S₂.acc_lt) (by rw [m₂]; exact S₂.flag)
      (by rw [g₂, S₂.x20, g, x0₁]) hp.out_fit (by rw [w₂, hwr₁]; simp) hp.out_sc
  refine ⟨_, _, .seq ex' exm, fun r hr => ?_, ?_⟩
  · have hsv : ∀ r ∈ Cfg.saved.map Prod.fst, r ∉ [Reg.x2, .x3, .x4] := by decide
    rw [saved r hr, g, k₁.gpr r (hsv r hr)]
  -- The specification.
  have hk : kv c sN = dk c s₀ := by simp only [kv, dk, mN, g, x3₁]
  have hD : sv c (s₀.gpr .x2) s₂ D = dk c s₀ := by
    rw [sv₂, S₂.d, shAt_none, Nat.shiftRight_zero]; simp only [dv, dk, k₁.mem, x1₁]
  have hR := S₂.rep
  rw [hk] at hR
  have hZ : ∀ {i}, tmv c.C c.n (s₀.gpr .x2) s₂N (c.sl i) = toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s₂ i) :=
    fun {i} => by rw [sv₂]
  have acc := S₂.acc
  rw [← sv₂, hZ] at acc
  rw [hZ, hZ, hZ] at hR
  have hxX : Fin.ofNat c.C.p xv = toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s₂ RX) *
      toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s₂ RZ) ^ (c.C.p - 2) := by rw [hx, acc]
  have hyY : Fin.ofNat c.C.p yv = toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s₂ RY) *
      toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s₂ RZ) ^ (c.C.p - 2) := by rw [hy, acc]
  have hz := toM_eq_zero_iff hpR (x := sv c (s₀.gpr .x2) s₂ RZ) (by rw [sv₂]; exact S₂.rz_lt)
  unfold PkPost
  rw [publicKey_eq hC hR hxl hxX hyl hyY]
  by_cases hd : 1 ≤ dk c s₀ ∧ dk c s₀ < c.C.n
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]
    by_cases h0 : sv c (s₀.gpr .x2) s₂ RZ = 0
    · have hok : ok c (s₀.gpr .x2) s₂ = false := decide_eq_false (by rw [hD]; omega_using [h0])
      rw [ite_eq_left_of_eq_true _ _ (eq_true (hz.mpr h0))]
      exact ⟨by rw [rax, hok]; rfl, by rw [bytes, hok]; rfl⟩
    · have hok : ok c (s₀.gpr .x2) s₂ = true := decide_eq_true (by rw [hD]; omega_using [hd, h0])
      rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => h0 (hz.mp h)))]
      refine ⟨by rw [rax, hok]; rfl, ?_⟩
      rw [bytes, hok]
      rfl
  · have hok : ok c (s₀.gpr .x2) s₂ = false := decide_eq_false (by rw [hD]; omega_using [hd])
    rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
    exact ⟨by rw [rax, hok]; rfl, by rw [bytes, hok]; rfl⟩

theorem publicKey_ok (hc : BaseCfgOk secp256k1) (hC : Law secp256k1.C)
    {s₀ : State} (hp : PkPre secp256k1 s₀) :
    WP isa Impl.EcKey.AArch64.publicKeySecp256k1 s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ PkPost secp256k1 s₀ s' :=
  publicKeyWithStage_ok hc hC gMul
    (fun S => Ecdsa.AArch64.Secp256k1.stage₂ hc hC S fun _ S₂ => WP.block_nil S₂) hp

end VG.Proof.EcKey.AArch64.Secp256k1

end

end

/-!
# secp256k1 public keys on AArch64: `Verified`

secp256k1 is a curve the proof supports (`secp256k1_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.Secp256k1.law`), so `publicKey_ok`
gives the contract's postcondition; `x19` and `x20` are restored, and no
instruction writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.EcKey.AArch64.Secp256k1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.EcKey.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.Secp256k1

theorem pre_of {s : State} (h : pkAArch64.pre s) : PkPre secp256k1 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem post_of {s s' : State} (h : PkPost secp256k1 s s') : pkAArch64.post s s' := by
  unfold PkPost at h
  dsimp only [pkAArch64]
  revert h
  generalize hq : pk s.mem (s.gpr .x1) = q
  rw [show Spec.EcKey.publicKey secp256k1.C (dk secp256k1 s) = pk s.mem (s.gpr .x1) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

theorem pk_a64 (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Weierstrass.AArch64.InvSounds)
    (s : State) (hs : pkAArch64.pre s) :
    ∃ t s', Exec isa publicKeySecp256k1 s t s' ∧ abiPreserved s s' ∧ pkAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := publicKey_ok (secp256k1_ok hI) hL (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he (by lit_decide) (by lit_decide) (by lit_decide) hsv, post_of hpost⟩

theorem pk_ct : ConstantTime isa pkAArch64.pre pkAArch64.pub publicKeySecp256k1 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ ⟨h0, h1, h2, hsp⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩) (by taint_decide)

theorem pk_verified (hL : Weierstrass.Law Spec.Secp256k1.curve)
    (hI : Weierstrass.AArch64.InvSounds) :
    Verified AArch64.target publicKeySecp256k1 (Spec.EcKey.Secp256k1.inst.publicKeyContract AArch64.abi) :=
  Verified.of_correct (pk_a64 hL hI) pk_ct implies

/-- `vg_ec_secp256k1_public_key` as it is emitted, its cleanup included
(`Impl.EcKey.AArch64.Fn.publicKeySecp256k1`), meets its contract in constant time and
returns without secret residue. -/
theorem pk_scrubbed (hL : Weierstrass.Law Spec.Secp256k1.curve)
    (hI : Weierstrass.AArch64.InvSounds) :
    VerifiedScrubbed AArch64.target Impl.EcKey.AArch64.Fn.publicKeySecp256k1
      (Spec.EcKey.Secp256k1.inst.publicKeyContract AArch64.abi) 32 :=
  AArch64.ScrubAll.verifiedScrubbed (api := Spec.EcKey.Secp256k1.publicKeyApi)
    { code := publicKeySecp256k1, verified := pk_verified hL hI } _
    (Proof.EcKey.AArch64.Scrub.publicKeyOk _) (by dsimp only; lit_decide)

end VG.Proof.EcKey.AArch64.Secp256k1
