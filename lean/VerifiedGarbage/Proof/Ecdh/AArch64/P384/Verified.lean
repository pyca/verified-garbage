module

public import VerifiedGarbage.Proof.Ecdh.AArch64.Main
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.P384.EcdhDouble
import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
import VerifiedGarbage.Proof.Ecdh.AArch64.MulJ4
import VerifiedGarbage.Proof.Ecdh.AArch64.WithMul
import VerifiedGarbage.Proof.Ecdh.AArch64.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.AbiOnce
public import VerifiedGarbage.Impl.Ecdh.P384.AArch64
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
meta import VerifiedGarbage.Proof.Ecdh.AArch64.Main
meta import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
meta import VerifiedGarbage.Proof.Ecdh.AArch64.MulJ4
meta import VerifiedGarbage.Proof.Ecdh.AArch64.WithMul
meta import VerifiedGarbage.Proof.Ecdh.AArch64.P384.Lit
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.AbiOnce
meta import VerifiedGarbage.Impl.Ecdh.P384.AArch64
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
public import VerifiedGarbage.Impl.P384.EcdhMadd
import VerifiedGarbage.Proof.P384.Ops
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
meta import VerifiedGarbage.Impl.P384.EcdhMadd
meta import VerifiedGarbage.Proof.P384.Ops
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
public import VerifiedGarbage.Impl.P384.EcdhSelect
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowEntry
import VerifiedGarbage.Proof.Ed25519.AArch64.CombEntry
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
meta import VerifiedGarbage.Impl.P384.EcdhSelect
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowEntry
meta import VerifiedGarbage.Proof.Ed25519.AArch64.CombEntry
meta import VerifiedGarbage.Proof.Mont.AArch64.Blocks
meta import VerifiedGarbage.Proof.Mont.AArch64.Chain
meta import VerifiedGarbage.Proof.Mont.AArch64.Rounds
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
meta import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
meta import VerifiedGarbage.Proof.Weierstrass.InverseContract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.P384
public import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.EcKey.P384
meta import VerifiedGarbage.Spec.Ecdh.Generic
meta import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
public import VerifiedGarbage.Spec.Ecdh.P384
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved

/-! ### `Ecdh.AArch64.P384.Contract`, which only this module used -/

section

/-!
# ECDH over P-384 on AArch64: the contract the proof is written against

The facts of `Spec.Ecdh.P384.exchangeApi`'s contract for AArch64, by name:
`vg_ecdh_p384(out = x0, d = x1, peer = x2, scratch = x3)`, the result in
`w0`.
-/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.P384

open VG VG.AArch64 Spec.Weierstrass Spec.EcKey

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.P384.curve (ofBytes (bytesAt m d 48)) (bytesAt m peer 97)

def ecdhAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 48⟩
    let d : Region := ⟨s.gpr .x1, 48⟩
    let peer : Region := ⟨s.gpr .x2, 97⟩
    let scratch : Region := ⟨s.gpr .x3, 8192⟩
    s.rd = [d, peer] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ out.Disjoint d ∧
      out.Disjoint peer ∧ d.Disjoint scratch ∧ peer.Disjoint scratch ∧
      (s.gpr .x0).toNat + 48 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match ex s.mem (s.gpr .x1) (s.gpr .x2) with
    | some z => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 48 = z
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 48 = List.replicate 48 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 48⟩, ⟨0x3000, 97⟩]
  wr := [⟨0x1000, 48⟩, ⟨0x8000, 8192⟩]

theorem implies :
    ecdhAArch64.Implies (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst AArch64.abi) := by
  exact
    { pre := by
        sig_implies_pre [Spec.EcKey.P384.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, ecdhAArch64, ex]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P384.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, ecdhAArch64, ex]
        simp only [ecdhAArch64, ex, Spec.P384.curve] at h
        revert h
        generalize Spec.Ecdh.exchange _ _ _ = q
        rcases q with _ | z <;> exact id
      pub := by
        sig_implies_pub [Spec.EcKey.P384.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, ecdhAArch64, ex]
      sat := by
        sig_implies_sat [Spec.EcKey.P384.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, satState] [satState] using satState }

end VG.Proof.Ecdh.AArch64.P384

end

end

/-! ### `P384.EcdhMadd`, which only this module used -/

section

/-!
# P-384's inline mixed addition

`madd_ok`: the inline mixed addition (`Impl/P384/EcdhMadd.lean`) does what
the window's must (`MaddSpec`), as `ofN_ok` shows of the field program's: its
operations are `fprog_ok`'s, on the slots the field program uses.
-/

@[expose] public section

-- Powers of two up to `2^384` are evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.P384.EcdhMadd
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P384.EcdhDouble
open VG.Impl.P384.EcdhMadd
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.P384.Ops (clobX ProgKeepX)
open VG.Proof.Weierstrass.AArch64.Mont (p384)
open Spec.Weierstrass

/-- The inline mixed addition, as the window's. -/
theorem madd_ok {C : Curve} (hC : C.p = p384) {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) : MaddSpec K C base size (.block madd) := by
  intro E s hI
  have oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  have oE := pt_other (K := K) (p := K.E) (Or.inr (Or.inl rfl))
  have oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  have sl := fun (P : Pt) (h : ∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) x (hx : x ∈ [P.x, P.y, P.z]) =>
    List.mem_append_right (winRo K) (h x hx)
  have w1 := winJ_sl oD (sl _ oR) (sl _ oE)
  have hAp := hL.rcbApart_D (Or.inr rfl)
  rw [madd, maddJ_eq]
  refine WP.mono (Ops.fprog_ok hC hL.lay hA.al hp _ hI (fun op hop x hx => w1.1 x (ofN_slots op hop x hx))
    (readsOk_mono (ofN_readsOk maddJN_ok _ _ _ _) fun x hx => hx)) fun s' ⟨k, I⟩ => ?_
  have hw : ∀ w ∈ (ofN maddJN K.S K.R K.E K.D).map FOp.out, w ∈ rcbW K.S K.D := fun w hw => by
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact ofN_out maddJN_ok op hop
  refine ⟨⟨fun r hr => k.gpr r fun h => hr (by
      have : ∀ r ∈ clobX, r ∈ clob K.M.n ++ winSaved K.M.n := by decide
      exact this r h), k.rd, k.wr, k.sp⟩,
    (ProgKeepX.mono k hw).unch.mono fun w hw => ?_, _, I.sub fun x hx => ?_,
    fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ ofN_out maddJN_ok op hop),
    (congrArg₂ Prod.mk (ofN_run maddJN_ok hAp E 6)
      (congrArg₂ Prod.mk (ofN_run maddJN_ok hAp E 7) (ofN_run maddJN_ok hAp E 8))).trans (maddJN_run _)⟩
  · simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · exact Or.inl ⟨y, w1.2.1 y hy, rfl⟩
    · exact Or.inr rfl
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ofN_out_mem maddJN_ok hx)
    · exact Or.inl hx

/-- P-384's inline mixed addition, as the window's. -/
theorem maddOk {C : Curve} (hC : C.p = p384) (hL : WinLay K 8192) (hA : WinA K)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (base : Addr) : MaddOk K C base 8192 (some (.block madd)) := by
  intro m hm
  cases hm
  exact madd_ok hC hL hA hp

end VG.Proof.P384.EcdhMadd

end

end

/-!
# ECDH over P-384 on AArch64: `Verified`

P-384 is a curve the proof supports (`p384_ok`, given the inversions' soundness `InvSounds`, and `Law` for its group
law, which the registration file supplies: `Proof.P384.law` and `invSound_of_toM`), and of prime order
(`Proof.P384.primeOrder`), so the windows with a Jacobian accumulator compute `[d]P` (`mulJ4_ok`) and
`exchangeWith_ok'` gives the contract's postcondition; `x19`–`x25` are restored, and no
instruction writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter,
so not even the peer's key (which the contract would let leak) affects timing.
-/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.P384

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdh.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P384

theorem pre_of {s : State} (h : ecdhAArch64.pre s) : EPre p384 s := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h6, h7, h8, h9⟩

theorem post_of {s s' : State} (h : EPost p384 s s') : ecdhAArch64.post s s' := by
  unfold EPost at h
  dsimp only [ecdhAArch64]
  revert h
  generalize hq : ex s.mem (s.gpr .x1) (s.gpr .x2) = q
  rw [show Spec.Ecdh.exchange p384.C (dk p384 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (1 + 2 * p384.C.len)) = ex s.mem (s.gpr .x1) (s.gpr .x2) from rfl, hq]
  rcases q with _ | z <;> exact id

theorem ecdh_a64 (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P384.curve) (s : State) (hs : ecdhAArch64.pre s) :
    ∃ t s', Exec isa exchangeP384 s t s' ∧ abiPreserved s s' ∧ ecdhAArch64.post s s' := by
  -- In steps: elaborated in one term, the unifier would compare P-384's
  -- terms before the literals' facts are known.
  have ha : AbiOk exchangeP384 := by lit_decide
  have hmc : CallsKeep (Impl.Ecdh.AArch64.Cfg.middle p384) :=
    callsKeep_ofK (c := Impl.Ecdh.AArch64.Cfg.middle p384) (by lit_decide)
  have hmu : KeepsUntouched (Impl.Ecdh.AArch64.Cfg.middle p384) :=
    keepsUntouched_ofK (c := Impl.Ecdh.AArch64.Cfg.middle p384) (by lit_decide)
  have hm : Ecdh.AArch64.MulOk p384 (Cfg.mulJ4 p384
      (some (.block Impl.P384.EcdhDouble.doubleRD, .block Impl.P384.EcdhDouble.doubleDR))
      (some (.block Impl.P384.EcdhMadd.madd)) (some Impl.P384.EcdhSelect.sel)) :=
    Ecdh.AArch64.mulJ4_ok (p384_ok hI) hL hO rfl (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (P384.EcdhDouble.dblsOk P384.EcdhDouble.p384_C_p (Ecdh.AArch64.winLayQ (p384_ok hI)) (Ecdh.AArch64.winAQ (p384_ok hI))
        (Weierstrass.unitMod_pow_two (p384_ok hI).p_odd _))
      (P384.EcdhMadd.maddOk P384.EcdhDouble.p384_C_p (Ecdh.AArch64.winLayQ (p384_ok hI))
        (Ecdh.AArch64.winAQ (p384_ok hI)) (Weierstrass.unitMod_pow_two (p384_ok hI).p_odd _))
      P384.EcdhSelect.sel_ok
  obtain ⟨t, s', he, hsv, -, hpost⟩ :=
    Ecdh.AArch64.exchangeWith_ok' (p384_ok hI) hL hm (by decide +kernel) hmc hmu (pre_of hs)
  exact ⟨t, s', he, abiPreserved_ofK he ha hsv, post_of hpost⟩

theorem ecdh_ct : ConstantTime isa ecdhAArch64.pre ecdhAArch64.pub exchangeP384 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3⟩) (by taint_decide)

theorem ecdh_verified (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P384.curve) :
    Verified AArch64.target exchangeP384
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst AArch64.abi) :=
  Verified.of_correct (ecdh_a64 hL hI hO) ecdh_ct implies


/-- ECDH over P-384 as it is emitted, its cleanup included
(`Impl.Ecdh.AArch64.Fn.exchangeP384`), meets its contract in constant time and
returns without secret residue. -/
theorem exchange_scrubbed (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P384.curve) :
    VerifiedScrubbed AArch64.target VG.Impl.Ecdh.AArch64.Fn.exchangeP384
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst AArch64.abi) 32 :=
  VG.AArch64.Scrub.verifiedScrubbedAll (api := Spec.Ecdh.P384.exchangeApi)
    { code := exchangeP384, verified := ecdh_verified hL hI hO } _
    (VG.Proof.EcKey.AArch64.Scrub.exchangeOk _) (by dsimp only; lit_decide)

end VG.Proof.Ecdh.AArch64.P384
