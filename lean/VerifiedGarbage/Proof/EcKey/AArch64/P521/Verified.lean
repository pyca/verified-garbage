module

public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.EcKey.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.EcKey.AArch64.P521.Lit
public import VerifiedGarbage.Impl.EcKey.P521.AArch64
meta import VerifiedGarbage.Proof.EcKey.AArch64.Main
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.EcKey.AArch64.P521.Lit
meta import VerifiedGarbage.Impl.EcKey.P521.AArch64
public import VerifiedGarbage.Spec.EcKey.P521
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Contract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Spec.EcKey.P521
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `EcKey.AArch64.P521.Contract`, which only this module used -/

section

/-!
# P-521 public keys on AArch64: the contract the proof is written against

The facts of `Spec.EcKey.P521.inst.publicKeyContract` for AArch64, under the
calling convention with the comb's tables (`Abi.withConsts p521.combConsts`),
by name: `vg_ec_p521_public_key(out = x0, d = x1, scratch = x2)`, the result
in `w0`, and the tables at the address of the static `p521.tsym`.
-/

@[expose] public section

namespace VG.Proof.EcKey.AArch64.P521

open VG VG.AArch64 Spec.Weierstrass Spec.EcKey
open VG.Impl.Ecdsa.AArch64 (p521)
open VG.Proof.Ecdsa.AArch64.P521 (TblHeld p521_combConsts p521_combWords_length satMem satMem_held)

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.P521.curve) :=
  publicKey Spec.P521.curve (ofBytes (bytesAt m d 66))

def pkAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 133⟩
    let d : Region := ⟨s.gpr .x1, 66⟩
    let scratch : Region := ⟨s.gpr .x2, 8192⟩
    s.rd = [d, ⟨s.syms p521.tsym, 8 * p521.combWords.length⟩] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ d.Disjoint scratch ∧
      (s.gpr .x0).toNat + 133 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [out, scratch]
  post s s' :=
    match pk s.mem (s.gpr .x1) with
    | some (.affine x y) => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 133 = encodePoint (.affine x y)
    | _ => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 133 = List.replicate 133 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp ∧ s₁.syms p521.tsym = s₂.syms p521.tsym

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x1, 66⟩, ⟨s.syms p521.tsym, 8 * p521.combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 133⟩, ⟨s.gpr .x2, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .x0, 133⟩ ⟨s.gpr .x1, 66⟩)
    (h2 : Region.Disjoint ⟨s.gpr .x0, 133⟩ ⟨s.gpr .x2, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x1, 66⟩ ⟨s.gpr .x2, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 133 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 66 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64) (ht : TblHeld s [⟨s.gpr .x0, 133⟩, ⟨s.gpr .x2, 8192⟩])
    (hal : (s.syms p521.tsym).toNat % 64 = 0) :
    (Spec.EcKey.P521.inst.publicKeyContract (AArch64.abi.withConsts p521.combConsts)).pre s := by
  sig_pre [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, AArch64.abi,
    AArch64.argRegs, p521_combConsts, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, hal, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1, f2⟩

/-- A state satisfying the precondition: the tables at `0x100000`. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x8000 | _ => 0
  sp := 0x20000
  mem := satMem
  rd := [⟨0x2000, 66⟩, ⟨0x100000, 764928⟩]
  wr := [⟨0x1000, 133⟩, ⟨0x8000, 8192⟩]
  syms _ := 0x100000

theorem sat_spec :
    (Spec.EcKey.P521.inst.publicKeyContract (AArch64.abi.withConsts p521.combConsts)).pre satState := by
  have hl := p521_combWords_length
  have held : ∀ i < p521.combWords.length, satState.mem.readW (satState.syms p521.tsym +
      BitVec.ofNat 64 (8 * i)) 64 = p521.combWords.getD i 0 := satMem_held
  refine spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) ⟨held, ?_, ?_⟩ (by decide)
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies : pkAArch64.Implies
    (Spec.EcKey.P521.inst.publicKeyContract (AArch64.abi.withConsts p521.combConsts)) where
  pre s h := by
    sig_pre [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, AArch64.abi,
      AArch64.argRegs, p521_combConsts, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, -, ht, hw, h1, h2, h3, h4, -, h5⟩ := h
    refine ⟨?_, hw, h2, h1, h3, h4, h5, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, AArch64.abi,
      AArch64.argRegs, p521_combConsts, Abi.withConsts, pkAArch64, pk]
    simp only [pkAArch64, pk, Spec.P521.curve] at h
    revert h
    generalize publicKey _ _ = q
    rcases q with _ | _ | ⟨x, y⟩ <;> exact id
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, AArch64.abi,
      AArch64.argRegs, p521_combConsts, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨h0, h1, h2, hsp, hsy⟩
  sat := ⟨satState, sat_spec⟩

end VG.Proof.EcKey.AArch64.P521

end

end

/-!
# P-521 public keys on AArch64: `Verified`

P-521 is a curve the proof supports (`p521_ok`, given the inversions' soundness `InvSounds`, and `Law` for its group
law, which the registration file supplies: `Proof.P521.law` and `invSound_of_toM`), so `publicKey_ok`
gives the contract's postcondition; `x19`–`x25` are restored, and no
instruction writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.EcKey.AArch64.P521

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.EcKey.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P521

theorem pre_of {s : State} (h : pkAArch64.pre s) : PkPre p521 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, held, fit, hdw⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, ⟨by rw [h1]; simp, held, fit, hdw _ (by simp)⟩⟩

theorem post_of {s s' : State} (h : PkPost p521 s s') : pkAArch64.post s s' := by
  unfold PkPost at h
  dsimp only [pkAArch64]
  revert h
  generalize hq : pk s.mem (s.gpr .x1) = q
  rw [show Spec.EcKey.publicKey p521.C (dk p521 s) = pk s.mem (s.gpr .x1) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

theorem pk_a64 (hL : Weierstrass.Law Spec.P521.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (s : State)
    (hs : pkAArch64.pre s) :
    ∃ t s', Exec isa publicKeyP521 s t s' ∧ abiPreserved s s' ∧ pkAArch64.post s s' := by
  -- In steps: elaborated in one term, the unifier would compare P-521's
  -- terms before the literals' facts are known.
  have hn : CallsKeep publicKeyP521 := by lit_decide
  have hu : KeepsUntouched publicKeyP521 := by lit_decide
  have hv : publicKeyP521.allInstrs keepsV = true := by lit_decide
  obtain ⟨t, s', he, hsv, hpost⟩ := publicKey_ok (p521_ok hI) hL hT (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he hn hu hv hsv, post_of hpost⟩

theorem pk_ct : ConstantTime isa pkAArch64.pre pkAArch64.pub publicKeyP521 :=
  VG.Taint.constantTime (A := taintS [p521.tsym]) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ ⟨h0, h1, h2, hsp, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

theorem pk_verified (hL : Weierstrass.Law Spec.P521.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) :
    Verified AArch64.target publicKeyP521
      (Spec.EcKey.P521.inst.publicKeyContract (AArch64.abi.withConsts p521.combConsts)) :=
  Verified.of_correct (pk_a64 hL hI hT) pk_ct implies

/-- `vg_ec_p521_public_key` as it is emitted, its cleanup included
(`Impl.EcKey.AArch64.Fn.publicKeyP521`), meets its contract in constant time and
returns without secret residue. -/
theorem pk_scrubbed (hL : Weierstrass.Law Spec.P521.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) :
    VerifiedScrubbed AArch64.target Impl.EcKey.AArch64.Fn.publicKeyP521
      (Spec.EcKey.P521.inst.publicKeyContract (AArch64.abi.withConsts p521.combConsts)) 32 :=
  AArch64.ScrubAll.verifiedScrubbed (api := Spec.EcKey.P521.publicKeyApi)
    { code := publicKeyP521, verified := pk_verified hL hI hT } _
    (Proof.EcKey.AArch64.Scrub.publicKeyOk_consts _ _ _) (by dsimp only; lit_decide)

end VG.Proof.EcKey.AArch64.P521
