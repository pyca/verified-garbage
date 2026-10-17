module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Sat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha256
public import VerifiedGarbage.Proof.Ecdsa.X86.CombSat
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve
public import VerifiedGarbage.Proof.Ecdsa.X86.CombVerified
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombVerified
import VerifiedGarbage.Proof.Ecdsa.X86.Lit
meta import VerifiedGarbage.Proof.Ecdsa.X86.Lit
public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.X25519.X86.Column
meta import Mathlib.Data.Finset.Card
meta import Mathlib.Data.Nat.Find
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.X25519.X86.Column

/-!
# Deterministic ECDSA on x86 (32-bit): P-256

P-256 as the proof's curve (`p256`): scalars of 4 64-bit words, the order
`n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_p256_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at P-256's sizes). Its seven-bit comb reads the same immutable
table as public-key generation and verification, using four bytes of stack
for position-independent addressing, within the 20 its calls use.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86

theorem p256_nBits : Spec.Ecdsa.nBits Spec.P256.curve = 256 := by
  show Spec.P256.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.P256.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P256.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

open VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86

private theorem core_pre_256 {s : State} (h : (coreK p256Comb).pre s) : CombSignPre p256Comb s := by
  obtain ⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss, ds, gs, ks,
    ht⟩ := h
  exact ⟨⟨rd, wr, oc, od, og, ok, dc, gc, kc, ao, ac, ro, rc, no, nd, ng, nk, nc, sp, lo, so, ss⟩, ht, ds, gs, ks⟩

private theorem core_pub_256 {s t : State} (h : (coreK p256Comb).pub s t) : CombSignPub s t := by
  obtain ⟨he, a0, a1, a2, a3, a4, sy⟩ := h
  refine ⟨he, ?_, sy ("VG_P256_COMB", p256W) (by rw [p256Comb_consts]; simp)⟩
  intro j hj
  match j, hj with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4

/-- P-256, with the group law `hL`. -/
def p256 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) : RfcCurve where
  E := p256Comb
  inst := Spec.Ecdsa.P256.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inl rfl), .inl rfl, p256_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 32 - Spec.Ecdsa.nBits Spec.P256.curve = 0; rw [p256_nBits]
  coreN := Spec.Ecdsa.P256.signApi.name
  coreC := signP256Comb
  coreX := by
    intro s h
    have co : ∀ d, p256Comb.comb = some d → CombOk p256Comb d := by
      intro d hd
      have he : p256d = d := Option.some.inj hd
      rw [← he]; exact p256Comb_shape
    obtain ⟨tr, t, he, ha, hp⟩ := signComb_ok (p256Comb_ok hI) hL (p256Comb_tables hL) co p256Comb_am3 rfl signComb_spG
      signComb_spTail (core_pre_256 h)
    refine ⟨tr, t, he, ha, ?_⟩
    simp only [coreK, coreSigOf, SignPost, ptr, BitVec.setWidth_append_eq_right] at hp ⊢
    generalize Spec.Ecdsa.signWith p256Comb.C
      (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem ((arg s 1).setWidth 64) p256Comb.C.len))
      (Spec.Ecdsa.hashToInt p256Comb.C (Spec.Ecdsa.bytesAt s.mem ((arg s 2).setWidth 64) p256Comb.C.len))
      (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem ((arg s 3).setWidth 64) p256Comb.C.len)) = r at hp ⊢
    cases r <;> exact hp
  coreCT := by
    intro s t tr₁ tr₂ s' t' hs ht hp
    exact signComb_ct (p256Comb_ok hI) hL (p256Comb_tables hL) p256Comb_shape p256Comb_am3 signComb_spMul
      s t tr₁ tr₂ s' t' (core_pre_256 hs) (core_pre_256 ht) (core_pub_256 hp)
  coreNs := NoSp.of_all (by lit_decide)
  coreStack := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)

/-- The arguments' bytes miss the comb's tables. -/
theorem anyMem_comb (a : Addr) (h : 0x100000 ≤ a.toNat) : anyMem combSatMem a = combSatMem a := by
  have ne : ∀ c : Addr, c.toNat < 0x100000 → (a = c) = False := fun c hc => eq_false fun e => by subst e; omega
  have hs : ((a - 0x20004).toNat < 24) = False := by
    refine eq_false fun h' => ?_
    rw [BitVec.toNat_sub, show (131076 : Addr).toNat = 131076 from rfl] at h'
    have := a.isLt
    omega
  unfold anyMem
  simp only [ne 0x20005 (by decide), ne 0x20009 (by decide), ne 0x2000d (by decide), ne 0x20010 (by decide),
    ne 0x20015 (by decide), ne 0x20018 (by decide), hs, ite_false]

/-- The state, with P-256's comb tables. -/
abbrev combAny : State := anySat combSatMem (fun _ => 0x100000) 32 [⟨0x100000, 151552⟩]

/-- A state with P-256's comb tables that satisfies the shared contract. -/
theorem sat_comb (I₀ : Spec.Ecdsa.Rfc6979.Instance) (hE : I₀.ecdsa = Spec.Ecdsa.P256.inst)
    (hS : I₀.scratchWords = 1024) :
    ∃ s, (I₀.signAnyContract (X86.abi.withConsts p256Comb.combConsts) 536).pre s := by
  refine ⟨combAny, ?_⟩
  have ha := anySat_args combSatMem (fun _ => 0x100000) 32 [⟨0x100000, 151552⟩]
  have a0 : arg combAny 0 = 0x1000 := ha.1
  have a1 : arg combAny 1 = 0x2000 := ha.2.1
  have a2 : arg combAny 2 = 0x3000 := ha.2.2.1
  have a3 : arg combAny 3 = 32 := ha.2.2.2.1
  have a4 : arg combAny 4 = 0x8000 := ha.2.2.2.2.1
  have a5 : arg combAny 5 = 3 := ha.2.2.2.2.2
  clear ha
  have aa : argAddr combAny 0 = 0x20004 := rfl
  have esp : combAny.gpr .esp = 0x20000 := rfl
  have sy : combAny.syms "VG_P256_COMB" = 0x100000 := rfl
  have held : ∀ i < p256W.length, combAny.mem.readW
      ((combAny.syms "VG_P256_COMB").setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = p256W.getD i 0 := by
    intro i hi
    rw [← combSatMem_held i hi, sy, show BitVec.setWidth 64 (0x100000 : BitVec 32) = 0x100000 by decide]
    apply Mem.readW_congr
    intro j hj
    apply anyMem_comb
    have hl := p256W_length
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (0x100000 : Addr).toNat = 0x100000 from rfl]
    omega
  have hrd : combAny.rd = [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x100000, 151552⟩] := rfl
  have hwr : combAny.wr = [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩, ⟨0x20004, 24⟩] := rfl
  generalize combAny = s at a0 a1 a2 a3 a4 a5 aa esp sy held hrd hwr ⊢
  sig_pre [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig, hE, hS,
    Spec.Ecdsa.P256.inst, Spec.P256.curve, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, p256Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  simp only [a0, a1, a2, a3, a4, a5, aa, esp, sy, hrd, hwr, hE, hS, Spec.Ecdsa.P256.inst, Spec.P256.curve]
  rw [sy] at held
  simp only [p256W_length] at held ⊢
  repeat' apply And.intro
  all_goals first
    | exact held
    | decide
    | rfl
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))
    | (intro H h; simp only [Spec.HashId.mgf1] at h; cases h; rfl)


/-- `vg_ecdsa_p256_rfc6979_sign`, with the hash functions of the tier `t`,
meets the shared contract. -/
theorem p256_any (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds)
    (t : Proof.Pbkdf2.Whole.X86.Tier) :
    Verified X86.target (cfgAny (p256 hL hI) t.fns Spec.Ecdsa.Rfc6979.P256Sha256.inst).sign
      (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signAnyContract (X86.abi.withConsts (p256 hL hI).E.combConsts) 536) :=
  sign_verified _ _ rfl (by decide) (by decide) rfl t (sat_comb _ rfl rfl)

/-- No instruction of `vg_ecdsa_p256_rfc6979_sign` writes `esp` but the frames'. -/
theorem p256_spSafe (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) (t : Proof.Pbkdf2.Whole.X86.Tier) :
    (cfgAny (p256 hL hI) t.fns Spec.Ecdsa.Rfc6979.P256Sha256.inst).sign.all (fun i => !isa.writesSp i) = true :=
  any_spSafe _ _ rfl (by decide) (by decide) t

end VG.Proof.Ecdsa.Rfc6979.X86
