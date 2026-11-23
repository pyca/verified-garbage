module

public import VerifiedGarbage.Impl.MlKem.X86.Wipe
public import VerifiedGarbage.Proof.Framework.X86.CallWipe
public import VerifiedGarbage.Proof.Zeroize.X86
public import VerifiedGarbage.Proof.MlKem.Scrubbed
public import VerifiedGarbage.Proof.MlKem.X86.KeyGenBody
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.MlKem.Bits
public import VerifiedGarbage.Spec.MlKem.Contract
public import VerifiedGarbage.Impl.MlKem.X86.CheckEk
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Framework.X86.Mmx
public import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.MlKem.X86.NttSetup
public import VerifiedGarbage.Proof.MlKem.X86.Red
public import VerifiedGarbage.Proof.MlKem.X86.Table
public import VerifiedGarbage.Proof.MlKem.X86.TopCall
public import VerifiedGarbage.Proof.MlKem.X86.TopLocal
public import VerifiedGarbage.Proof.MlKem.X86.TopKem
public import VerifiedGarbage.Proof.MlKem.X86.TopSeq
public import VerifiedGarbage.Proof.Sha512.Spec
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.X86.EncapsBody
import VerifiedGarbage.Proof.MlKem.X86.EncInst
public import VerifiedGarbage.Spec.MlKem.EncapsH
import VerifiedGarbage.Proof.MlKem.EncapsHSat
public import VerifiedGarbage.Proof.MlKem.X86.DecapsBody
public import VerifiedGarbage.Impl.MlKem1024.X86.Kem
public import VerifiedGarbage.Spec.MlKem.Contract1024
import VerifiedGarbage.Proof.MlKem1024.X86.Kem

/-! ### `MlKem.X86.KeyGen`, which only this module used -/

section

/-!
# ML-KEM-768 on x86 (32-bit): `vg_mlkem768_keygen`

Key generation (`KeyGenBody.lean`) for ML-KEM-768 (`L768`): the facts of its
layout (`GOK`, `PrfOK`, `KgRowOK`, `FinOK`), computed from its offsets; the
contract's precondition implies `TPre (Y L768)` (`pre_of`) and its public data
`TPub`, which includes `ρ` (`pub_of`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

instance : GOK L768 where
  rs := by decide
  g := by decide

instance : PrfOK L768 where
  sig := by decide
  nb := by decide
  hash := by decide
  prf := by decide

instance : KgRowOK L768 where
  seed := by decide
  nb := by decide
  samp := by decide
  mask := by decide
  mul := by decide
  mul0 := by decide
  mulJ := by decide
  row := by decide

instance : FinOK L768 where
  fin := by decide
  enc := by decide
  ek := by decide
  rho := by decide
  cp := by decide
  hh := by decide
  zk := by decide
  acc := by decide

theorem pre_of {s₀ : State} (h : (Proof.MlKem.Scrubbed.keyGenBodyContract X86.abi 88).pre s₀) : TPre (Y L768) s₀ := by
  sig_pre [Proof.MlKem.Scrubbed.keyGenBodyContract, keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 88#64, 88⟩ : Region) = below (E0 s₀) 88 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h20 h21 h22 h23 h24
  have c4 : ∀ i, i < (Y L768).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by
    simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi; omega_using [hi]
  refine ⟨h1, by decide, by simp only [Y, Lay.n, List.length_cons, List.length_nil]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h24, ?_, by decide⟩
  · intro i hi hw
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · rw [h3]; exact List.mem_singleton_self _
    all_goals exact absurd hw (by decide)
  · intro i hi hw
    rw [h4]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact absurd hw (by decide)
    all_goals simp [argR, Lay.alen, Y, L768, Params.ekLen, Params.dkLen, mlKem768]
  · rw [h4]; simp [gR, Lay.n, Y]
  · intro i hi j hj hne _
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> rcases c4 j hj with rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, h5, h6, h7, h5.symm, absurd rfl hne, h9, h10, h6.symm, h9.symm, absurd rfl hne, h12,
      h7.symm, h10.symm, h12.symm, absurd rfl hne]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact h8.symm
    · exact h11.symm
    · exact h13.symm
    · exact h14.symm
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact h15
    · exact h16
    · exact h17
    · exact h18
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact h20
    · exact h21
    · exact h22
    · exact h23
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact h25
    · exact h26
    · exact h27
    · exact h28

theorem pub_of {s₀ s₀' : State} (h : (Proof.MlKem.Scrubbed.keyGenBodyContract X86.abi 88).pub s₀ s₀') : TPub (Y L768) (lk L768) s₀ s₀' := by
  sig_pub [Proof.MlKem.Scrubbed.keyGenBodyContract, keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega_using [hi]
    exacts [e₃, e₄, e₅, e₆]
  · simp only [lk, d, addr0]
    exact map_toNat_inj e₂

/-- Memory with the arguments `0`, `0x100`, `0x1000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 1 else if a = 0x500d then 0x10 else if a = 0x5012 then 1 else 0

theorem verified : Verified X86.target Impl.MlKem.X86.keyGen (Proof.MlKem.Scrubbed.keyGenBodyContract X86.abi 88) := by
  refine Piece.verified (((piece (L := L768) (NoSp.of_all (by lit_decide))).pre_mono (fun _ h => pre_of h) fun _ _ _ _ h => pub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · have hp := pre_of h₀
    obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Proof.MlKem.Scrubbed.keyGenBodyContract, keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, argKeep hp hm (k := 1) (l := 1184) (by decide), argKeep hp hm (k := 2) (l := 2400) (by decide)]
    have r := post (by decide) hp hfin
    have ez : Buf.addr s₀ ⟨0, 32, 32⟩ = (arg s₀ 0).setWidth 64 + 32 := Buf.addr_eq hp (by decide)
    simp only [d, z, addr0, ez, show Buf.addr s₀ ⟨1, 0, L768.p.ekLen⟩ = (arg s₀ 1).setWidth 64 from addr0 s₀ 1,
      show Buf.addr s₀ ⟨2, 0, L768.p.dkLen⟩ = (arg s₀ 2).setWidth 64 from addr0 s₀ 2] at r
    exact r
  · let st := satState satMem [⟨0, 64⟩]
      [⟨0x100, 1184⟩, ⟨0x1000, 2400⟩, ⟨0x10000, 32768⟩, ⟨0x5004, 16⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Proof.MlKem.Scrubbed.keyGenBodyContract, keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

end VG.Proof.MlKem.X86.KeyGen

end

end

/-! ### `MlKem.X86.Encaps`, which only this module used -/

section

/-!
# ML-KEM-768 on x86 (32-bit): `vg_mlkem768_encaps`

Encapsulation (`EncapsBody.lean`) for ML-KEM-768 (`L768`): the facts of its
layout (`EncapsOK`), computed from its offsets; the contract's precondition
implies `TPre (Y L768)` (`pre_of`) and its public data `TPub` (`pub_of`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.Encaps

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

instance : EncapsOK L768 where
  ekc := by decide
  mc := by decide
  ek4 := by decide
  ct4 := by decide
  aEM := by decide
  hh := by decide
  aH := by decide
  g := by decide
  aG := by decide
  key := by decide
  ct := by decide
  dKey := by simp only [Enc.safe, Enc.safeS]; decide
  dCt := by simp only [Enc.safe, Enc.safeS]; decide
  acc := by simp only [Enc.safe, Enc.safeS]; decide

theorem pre_of {s₀ : State} (h : (Proof.MlKem.Scrubbed.encapsBodyContract X86.abi 88).pre s₀) : TPre (Y L768) s₀ := by
  sig_pre [Proof.MlKem.Scrubbed.encapsBodyContract, encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, -, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 88#64, 88⟩ : Region) = below (E0 s₀) 88 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h25 h26 h27 h28 h29 h30
  have c5 : ∀ i, i < (Y L768).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := fun i hi => by
    simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi; omega_using [hi]
  refine ⟨h1, by decide, by simp only [Y, Lay.n, List.length_cons, List.length_nil]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h30, ?_, by decide⟩
  · intro i hi hw
    rw [h3]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    all_goals exact absurd hw (by decide)
  · intro i hi hw
    rw [h4]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
    all_goals simp [argR, Lay.alen, Y, L768, Params.ekLen, Params.ctLen, mlKem768]
  · rw [h4]; simp [gR, Lay.n, Y]
  · intro i hi j hj hne hw
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl <;> rcases c5 j hj with rfl | rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, absurd hw (by decide), h5, h6, h7,
      absurd hw (by decide), absurd rfl hne, h9, h10, h11,
      h5.symm, h9.symm, absurd rfl hne, h13, h14,
      h6.symm, h10.symm, h13.symm, absurd rfl hne, h16,
      h7.symm, h11.symm, h14.symm, h16.symm, absurd rfl hne]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h8.symm, h12.symm, h15.symm, h17.symm, h18.symm]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h19, h20, h21, h22, h23]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h25, h26, h27, h28, h29]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h31, h32, h33, h34, h35]

theorem pub_of {s₀ s₀' : State} (h : (Proof.MlKem.Scrubbed.encapsBodyContract X86.abi 88).pub s₀ s₀') : TPub (Y L768) (lk L768) s₀ s₀' := by
  sig_pub [Proof.MlKem.Scrubbed.encapsBodyContract, encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega_using [hi]
    exacts [e₃, e₄, e₅, e₆, e₇]
  · have e := map_toNat_inj e₂
    show ekRho L768.p (ek L768 s₀) = ekRho L768.p (ek L768 s₀')
    rw [ek_eq, ek_eq, addr0, addr0]
    exact e

/-- Memory with the arguments `0`, `0x800`, `0x1000`, `0x2000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5009 then 0x08 else if a = 0x500d then 0x10 else if a = 0x5011 then 0x20 else if a = 0x5016 then 1
  else 0

theorem verified : Verified X86.target Impl.MlKem.X86.encaps (Proof.MlKem.Scrubbed.encapsBodyContract X86.abi 88) := by
  refine Piece.verified (((piece (L := L768) (by decide) (NoSp.of_all (by lit_decide))).pre_mono (fun _ h => pre_of h) fun _ _ _ _ h => pub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Proof.MlKem.Scrubbed.encapsBodyContract, encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, argKeep (pre_of h₀) hm (k := 2) (l := 32) (by decide), argKeep (pre_of h₀) hm (k := 3) (l := 1088) (by decide)]
    have r := post (by decide) hfin
    rw [ek_eq, msg_eq, addr0, addr0, addr0, addr0] at r
    exact r
  · let st := satState satMem [⟨0, 1184⟩, ⟨0x800, 32⟩]
      [⟨0x1000, 32⟩, ⟨0x2000, 1088⟩, ⟨0x10000, 32768⟩, ⟨0x5004, 20⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Proof.MlKem.Scrubbed.encapsBodyContract, encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]


/-! ## `vg_mlkem768_encaps_h` -/

instance : EncapsHOK L768 where
  ekc := by decide
  mc := by decide
  hc := by decide
  ek4 := by decide
  ct4 := by decide
  aEM := by decide
  aH := by decide
  g := by decide
  aG := by decide
  key := by decide
  ct := by decide
  dKey := by simp only [Enc.safe, Enc.safeS]; decide
  dCt := by simp only [Enc.safe, Enc.safeS]; decide
  acc := by simp only [Enc.safe, Enc.safeS]; decide

theorem pre_ofH {s₀ : State} (h : (Proof.MlKem.Scrubbed.encapsHBodyContract X86.abi 88).pre s₀) :
    TPre (YH L768) s₀ ∧ hv s₀ = H (ek L768 s₀) := by
  sig_pre [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, -, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42,
    h43⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 88#64, 88⟩ : Region) = below (E0 s₀) 88 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h30 h31 h32 h33 h34 h35 h36
  have c6 : ∀ i, i < (YH L768).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := fun i hi => by
    simp only [YH, Lay.n, List.length_cons, List.length_nil] at hi; omega_using [hi]
  refine ⟨⟨h1, by decide, by simp only [YH, Lay.n, List.length_cons, List.length_nil]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h36, ?_, by decide⟩, by rw [hv_eq, ek_eq, addr0, addr0]; exact h43⟩
  · intro i hi hw
    rw [h3]
    rcases c6 i hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact .head _
    · exact .tail _ (.head _)
    · exact .tail _ (.tail _ (.head _))
    all_goals exact absurd hw (by decide)
  · intro i hi hw
    rw [h4]
    rcases c6 i hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
    all_goals simp [argR, Lay.alen, YH, L768, Params.ekLen, Params.ctLen, mlKem768]
  · rw [h4]; simp [gR, Lay.n, YH]
  · intro i hi j hj hne hw
    rcases c6 i hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases c6 j hj with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, absurd hw (by decide), absurd hw (by decide), h5, h6, h7,
      absurd hw (by decide), absurd rfl hne, absurd hw (by decide), h9, h10, h11,
      absurd hw (by decide), absurd hw (by decide), absurd rfl hne, h13, h14, h15,
      h5.symm, h9.symm, h13.symm, absurd rfl hne, h17, h18,
      h6.symm, h10.symm, h14.symm, h17.symm, absurd rfl hne, h20,
      h7.symm, h11.symm, h15.symm, h18.symm, h20.symm, absurd rfl hne]
  · intro i hi
    rcases c6 i hi with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h8.symm, h12.symm, h16.symm, h19.symm, h21.symm, h22.symm]
  · intro i hi
    rcases c6 i hi with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h23, h24, h25, h26, h27, h28]
  · intro i hi
    rcases c6 i hi with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h30, h31, h32, h33, h34, h35]
  · intro i hi
    rcases c6 i hi with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h37, h38, h39, h40, h41, h42]

theorem pub_ofH {s₀ s₀' : State} (h : (Proof.MlKem.Scrubbed.encapsHBodyContract X86.abi 88).pub s₀ s₀') :
    TPub (YH L768) (lk L768) s₀ s₀' := by
  sig_pub [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · simp only [YH, Lay.n, List.length_cons, List.length_nil] at hi
    obtain rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega_using [hi]
    exacts [e₃, e₄, e₅, e₆, e₇, e₈]
  · have e := map_toNat_inj e₂
    show ekRho L768.p (ek L768 s₀) = ekRho L768.p (ek L768 s₀')
    rw [ek_eq, ek_eq, addr0, addr0]
    exact e

/-- A state satisfying `encapsH`'s precondition. -/
def satStH : State := satState (satMemH 1184) [⟨0x1000, 1184⟩, ⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  [⟨0x4000, 32⟩, ⟨0x6000, 1088⟩, ⟨0x10000, 32768⟩, ⟨0x5004, 24⟩]

theorem satStH_ek : BitVec.setWidth 64 (arg satStH 0) = 0x1000 := by decide +kernel
theorem satStH_h : BitVec.setWidth 64 (arg satStH 1) = 0x2000 := by decide +kernel

theorem verifiedH : Verified X86.target Impl.MlKem.X86.encapsH (Proof.MlKem.Scrubbed.encapsHBodyContract X86.abi 88) := by
  refine Piece.verified (((pieceH (L := L768) (by decide) (NoSp.of_all (by lit_decide))).pre_mono
    (fun _ h => (pre_ofH h).1) fun _ _ _ _ h => pub_ofH h).mono (fun _ _ _ h => h) fun s₀ s' hpre hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, argKeep (pre_ofH hpre).1 hm (k := 3) (l := 32) (by decide), argKeep (pre_ofH hpre).1 hm (k := 4) (l := 1088) (by decide)]
    have r := postH (by decide) (pre_ofH hpre).2 hfin
    rw [ek_eq, msgH_eq, addr0, addr0, addr0, addr0] at r
    exact r
  · refine ⟨satStH, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes]
      sig_and_intros
      all_goals first
        | (fail_if_success show bytesAt _ _ _ = _
           decide +kernel)
        | (rw [satStH_ek, satStH_h]
           exact VG.Proof.MlKem.hMem_h_of (by decide) satMemH_low)

end VG.Proof.MlKem.X86.Encaps

end

end

/-! ### `MlKem.X86.Decaps`, which only this module used -/

section

/-!
# ML-KEM-768 on x86 (32-bit): `vg_mlkem768_decaps`

Decapsulation (`DecapsBody.lean`) for ML-KEM-768 (`L768`): the facts of its
layout (`DecOK`, `CmpOK`, `DecapsOK`), computed from its offsets; the
contract's precondition implies `TPre (Y L768)` (`pre_of`) and its public data
`TPub` (`pub_of`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.Decaps

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

instance : DecOK L768 where
  ct := by decide
  dec := by decide
  keep := by decide
  mul := by decide
  v := by decide

instance : CmpOK L768 where
  ct := by decide
  sel := by decide

instance : DecapsOK L768 where
  ekc := by decide
  ek4 := by decide
  aEM := by decide
  g := by decide
  aG := by decide
  j := by decide
  dJ := by simp only [Enc.safe, Enc.safeS]; decide
  dNil := by simp only [Enc.safe, Enc.safeS]; decide
  dKey := by simp only [Enc.safe, Enc.safeS]; decide
  acc := by decide

theorem pre_of {s₀ : State} (h : (Proof.MlKem.Scrubbed.decapsBodyContract X86.abi 88).pre s₀) : TPre (Y L768) s₀ := by
  sig_pre [Proof.MlKem.Scrubbed.decapsBodyContract, decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, -, h19, h20, h21, h22, h23,
    h24, h25, h26, h27⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 88#64, 88⟩ : Region) = below (E0 s₀) 88 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h19 h20 h21 h22 h23
  have c4 : ∀ i, i < (Y L768).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by
    simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi; omega_using [hi]
  refine ⟨h1, by decide, by simp only [Y, Lay.n, List.length_cons, List.length_nil]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h23, ?_, by decide⟩
  · intro i hi hw
    rw [h3]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    all_goals exact absurd hw (by decide)
  · intro i hi hw
    rw [h4]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
    all_goals simp [argR, Lay.alen, Y, L768, Params.dkLen, Params.ctLen, mlKem768]
  · rw [h4]; simp [gR, Lay.n, Y]
  · intro i hi j hj hne hw
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> rcases c4 j hj with rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, absurd hw (by decide), h5, h6,
      absurd hw (by decide), absurd rfl hne, h8, h9,
      h5.symm, h8.symm, absurd rfl hne, h11,
      h6.symm, h9.symm, h11.symm, absurd rfl hne]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    exacts [h7.symm, h10.symm, h12.symm, h13.symm]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    exacts [h14, h15, h16, h17]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    exacts [h19, h20, h21, h22]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    exacts [h24, h25, h26, h27]

theorem pub_of {s₀ s₀' : State} (h : (Proof.MlKem.Scrubbed.decapsBodyContract X86.abi 88).pub s₀ s₀') : TPub (Y L768) (lk L768) s₀ s₀' := by
  sig_pub [Proof.MlKem.Scrubbed.decapsBodyContract, decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega_using [hi]
    exacts [e₃, e₄, e₅, e₆]
  · have e := map_toNat_inj e₂
    show dkRho L768.p (dk L768 s₀) = dkRho L768.p (dk L768 s₀')
    rw [dk_eq, dk_eq, addr0, addr0]
    exact e

/-- Memory with the arguments `0`, `0x1000`, `0x2000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5009 then 0x10 else if a = 0x500d then 0x20 else if a = 0x5012 then 1 else 0

theorem verified : Verified X86.target Impl.MlKem.X86.decaps (Proof.MlKem.Scrubbed.decapsBodyContract X86.abi 88) := by
  refine Piece.verified (((piece (L := L768) (by decide) (NoSp.of_all (by lit_decide))).pre_mono (fun _ h => pre_of h) fun _ _ _ _ h => pub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · have hp := pre_of h₀
    obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Proof.MlKem.Scrubbed.decapsBodyContract, decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, argKeep hp hm (k := 2) (l := 32) (by decide)]
    have r := post (by decide) hp hfin
    rw [dk_eq, ct_eq, addr0, addr0, addr0] at r
    exact r
  · let st := satState satMem [⟨0, 2400⟩, ⟨0x1000, 1088⟩]
      [⟨0x2000, 32⟩, ⟨0x10000, 32768⟩, ⟨0x5004, 16⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Proof.MlKem.Scrubbed.decapsBodyContract, decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

end VG.Proof.MlKem.X86.Decaps

end

end

/-! ### `MlKem1024.X86.KeyGen`, which only this module used -/

section

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_keygen`

Key generation (`Proof/MlKem/X86/KeyGenBody.lean`) for ML-KEM-1024
(`L1024`): the facts of its layout, computed from its offsets; the contract's
precondition implies `TPre (Y L1024)` (`pre_of`) and its public data `TPub`,
which includes `ρ` (`pub_of`).
-/

@[expose] public section

namespace VG.Proof.MlKem1024.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86.KeyGen

instance : GOK L1024 where
  rs := by decide
  g := by decide

instance : PrfOK L1024 where
  sig := by decide
  nb := by decide
  hash := by decide
  prf := by decide

instance : KgRowOK L1024 where
  seed := by decide
  nb := by decide
  samp := by decide
  mask := by decide
  mul := by decide
  mul0 := by decide
  mulJ := by decide
  row := by decide

instance : FinOK L1024 where
  fin := by decide
  enc := by decide
  ek := by decide
  rho := by decide
  cp := by decide
  hh := by decide
  zk := by decide
  acc := by decide

theorem pre_of {s₀ : State} (h : (Proof.MlKem.Scrubbed.keyGen1024BodyContract X86.abi 88).pre s₀) : TPre (Y L1024) s₀ := by
  sig_pre [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 88#64, 88⟩ : Region) = below (E0 s₀) 88 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h20 h21 h22 h23 h24
  have c4 : ∀ i, i < (Y L1024).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by
    simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi; omega_using [hi]
  refine ⟨h1, by decide, by simp only [Y, Lay.n, List.length_cons, List.length_nil]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h24, ?_, by decide⟩
  · intro i hi hw
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · rw [h3]; exact List.mem_singleton_self _
    all_goals exact absurd hw (by decide)
  · intro i hi hw
    rw [h4]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact absurd hw (by decide)
    all_goals simp [argR, Lay.alen, Y, L1024, Params.ekLen, Params.dkLen, mlKem1024]
  · rw [h4]; simp [gR, Lay.n, Y]
  · intro i hi j hj hne _
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> rcases c4 j hj with rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, h5, h6, h7, h5.symm, absurd rfl hne, h9, h10, h6.symm, h9.symm, absurd rfl hne, h12,
      h7.symm, h10.symm, h12.symm, absurd rfl hne]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact h8.symm
    · exact h11.symm
    · exact h13.symm
    · exact h14.symm
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact h15
    · exact h16
    · exact h17
    · exact h18
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact h20
    · exact h21
    · exact h22
    · exact h23
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact h25
    · exact h26
    · exact h27
    · exact h28

theorem pub_of {s₀ s₀' : State} (h : (Proof.MlKem.Scrubbed.keyGen1024BodyContract X86.abi 88).pub s₀ s₀') : TPub (Y L1024) (lk L1024) s₀ s₀' := by
  sig_pub [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega_using [hi]
    exacts [e₃, e₄, e₅, e₆]
  · simp only [lk, d, addr0]
    exact VG.Proof.MlKem.map_toNat_inj e₂

/-- Memory with the arguments `0`, `0x100`, `0x1000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 1 else if a = 0x500d then 0x10 else if a = 0x5012 then 1 else 0

theorem verified : Verified X86.target Impl.MlKem1024.X86.keyGen (Proof.MlKem.Scrubbed.keyGen1024BodyContract X86.abi 88) := by
  refine Piece.verified (((piece (L := L1024) (NoSp.of_all (by lit_decide))).pre_mono (fun _ h => pre_of h) fun _ _ _ _ h => pub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · have hp := pre_of h₀
    obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, argKeep hp hm (k := 1) (l := 1568) (by decide), argKeep hp hm (k := 2) (l := 3168) (by decide)]
    have r := post (by decide) hp hfin
    have ez : Buf.addr s₀ ⟨0, 32, 32⟩ = (arg s₀ 0).setWidth 64 + 32 := Buf.addr_eq hp (by decide)
    simp only [d, z, addr0, ez, show Buf.addr s₀ ⟨1, 0, L1024.p.ekLen⟩ = (arg s₀ 1).setWidth 64 from addr0 s₀ 1,
      show Buf.addr s₀ ⟨2, 0, L1024.p.dkLen⟩ = (arg s₀ 2).setWidth 64 from addr0 s₀ 2] at r
    exact r
  · let st := satState satMem [⟨0, 64⟩]
      [⟨0x100, 1568⟩, ⟨0x1000, 3168⟩, ⟨0x10000, 49152⟩, ⟨0x5004, 16⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]

end VG.Proof.MlKem1024.X86.KeyGen

end

end

/-! ### `MlKem1024.X86.Encaps`, which only this module used -/

section

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_encaps`

Encapsulation (`Proof/MlKem/X86/EncapsBody.lean`) for ML-KEM-1024 (`L1024`):
the facts of its layout, computed from its offsets; the contract's
precondition implies `TPre (Y L1024)` (`pre_of`) and its public data `TPub`
(`pub_of`).
-/

@[expose] public section

namespace VG.Proof.MlKem1024.X86.Encaps

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86.Encaps

instance : EncapsOK L1024 where
  ekc := by decide
  mc := by decide
  ek4 := by decide
  ct4 := by decide
  aEM := by decide
  hh := by decide
  aH := by decide
  g := by decide
  aG := by decide
  key := by decide
  ct := by decide
  dKey := by simp only [Enc.safe, Enc.safeS]; decide
  dCt := by simp only [Enc.safe, Enc.safeS]; decide
  acc := by simp only [Enc.safe, Enc.safeS]; decide

theorem pre_of {s₀ : State} (h : (Proof.MlKem.Scrubbed.encaps1024BodyContract X86.abi 88).pre s₀) : TPre (Y L1024) s₀ := by
  sig_pre [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, -, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 88#64, 88⟩ : Region) = below (E0 s₀) 88 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h25 h26 h27 h28 h29 h30
  have c5 : ∀ i, i < (Y L1024).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := fun i hi => by
    simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi; omega_using [hi]
  refine ⟨h1, by decide, by simp only [Y, Lay.n, List.length_cons, List.length_nil]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h30, ?_, by decide⟩
  · intro i hi hw
    rw [h3]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    all_goals exact absurd hw (by decide)
  · intro i hi hw
    rw [h4]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
    all_goals simp [argR, Lay.alen, Y, L1024, Params.ekLen, Params.ctLen, mlKem1024]
  · rw [h4]; simp [gR, Lay.n, Y]
  · intro i hi j hj hne hw
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl <;> rcases c5 j hj with rfl | rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, absurd hw (by decide), h5, h6, h7,
      absurd hw (by decide), absurd rfl hne, h9, h10, h11,
      h5.symm, h9.symm, absurd rfl hne, h13, h14,
      h6.symm, h10.symm, h13.symm, absurd rfl hne, h16,
      h7.symm, h11.symm, h14.symm, h16.symm, absurd rfl hne]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h8.symm, h12.symm, h15.symm, h17.symm, h18.symm]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h19, h20, h21, h22, h23]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h25, h26, h27, h28, h29]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h31, h32, h33, h34, h35]

theorem pub_of {s₀ s₀' : State} (h : (Proof.MlKem.Scrubbed.encaps1024BodyContract X86.abi 88).pub s₀ s₀') : TPub (Y L1024) (lk L1024) s₀ s₀' := by
  sig_pub [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega_using [hi]
    exacts [e₃, e₄, e₅, e₆, e₇]
  · have e := VG.Proof.MlKem.map_toNat_inj e₂
    show ekRho L1024.p (ek L1024 s₀) = ekRho L1024.p (ek L1024 s₀')
    rw [ek_eq, ek_eq, addr0, addr0]
    exact e

/-- Memory with the arguments `0`, `0x800`, `0x1000`, `0x2000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5009 then 0x08 else if a = 0x500d then 0x10 else if a = 0x5011 then 0x20 else if a = 0x5016 then 1
  else 0

theorem verified : Verified X86.target Impl.MlKem1024.X86.encaps (Proof.MlKem.Scrubbed.encaps1024BodyContract X86.abi 88) := by
  refine Piece.verified (((piece (L := L1024) (by decide) (NoSp.of_all (by lit_decide))).pre_mono (fun _ h => pre_of h) fun _ _ _ _ h => pub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, argKeep (pre_of h₀) hm (k := 2) (l := 32) (by decide), argKeep (pre_of h₀) hm (k := 3) (l := 1568) (by decide)]
    have r := post (by decide) hfin
    rw [ek_eq, msg_eq, addr0, addr0, addr0, addr0] at r
    exact r
  · let st := satState satMem [⟨0, 1568⟩, ⟨0x800, 32⟩]
      [⟨0x1000, 32⟩, ⟨0x2000, 1568⟩, ⟨0x10000, 49152⟩, ⟨0x5004, 20⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]

/-! ## `vg_mlkem1024_encaps_h` -/

instance : EncapsHOK L1024 where
  ekc := by decide
  mc := by decide
  hc := by decide
  ek4 := by decide
  ct4 := by decide
  aEM := by decide
  aH := by decide
  g := by decide
  aG := by decide
  key := by decide
  ct := by decide
  dKey := by simp only [Enc.safe, Enc.safeS]; decide
  dCt := by simp only [Enc.safe, Enc.safeS]; decide
  acc := by simp only [Enc.safe, Enc.safeS]; decide

theorem pre_ofH {s₀ : State} (h : (Proof.MlKem.Scrubbed.encapsH1024BodyContract X86.abi 88).pre s₀) :
    TPre (YH L1024) s₀ ∧ hv s₀ = H (ek L1024 s₀) := by
  sig_pre [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, -, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42,
    h43⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 88#64, 88⟩ : Region) = below (E0 s₀) 88 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h30 h31 h32 h33 h34 h35 h36
  have c6 : ∀ i, i < (YH L1024).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := fun i hi => by
    simp only [YH, Lay.n, List.length_cons, List.length_nil] at hi; omega_using [hi]
  refine ⟨⟨h1, by decide, by simp only [YH, Lay.n, List.length_cons, List.length_nil]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h36, ?_, by decide⟩, by rw [hv_eq, ek_eq, addr0, addr0]; exact h43⟩
  · intro i hi hw
    rw [h3]
    rcases c6 i hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact .head _
    · exact .tail _ (.head _)
    · exact .tail _ (.tail _ (.head _))
    all_goals exact absurd hw (by decide)
  · intro i hi hw
    rw [h4]
    rcases c6 i hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
    all_goals simp [argR, Lay.alen, YH, L1024, Params.ekLen, Params.ctLen, mlKem1024]
  · rw [h4]; simp [gR, Lay.n, YH]
  · intro i hi j hj hne hw
    rcases c6 i hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases c6 j hj with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, absurd hw (by decide), absurd hw (by decide), h5, h6, h7,
      absurd hw (by decide), absurd rfl hne, absurd hw (by decide), h9, h10, h11,
      absurd hw (by decide), absurd hw (by decide), absurd rfl hne, h13, h14, h15,
      h5.symm, h9.symm, h13.symm, absurd rfl hne, h17, h18,
      h6.symm, h10.symm, h14.symm, h17.symm, absurd rfl hne, h20,
      h7.symm, h11.symm, h15.symm, h18.symm, h20.symm, absurd rfl hne]
  · intro i hi
    rcases c6 i hi with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h8.symm, h12.symm, h16.symm, h19.symm, h21.symm, h22.symm]
  · intro i hi
    rcases c6 i hi with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h23, h24, h25, h26, h27, h28]
  · intro i hi
    rcases c6 i hi with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h30, h31, h32, h33, h34, h35]
  · intro i hi
    rcases c6 i hi with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h37, h38, h39, h40, h41, h42]

theorem pub_ofH {s₀ s₀' : State} (h : (Proof.MlKem.Scrubbed.encapsH1024BodyContract X86.abi 88).pub s₀ s₀') :
    TPub (YH L1024) (lk L1024) s₀ s₀' := by
  sig_pub [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · simp only [YH, Lay.n, List.length_cons, List.length_nil] at hi
    obtain rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega_using [hi]
    exacts [e₃, e₄, e₅, e₆, e₇, e₈]
  · have e := map_toNat_inj e₂
    show ekRho L1024.p (ek L1024 s₀) = ekRho L1024.p (ek L1024 s₀')
    rw [ek_eq, ek_eq, addr0, addr0]
    exact e

/-- A state satisfying `encapsH`'s precondition. -/
def satStH1024 : State := satState (satMemH 1568) [⟨0x1000, 1568⟩, ⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  [⟨0x4000, 32⟩, ⟨0x6000, 1568⟩, ⟨0x10000, 49152⟩, ⟨0x5004, 24⟩]

theorem satStH1024_ek : BitVec.setWidth 64 (arg satStH1024 0) = 0x1000 := by decide +kernel
theorem satStH1024_h : BitVec.setWidth 64 (arg satStH1024 1) = 0x2000 := by decide +kernel

theorem verifiedH : Verified X86.target Impl.MlKem1024.X86.encapsH (Proof.MlKem.Scrubbed.encapsH1024BodyContract X86.abi 88) := by
  refine Piece.verified (((pieceH (L := L1024) (by decide) (NoSp.of_all (by lit_decide))).pre_mono
    (fun _ h => (pre_ofH h).1) fun _ _ _ _ h => pub_ofH h).mono (fun _ _ _ h => h) fun s₀ s' hpre hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, argKeep (pre_ofH hpre).1 hm (k := 3) (l := 32) (by decide), argKeep (pre_ofH hpre).1 hm (k := 4) (l := 1568) (by decide)]
    have r := postH (by decide) (pre_ofH hpre).2 hfin
    rw [ek_eq, msgH_eq, addr0, addr0, addr0, addr0] at r
    exact r
  · refine ⟨satStH1024, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes]
      sig_and_intros
      all_goals first
        | (fail_if_success show bytesAt _ _ _ = _
           decide +kernel)
        | (rw [satStH1024_ek, satStH1024_h]
           exact VG.Proof.MlKem.hMem_h_of (by decide) satMemH_low)

end VG.Proof.MlKem1024.X86.Encaps

end

end

/-! ### `MlKem1024.X86.Decaps`, which only this module used -/

section

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_decaps`

Decapsulation (`Proof/MlKem/X86/DecapsBody.lean`) for ML-KEM-1024 (`L1024`):
the facts of its layout, computed from its offsets; the contract's
precondition implies `TPre (Y L1024)` (`pre_of`) and its public data `TPub`
(`pub_of`).
-/

@[expose] public section

namespace VG.Proof.MlKem1024.X86.Decaps

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86.Decaps

instance : DecOK L1024 where
  ct := by decide
  dec := by decide
  keep := by decide
  mul := by decide
  v := by decide

instance : CmpOK L1024 where
  ct := by decide
  sel := by decide

instance : DecapsOK L1024 where
  ekc := by decide
  ek4 := by decide
  aEM := by decide
  g := by decide
  aG := by decide
  j := by decide
  dJ := by simp only [Enc.safe, Enc.safeS]; decide
  dNil := by simp only [Enc.safe, Enc.safeS]; decide
  dKey := by simp only [Enc.safe, Enc.safeS]; decide
  acc := by decide

theorem pre_of {s₀ : State} (h : (Proof.MlKem.Scrubbed.decaps1024BodyContract X86.abi 88).pre s₀) : TPre (Y L1024) s₀ := by
  sig_pre [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, -, h19, h20, h21, h22, h23,
    h24, h25, h26, h27⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 88#64, 88⟩ : Region) = below (E0 s₀) 88 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h19 h20 h21 h22 h23
  have c4 : ∀ i, i < (Y L1024).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by
    simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi; omega_using [hi]
  refine ⟨h1, by decide, by simp only [Y, Lay.n, List.length_cons, List.length_nil]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h23, ?_, by decide⟩
  · intro i hi hw
    rw [h3]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    all_goals exact absurd hw (by decide)
  · intro i hi hw
    rw [h4]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
    all_goals simp [argR, Lay.alen, Y, L1024, Params.dkLen, Params.ctLen, mlKem1024]
  · rw [h4]; simp [gR, Lay.n, Y]
  · intro i hi j hj hne hw
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> rcases c4 j hj with rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, absurd hw (by decide), h5, h6,
      absurd hw (by decide), absurd rfl hne, h8, h9,
      h5.symm, h8.symm, absurd rfl hne, h11,
      h6.symm, h9.symm, h11.symm, absurd rfl hne]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    exacts [h7.symm, h10.symm, h12.symm, h13.symm]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    exacts [h14, h15, h16, h17]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    exacts [h19, h20, h21, h22]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    exacts [h24, h25, h26, h27]

theorem pub_of {s₀ s₀' : State} (h : (Proof.MlKem.Scrubbed.decaps1024BodyContract X86.abi 88).pub s₀ s₀') : TPub (Y L1024) (lk L1024) s₀ s₀' := by
  sig_pub [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega_using [hi]
    exacts [e₃, e₄, e₅, e₆]
  · have e := VG.Proof.MlKem.map_toNat_inj e₂
    show dkRho L1024.p (dk L1024 s₀) = dkRho L1024.p (dk L1024 s₀')
    rw [dk_eq, dk_eq, addr0, addr0]
    exact e

/-- Memory with the arguments `0`, `0x1000`, `0x2000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5009 then 0x10 else if a = 0x500d then 0x20 else if a = 0x5012 then 1 else 0

theorem verified : Verified X86.target Impl.MlKem1024.X86.decaps (Proof.MlKem.Scrubbed.decaps1024BodyContract X86.abi 88) := by
  refine Piece.verified (((piece (L := L1024) (by decide) (NoSp.of_all (by lit_decide))).pre_mono (fun _ h => pre_of h) fun _ _ _ _ h => pub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · have hp := pre_of h₀
    obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, argKeep hp hm (k := 2) (l := 32) (by decide)]
    have r := post (by decide) hp hfin
    rw [dk_eq, ct_eq, addr0, addr0, addr0] at r
    exact r
  · let st := satState satMem [⟨0, 3168⟩, ⟨0x1000, 1568⟩]
      [⟨0x2000, 32⟩, ⟨0x10000, 49152⟩, ⟨0x5004, 16⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]

end VG.Proof.MlKem1024.X86.Decaps

end

end


/-!
# ML-KEM on x86 (32-bit): the functions that wipe their working space

Each of ML-KEM-768's and ML-KEM-1024's functions taking `scratch` is
`callWipe` (`Impl/CallWipe/X86.lean`) of its code, which gets all its
arguments on the stack, `scratch` the last: it copies them into its frame
for the call, then zeroes all of `scratch` with `vg_zeroize` once that code
returns. It is verified against the same contract (`Verified.callWipe'`) with
the frame and the return address more stack than the code's 88 bytes: 120
for key generation, encapsulation and decapsulation (a frame of 28 bytes,
padded: four or five arguments and the result), 136 for encapsulation with
`H(ek)` (44 bytes: six arguments and the result, padded); and with `scratch`
left scrubbed (`*_scrubbed`, the contracts of `Proof/MlKem/Scrubbed.lean`),
since every byte of it is zero (`Scrubbed.keyGen_wiped`, …). `*_verified` state them as the contracts of
`Spec/MlKem/`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.Wipe

open VG VG.X86 VG.Impl.CallWipe.X86

theorem zeroize_noSp : NoSp Impl.Zeroize.X86.zeroize := NoSp.of_all (by lit_decide)

theorem zeroize_stack : stackUse Impl.Zeroize.X86.zeroize ≤ 0 := by lit_decide

/-! ## What the contracts read of the memory -/

/-- Memories agreeing on the region of `k` bytes at `p` agree on the `n`
bytes at offset `o` within it. -/
theorem bytesAt_agree {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ a, Region.Contains ⟨p, k⟩ a 1 → m₁ a = m₂ a) (hk : k < 2 ^ 64) {o n : Nat} (hn : o + n ≤ k) :
    Spec.Sha3.bytesAt m₁ (p + BitVec.ofNat 64 o) n = Spec.Sha3.bytesAt m₂ (p + BitVec.ofNat 64 o) n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  rw [Offset.add_add]
  exact h _ (Offset.contains_base _ (by omega_using [hn, hi]) (by omega_using [hk, hn, hi]))

/-- `bytesAt_agree` at offset 0. -/
theorem bytesAt_agree0 {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ a, Region.Contains ⟨p, k⟩ a 1 → m₁ a = m₂ a) (hk : k < 2 ^ 64) {n : Nat} (hn : n ≤ k) :
    Spec.Sha3.bytesAt m₁ p n = Spec.Sha3.bytesAt m₂ p n := by
  have := bytesAt_agree h hk (o := 0) (n := n) (by omega_using [hn])
  rwa [show p + BitVec.ofNat 64 0 = p from BitVec.add_zero p] at this

theorem vs4 {vs : List (BitVec 64)} (h : vs.length = 4) : ∃ a b c d, vs = [a, b, c, d] :=
  match vs, h with | [a, b, c, d], _ => ⟨a, b, c, d, rfl⟩

theorem vs5 {vs : List (BitVec 64)} (h : vs.length = 5) : ∃ a b c d e, vs = [a, b, c, d, e] :=
  match vs, h with | [a, b, c, d, e], _ => ⟨a, b, c, d, e, rfl⟩

theorem vs6 {vs : List (BitVec 64)} (h : vs.length = 6) : ∃ a b c d e f, vs = [a, b, c, d, e, f] :=
  match vs, h with | [a, b, c, d, e, f], _ => ⟨a, b, c, d, e, f, rfl⟩

/-- Two buffers of a contract, one of them writable, lie apart. -/
theorem pw_disj {l : List (Region × Bool)} (h : l.Pairwise (fun a b => (a.2 || b.2) = true → a.1.Disjoint b.1))
    {i j : Nat} (hij : i < j) (hj : j < l.length) (hw : (l[i].2 || l[j].2) = true) : l[i].1.Disjoint l[j].1 :=
  List.pairwise_iff_getElem.mp h i j (by omega_using [hij, hj]) hj hij hw

/-! ## The functions, with any code verified against their contracts -/

/-- `vg_mlkem768_keygen`. -/
theorem keyGen_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.keyGenBodyContract abi 88))
    (hsp : NoSp body) (hd : stackUse body ≤ 88)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.keyGenBodyContract abi 120).pre s) :
    Verified target (Impl.MlKem.X86.Wipe.wiped 4 32768 "vg_mlkem768_keygen" body)
      (Scrubbed.keyGenContract abi 120) := by
  have e : slots Spec.MlKem.keyGenSig = 4 := by decide
  have h' := Verified.callWipe' (sig := Spec.MlKem.keyGenSig) (ps₁ := Spec.MlKem.keyGenSig.params.dropLast) (ps₂ := [])
    (i := 3) (j := 3) (n := 32768) (name := "vg_mlkem768_keygen_body") (zname := "vg_zeroize_core") h Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) hsp hd zeroize_noSp zeroize_stack
    (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide),
        show a + 32 = a + BitVec.ofNat 64 32 from rfl,
        ← bytesAt_agree hb.1 (by decide) (o := 32) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.1 (pw_disj hpw (i := 1) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1184) (by decide),
        ← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 2400) (by decide)]
      exact h)
    (Scrubbed.keyGen_wiped _)
    (by rw [e, show 88 + frameSize 4 + 4 = 120 by decide]; exact hsat)
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide)])
  rw [e, show 88 + frameSize 4 + 4 = 120 by decide] at h'
  exact h'

/-- `vg_mlkem768_encaps_h`. -/
theorem encapsH_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsHBodyContract abi 88))
    (hsp : NoSp body) (hd : stackUse body ≤ 88)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsHBodyContract abi 136).pre s) :
    Verified target (Impl.MlKem.X86.Wipe.wiped 6 32768 "vg_mlkem768_encaps_h" body)
      (Scrubbed.encapsHContract abi 136) := by
  have e : slots Spec.MlKem.encapsHSig = 6 := by decide
  have h' := Verified.callWipe' (sig := Spec.MlKem.encapsHSig) (ps₁ := Spec.MlKem.encapsHSig.params.dropLast) (ps₂ := [])
    (i := 5) (j := 5) (n := 32768) (name := "vg_mlkem768_encaps_h_body") (zname := "vg_zeroize_core") h Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) hsp hd zeroize_noSp zeroize_stack
    (Nat.zero_le _)
    (by
      intro vs m₁ m₂ hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ at h
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide),
        ← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)]
      exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide),
        ← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.2.1 (pw_disj hpw (i := 4) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1088) (by decide)]
      exact h)
    (Scrubbed.encapsH_wiped _)
    (by rw [e, show 88 + frameSize 6 + 4 = 136 by decide]; exact hsat)
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)])
  rw [e, show 88 + frameSize 6 + 4 = 136 by decide] at h'
  exact h'

/-- `vg_mlkem768_encaps`. -/
theorem encaps_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsBodyContract abi 88))
    (hsp : NoSp body) (hd : stackUse body ≤ 88)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsBodyContract abi 120).pre s) :
    Verified target (Impl.MlKem.X86.Wipe.wiped 5 32768 "vg_mlkem768_encaps" body)
      (Scrubbed.encapsContract abi 120) := by
  have e : slots Spec.MlKem.encapsSig = 5 := by decide
  have h' := Verified.callWipe' (sig := Spec.MlKem.encapsSig) (ps₁ := Spec.MlKem.encapsSig.params.dropLast) (ps₂ := [])
    (i := 4) (j := 4) (n := 32768) (name := "vg_mlkem768_encaps_body") (zname := "vg_zeroize_core") h Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) hsp hd zeroize_noSp zeroize_stack
    (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1088) (by decide)]
      exact h)
    (Scrubbed.encaps_wiped _)
    (by rw [e, show 88 + frameSize 5 + 4 = 120 by decide]; exact hsat)
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1184) (by decide)])
  rw [e, show 88 + frameSize 5 + 4 = 120 by decide] at h'
  exact h'

/-- `vg_mlkem768_decaps`. -/
theorem decaps_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.decapsBodyContract abi 88))
    (hsp : NoSp body) (hd : stackUse body ≤ 88)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.decapsBodyContract abi 120).pre s) :
    Verified target (Impl.MlKem.X86.Wipe.wiped 4 32768 "vg_mlkem768_decaps" body)
      (Scrubbed.decapsContract abi 120) := by
  have e : slots Spec.MlKem.decapsSig = 4 := by decide
  have h' := Verified.callWipe' (sig := Spec.MlKem.decapsSig) (ps₁ := Spec.MlKem.decapsSig.params.dropLast) (ps₂ := [])
    (i := 3) (j := 3) (n := 32768) (name := "vg_mlkem768_decaps_body") (zname := "vg_zeroize_core") h Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) hsp hd zeroize_noSp zeroize_stack
    (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 2400) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 1088) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide)]
      exact h)
    (Scrubbed.decaps_wiped _)
    (by rw [e, show 88 + frameSize 4 + 4 = 120 by decide]; exact hsat)
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 2400) (by decide)])
  rw [e, show 88 + frameSize 4 + 4 = 120 by decide] at h'
  exact h'

/-- `vg_mlkem1024_keygen`. -/
theorem keyGen1024_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi 88))
    (hsp : NoSp body) (hd : stackUse body ≤ 88)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi 120).pre s) :
    Verified target (Impl.MlKem.X86.Wipe.wiped 4 49152 "vg_mlkem1024_keygen" body)
      (Scrubbed.keyGen1024Contract abi 120) := by
  have e : slots Spec.MlKem1024.keyGenSig = 4 := by decide
  have h' := Verified.callWipe' (sig := Spec.MlKem1024.keyGenSig) (ps₁ := Spec.MlKem1024.keyGenSig.params.dropLast) (ps₂ := [])
    (i := 3) (j := 3) (n := 49152) (name := "vg_mlkem1024_keygen_body") (zname := "vg_zeroize_core") h Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) hsp hd zeroize_noSp zeroize_stack
    (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide),
        show a + 32 = a + BitVec.ofNat 64 32 from rfl,
        ← bytesAt_agree hb.1 (by decide) (o := 32) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.1 (pw_disj hpw (i := 1) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1568) (by decide),
        ← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 3168) (by decide)]
      exact h)
    (Scrubbed.keyGen1024_wiped _)
    (by rw [e, show 88 + frameSize 4 + 4 = 120 by decide]; exact hsat)
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.keyGenSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 32) (by decide)])
  rw [e, show 88 + frameSize 4 + 4 = 120 by decide] at h'
  exact h'

/-- `vg_mlkem1024_encaps_h`. -/
theorem encapsH1024_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi 88))
    (hsp : NoSp body) (hd : stackUse body ≤ 88)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi 136).pre s) :
    Verified target (Impl.MlKem.X86.Wipe.wiped 6 49152 "vg_mlkem1024_encaps_h" body)
      (Scrubbed.encapsH1024Contract abi 136) := by
  have e : slots Spec.MlKem1024.encapsHSig = 6 := by decide
  have h' := Verified.callWipe' (sig := Spec.MlKem1024.encapsHSig) (ps₁ := Spec.MlKem1024.encapsHSig.params.dropLast) (ps₂ := [])
    (i := 5) (j := 5) (n := 49152) (name := "vg_mlkem1024_encaps_h_body") (zname := "vg_zeroize_core") h Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) hsp hd zeroize_noSp zeroize_stack
    (Nat.zero_le _)
    (by
      intro vs m₁ m₂ hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ at h
      change Curry.apply (α := Mem → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide),
        ← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)]
      exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide),
        ← bytesAt_agree0 hb.2.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.2.1 (pw_disj hpw (i := 4) (j := 5) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1568) (by decide)]
      exact h)
    (Scrubbed.encapsH1024_wiped _)
    (by rw [e, show 88 + frameSize 6 + 4 = 136 by decide]; exact hsat)
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
      simp only [Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)])
  rw [e, show 88 + frameSize 6 + 4 = 136 by decide] at h'
  exact h'

/-- `vg_mlkem1024_encaps`. -/
theorem encaps1024_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.encaps1024BodyContract abi 88))
    (hsp : NoSp body) (hd : stackUse body ≤ 88)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.encaps1024BodyContract abi 120).pre s) :
    Verified target (Impl.MlKem.X86.Wipe.wiped 5 49152 "vg_mlkem1024_encaps" body)
      (Scrubbed.encaps1024Contract abi 120) := by
  have e : slots Spec.MlKem1024.encapsSig = 5 := by decide
  have h' := Verified.callWipe' (sig := Spec.MlKem1024.encapsSig) (ps₁ := Spec.MlKem1024.encapsSig.params.dropLast) (ps₂ := [])
    (i := 4) (j := 4) (n := 49152) (name := "vg_mlkem1024_encaps_body") (zname := "vg_zeroize_core") h Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) hsp hd zeroize_noSp zeroize_stack
    (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 32) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide),
        ← bytesAt_agree0 (hb.2.2.2.1 (pw_disj hpw (i := 3) (j := 4) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 1568) (by decide)]
      exact h)
    (Scrubbed.encaps1024_wiped _)
    (by rw [e, show 88 + frameSize 5 + 4 = 120 by decide]; exact hsat)
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
      simp only [Spec.MlKem1024.encapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 1568) (by decide)])
  rw [e, show 88 + frameSize 5 + 4 = 120 by decide] at h'
  exact h'

/-- `vg_mlkem1024_decaps`. -/
theorem decaps1024_wipe {body : Prog isa}
    (h : Verified target body (Proof.MlKem.Scrubbed.decaps1024BodyContract abi 88))
    (hsp : NoSp body) (hd : stackUse body ≤ 88)
    (hsat : ∃ s, (Proof.MlKem.Scrubbed.decaps1024BodyContract abi 120).pre s) :
    Verified target (Impl.MlKem.X86.Wipe.wiped 4 49152 "vg_mlkem1024_decaps" body)
      (Scrubbed.decaps1024Contract abi 120) := by
  have e : slots Spec.MlKem1024.decapsSig = 4 := by decide
  have h' := Verified.callWipe' (sig := Spec.MlKem1024.decapsSig) (ps₁ := Spec.MlKem1024.decapsSig.params.dropLast) (ps₂ := [])
    (i := 3) (j := 3) (n := 49152) (name := "vg_mlkem1024_decaps_body") (zname := "vg_zeroize_core") h Proof.Zeroize.X86.verified
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) hsp hd zeroize_noSp zeroize_stack
    (Nat.zero_le _)
    (by
      intro vs m₁ m₂ _ _ h
      rw [Curry.apply_const] at h ⊢; exact h)
    (by
      intro vs m₁ m₂ m' x hlen hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₁ m' x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m₂ m' x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 hb.1 (by decide) (n := 3168) (by decide),
        ← bytesAt_agree0 hb.2.1 (by decide) (n := 1568) (by decide)]
      exact h)
    (by
      intro vs m m₁ m₂ x hlen hpw hb h
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul, List.getD_cons_succ, List.getD_cons_zero] at hb
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₁ x at h
      change Curry.apply (α := Mem → Mem → BitVec 32 → Prop) [.addr, .addr, .addr, .addr] _ _ m m₂ x
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [← bytesAt_agree0 (hb.2.2.1 (pw_disj hpw (i := 2) (j := 3) (by decide) (Nat.lt_succ_self _) rfl)) (by decide)
          (n := 32) (by decide)]
      exact h)
    (Scrubbed.decaps1024_wiped _)
    (by rw [e, show 88 + frameSize 4 + 4 = 120 by decide]; exact hsat)
    (by
      intro vs m₁ m₂ hlen hb
      obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
      simp only [Spec.MlKem1024.decapsSig, Sig.bufs_array, Sig.bufs_nil, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Elem.size, Nat.reduceMul] at hb
      change Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₁ = Curry.apply (α := Mem → List Nat) [.addr, .addr, .addr, .addr] _ _ m₂
      dsimp only [Curry.apply, ArgWord.ofRaw]
      rw [bytesAt_agree0 hb.1 (by decide) (n := 3168) (by decide)])
  rw [e, show 88 + frameSize 4 + 4 = 120 by decide] at h'
  exact h'

/-! ## The stack the functions use: at most 88 bytes -/

theorem keyGen_stack : stackUse Impl.MlKem.X86.keyGen ≤ 88 := by lit_decide
theorem encapsH_stack : stackUse Impl.MlKem.X86.encapsH ≤ 88 := by lit_decide
theorem encaps_stack : stackUse Impl.MlKem.X86.encaps ≤ 88 := by lit_decide
theorem decaps_stack : stackUse Impl.MlKem.X86.decaps ≤ 88 := by lit_decide
theorem keyGen1024_stack : stackUse Impl.MlKem1024.X86.keyGen ≤ 88 := by lit_decide
theorem encapsH1024_stack : stackUse Impl.MlKem1024.X86.encapsH ≤ 88 := by lit_decide
theorem encaps1024_stack : stackUse Impl.MlKem1024.X86.encaps ≤ 88 := by lit_decide
theorem decaps1024_stack : stackUse Impl.MlKem1024.X86.decaps ≤ 88 := by lit_decide

/-! ## The states satisfying the preconditions, with the frame's bytes of stack -/

theorem keyGen_sat : ∃ s, (Proof.MlKem.Scrubbed.keyGenBodyContract abi 120).pre s := by
  refine ⟨satState KeyGen.satMem [⟨0, 64⟩]
      [⟨0x100, 1184⟩, ⟨0x1000, 2400⟩, ⟨0x10000, 32768⟩, ⟨0x5004, 16⟩], ?_⟩
  sig_sat_check [Proof.MlKem.Scrubbed.keyGenBodyContract, Spec.MlKem.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

theorem encapsH_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsHBodyContract abi 136).pre s := by
  refine ⟨Encaps.satStH, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
    sig_and_intros
    all_goals first
      | (fail_if_success show Spec.Sha3.bytesAt _ _ _ = _
         decide +kernel)
      | (rw [Encaps.satStH_ek, Encaps.satStH_h]
         exact VG.Proof.MlKem.hMem_h_of (by decide) Encaps.satMemH_low)

theorem encaps_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsBodyContract abi 120).pre s := by
  refine ⟨satState Encaps.satMem [⟨0, 1184⟩, ⟨0x800, 32⟩]
      [⟨0x1000, 32⟩, ⟨0x2000, 1088⟩, ⟨0x10000, 32768⟩, ⟨0x5004, 20⟩], ?_⟩
  sig_sat_check [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

theorem decaps_sat : ∃ s, (Proof.MlKem.Scrubbed.decapsBodyContract abi 120).pre s := by
  refine ⟨satState Decaps.satMem [⟨0, 2400⟩, ⟨0x1000, 1088⟩]
      [⟨0x2000, 32⟩, ⟨0x10000, 32768⟩, ⟨0x5004, 16⟩], ?_⟩
  sig_sat_check [Proof.MlKem.Scrubbed.decapsBodyContract, Spec.MlKem.decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

theorem keyGen1024_sat : ∃ s, (Proof.MlKem.Scrubbed.keyGen1024BodyContract abi 120).pre s := by
  refine ⟨satState Proof.MlKem1024.X86.KeyGen.satMem [⟨0, 64⟩]
      [⟨0x100, 1568⟩, ⟨0x1000, 3168⟩, ⟨0x10000, 49152⟩, ⟨0x5004, 16⟩], ?_⟩
  sig_sat_check [Proof.MlKem.Scrubbed.keyGen1024BodyContract, Spec.MlKem1024.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

theorem encapsH1024_sat : ∃ s, (Proof.MlKem.Scrubbed.encapsH1024BodyContract abi 136).pre s := by
  refine ⟨Proof.MlKem1024.X86.Encaps.satStH1024, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Proof.MlKem.Scrubbed.encapsH1024BodyContract, Spec.MlKem1024.encapsHSig, Spec.MlKem.encapsHSigOf, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
    sig_and_intros
    all_goals first
      | (fail_if_success show Spec.Sha3.bytesAt _ _ _ = _
         decide +kernel)
      | (rw [Proof.MlKem1024.X86.Encaps.satStH1024_ek, Proof.MlKem1024.X86.Encaps.satStH1024_h]
         exact VG.Proof.MlKem.hMem_h_of (by decide) Encaps.satMemH_low)

theorem encaps1024_sat : ∃ s, (Proof.MlKem.Scrubbed.encaps1024BodyContract abi 120).pre s := by
  refine ⟨satState Proof.MlKem1024.X86.Encaps.satMem [⟨0, 1568⟩, ⟨0x800, 32⟩]
      [⟨0x1000, 32⟩, ⟨0x2000, 1568⟩, ⟨0x10000, 49152⟩, ⟨0x5004, 20⟩], ?_⟩
  sig_sat_check [Proof.MlKem.Scrubbed.encaps1024BodyContract, Spec.MlKem1024.encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

theorem decaps1024_sat : ∃ s, (Proof.MlKem.Scrubbed.decaps1024BodyContract abi 120).pre s := by
  refine ⟨satState Proof.MlKem1024.X86.Decaps.satMem [⟨0, 3168⟩, ⟨0x1000, 1568⟩]
      [⟨0x2000, 32⟩, ⟨0x10000, 49152⟩, ⟨0x5004, 16⟩], ?_⟩
  sig_sat_check [Proof.MlKem.Scrubbed.decaps1024BodyContract, Spec.MlKem1024.decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

/-! ## The functions -/

theorem keyGen_scrubbed :
    Verified target Impl.MlKem.X86.Wipe.keyGen (Scrubbed.keyGenContract abi 120) :=
  keyGen_wipe Proof.MlKem.X86.KeyGen.verified (NoSp.of_all (by lit_decide)) keyGen_stack keyGen_sat

theorem keyGen_verified :
    Verified target Impl.MlKem.X86.Wipe.keyGen (Spec.MlKem.keyGenContract abi 120) :=
  keyGen_scrubbed

theorem encapsH_scrubbed :
    Verified target Impl.MlKem.X86.Wipe.encapsH (Scrubbed.encapsHContract abi 136) :=
  encapsH_wipe Proof.MlKem.X86.Encaps.verifiedH (NoSp.of_all (by lit_decide)) encapsH_stack encapsH_sat

theorem encapsH_verified :
    Verified target Impl.MlKem.X86.Wipe.encapsH (Spec.MlKem.encapsHContract abi 136) :=
  encapsH_scrubbed

theorem encaps_scrubbed :
    Verified target Impl.MlKem.X86.Wipe.encaps (Scrubbed.encapsContract abi 120) :=
  encaps_wipe Proof.MlKem.X86.Encaps.verified (NoSp.of_all (by lit_decide)) encaps_stack encaps_sat

theorem encaps_verified :
    Verified target Impl.MlKem.X86.Wipe.encaps (Spec.MlKem.encapsContract abi 120) :=
  encaps_scrubbed

theorem decaps_scrubbed :
    Verified target Impl.MlKem.X86.Wipe.decaps (Scrubbed.decapsContract abi 120) :=
  decaps_wipe Proof.MlKem.X86.Decaps.verified (NoSp.of_all (by lit_decide)) decaps_stack decaps_sat

theorem decaps_verified :
    Verified target Impl.MlKem.X86.Wipe.decaps (Spec.MlKem.decapsContract abi 120) :=
  decaps_scrubbed

theorem keyGen1024_scrubbed :
    Verified target Impl.MlKem.X86.Wipe.keyGen1024 (Scrubbed.keyGen1024Contract abi 120) :=
  keyGen1024_wipe Proof.MlKem1024.X86.KeyGen.verified (NoSp.of_all (by lit_decide)) keyGen1024_stack keyGen1024_sat

theorem keyGen1024_verified :
    Verified target Impl.MlKem.X86.Wipe.keyGen1024 (Spec.MlKem1024.keyGenContract abi 120) :=
  keyGen1024_scrubbed

theorem encapsH1024_scrubbed :
    Verified target Impl.MlKem.X86.Wipe.encapsH1024 (Scrubbed.encapsH1024Contract abi 136) :=
  encapsH1024_wipe Proof.MlKem1024.X86.Encaps.verifiedH (NoSp.of_all (by lit_decide)) encapsH1024_stack encapsH1024_sat

theorem encapsH1024_verified :
    Verified target Impl.MlKem.X86.Wipe.encapsH1024 (Spec.MlKem1024.encapsHContract abi 136) :=
  encapsH1024_scrubbed

theorem encaps1024_scrubbed :
    Verified target Impl.MlKem.X86.Wipe.encaps1024 (Scrubbed.encaps1024Contract abi 120) :=
  encaps1024_wipe Proof.MlKem1024.X86.Encaps.verified (NoSp.of_all (by lit_decide)) encaps1024_stack encaps1024_sat

theorem encaps1024_verified :
    Verified target Impl.MlKem.X86.Wipe.encaps1024 (Spec.MlKem1024.encapsContract abi 120) :=
  encaps1024_scrubbed

theorem decaps1024_scrubbed :
    Verified target Impl.MlKem.X86.Wipe.decaps1024 (Scrubbed.decaps1024Contract abi 120) :=
  decaps1024_wipe Proof.MlKem1024.X86.Decaps.verified (NoSp.of_all (by lit_decide)) decaps1024_stack decaps1024_sat

theorem decaps1024_verified :
    Verified target Impl.MlKem.X86.Wipe.decaps1024 (Spec.MlKem1024.decapsContract abi 120) :=
  decaps1024_scrubbed

end VG.Proof.MlKem.X86.Wipe
