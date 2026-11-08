module

public import VerifiedGarbage.Proof.MlKem.Scrubbed
public import VerifiedGarbage.Proof.MlKem.X86.EncapsBody
import VerifiedGarbage.Proof.MlKem.X86.EncInst
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.MlKem.EncapsH
import VerifiedGarbage.Proof.MlKem.EncapsHSat

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
    simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi; omega
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
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
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
    (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Proof.MlKem.Scrubbed.encapsBodyContract, encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, hm]
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
    simp only [YH, Lay.n, List.length_cons, List.length_nil] at hi; omega
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
    obtain rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
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
    rw [setWidth_append32, hax, hfin.eax, hm]
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
