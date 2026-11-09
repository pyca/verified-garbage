module

public import VerifiedGarbage.Impl.MlDsa.X86.PkTr
public import VerifiedGarbage.Spec.MlDsa.PkTr
public import VerifiedGarbage.Proof.MlKem.X86.TopHash
public import VerifiedGarbage.Proof.MlKem.X86.TopKeep
import VerifiedGarbage.Proof.MlKem.X86.TopLocal
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.X86.Lit
meta import VerifiedGarbage.Impl.MlDsa.X86.PkTr
meta import VerifiedGarbage.Spec.MlDsa.PkTr
meta import VerifiedGarbage.Proof.MlKem.X86.TopHash
meta import VerifiedGarbage.Proof.MlKem.X86.TopKeep
meta import VerifiedGarbage.Proof.MlKem.X86.TopLocal
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Seeds
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha3.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa*_pk_tr`

Untrusted: everything here is checked by Lean. The body (`Impl/MlDsa/X86/PkTr.lean`)
as a top-level function of ML-KEM's setting (`Proof/MlKem/X86/Top.lean`): the
layout `YT p` (`pk` read, `tr` and `scratch` written, 56 bytes of stack), the
load of `scratch` (`ldsc_piece`), and the hash (`hash1_piece`), whose sponge
is `H` (`sponge_H`) of the bytes of `pk`, which the body does not write
(`Ctx.roBytes`); as a leaf (`topLeaf`), it meets `pkTrContract p X86.abi 56`
(`pkTr_verified`). Nothing is leaked.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.PkTr

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.PkTr
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)
open VG.Spec.Sha3 (bytesAt)

/-- `pk` (read), `tr` and `scratch` (written); 56 bytes of stack. -/
def YT (p : Params) : Lay := ⟨[(p.pkLen, false), (64, true), (scratchWords p * 8, true)], kS, 56⟩

/-- Nothing is leaked. -/
def lk (_ : State) : List Byte := []

/-- What the body establishes: `tr = H(pk, 64)`. -/
def Done (p : Params) (s₀ s : State) : Prop :=
  bytesAt s.mem (Buf.addr s₀ ⟨1, 0, 64⟩) 64 = Spec.MlDsa.H (bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, p.pkLen⟩) p.pkLen) 64

theorem body_piece {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    Piece (TPre (YT p)) (TPub (YT p) lk) (fun s₀ s => s = P0 s₀) (fun s₀ s => Ctx (YT p) s₀ s ∧ Done p s₀ s)
      (body p) := by
  have hc : ((YT p).okW ⟨(YT p).sc, 0, 200⟩ && (YT p).okW ⟨(YT p).sc, 200, 640⟩ && (YT p).ok ⟨0, 0, p.pkLen⟩ &&
      (YT p).okW ⟨1, 0, 64⟩ && (YT p).sep ⟨(YT p).sc, 0, 200⟩ ⟨(YT p).sc, 200, 640⟩ &&
      (YT p).sep ⟨0, 0, p.pkLen⟩ ⟨(YT p).sc, 0, 200⟩ && (YT p).sep ⟨0, 0, p.pkLen⟩ ⟨(YT p).sc, 200, 640⟩ &&
      (YT p).sep ⟨(YT p).sc, 0, 200⟩ ⟨1, 0, 64⟩ && (YT p).sep ⟨1, 0, 64⟩ ⟨(YT p).sc, 200, 640⟩) = true := by
    rcases hp with rfl | rfl | rfl <;> decide
  have hl : p.pkLen < 2 ^ 32 := by rcases hp with rfl | rfl | rfl <;> decide
  have hro : (YT p).ok ⟨0, 0, p.pkLen⟩ = true := by rcases hp with rfl | rfl | rfl <;> decide
  refine (ldsc_piece (Y := YT p) (lk := lk) (ht := .block []) (by kernel_rfl)).seq ?_
  refine hash1_piece (Y := YT p) 0 200 136 0x1f ⟨0, 0, p.pkLen⟩ ⟨1, 0, 64⟩ (by decide) hc (Nat.le_refl _) hl
    (by decide) (by native_taint_decide) (h₁ := .block []) (by kernel_rfl) (h₃ := .block []) (by kernel_rfl)
    (h₄ := .block []) (by kernel_rfl) (fun _ _ _ h => h) fun s₀ s s' hp' h h' _ out => ⟨h', ?_⟩
  rw [Done, out, Proof.MlDsa.X86.KeyGen.sponge_H, h.roBytes hp' hro (by rfl)]

theorem body_nosp (p : Params) : NoSp (body p) := NoSp.of_all (by kernel_rfl)

/-! ## The contract -/

theorem pre_of {p : Params} {s₀ : State} (h : (Spec.MlDsa.pkTrContract p X86.abi 56).pre s₀) : TPre (YT p) s₀ := by
  sig_pre [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 56#64, 56⟩ : Region) = below (E0 s₀) 56 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h15 h16 h17 h18
  have c3 : ∀ i, i < (YT p).n → i = 0 ∨ i = 1 ∨ i = 2 := fun i hi => by
    simp only [YT, Lay.n, List.length_cons, List.length_nil] at hi; omega
  refine ⟨h1, by show 16 ≤ 56; decide, by simp only [YT, Lay.n, List.length_cons, List.length_nil]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h18, ?_, by show 2 < 3; decide⟩
  · intro i hi hw
    rcases c3 i hi with rfl | rfl | rfl
    · rw [h3]; exact List.mem_singleton_self _
    all_goals simp [YT, Lay.awr] at hw
  · intro i hi hw
    rw [h4]
    rcases c3 i hi with rfl | rfl | rfl
    · simp [YT, Lay.awr] at hw
    all_goals simp [argR, Lay.alen, YT]
  · rw [h4]; simp [gR, Lay.n, YT]
  · intro i hi j hj hne _
    rcases c3 i hi with rfl | rfl | rfl <;> rcases c3 j hj with rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | skip
    all_goals simp only [argR, Lay.alen, YT, List.getD_cons_zero, List.getD_cons_succ]
    exacts [h5, h6, h5.symm, h8, h6.symm, h8.symm]
  · intro i hi
    rcases c3 i hi with rfl | rfl | rfl <;> simp only [argR, gR, Lay.n, Lay.alen, YT, List.getD_cons_zero,
      List.getD_cons_succ, List.length_cons, List.length_nil]
    · exact h7.symm
    · exact h9.symm
    · exact h10.symm
  · intro i hi
    rcases c3 i hi with rfl | rfl | rfl <;> simp only [argR, Lay.alen, YT, List.getD_cons_zero, List.getD_cons_succ]
    · exact h11
    · exact h12
    · exact h13
  · intro i hi
    rcases c3 i hi with rfl | rfl | rfl <;> simp only [argR, Lay.alen, YT, List.getD_cons_zero, List.getD_cons_succ]
    · exact h15
    · exact h16
    · exact h17
  · intro i hi
    rcases c3 i hi with rfl | rfl | rfl <;> simp only [Lay.alen, YT, List.getD_cons_zero, List.getD_cons_succ]
    · exact h19
    · exact h20
    · exact h21

theorem pub_of {p : Params} {s₀ s₀' : State} (h : (Spec.MlDsa.pkTrContract p X86.abi 56).pub s₀ s₀') :
    TPub (YT p) lk s₀ s₀' := by
  sig_pub [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄⟩ := h
  refine ⟨e₁, fun i hi => ?_, rfl⟩
  simp only [YT, Lay.n, List.length_cons, List.length_nil] at hi
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  exacts [e₂, e₃, e₄]

theorem addr0 (s₀ : State) (i : Nat) (l : Nat) : Buf.addr s₀ ⟨i, 0, l⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

/-- Memory with the arguments `0`, `0x1000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 0x10 else if a = 0x500e then 1 else 0

/-- A state satisfying the precondition. -/
def pkTrSat (p : Params) : State :=
  satState satMem [⟨0, p.pkLen⟩] [⟨0x1000, 64⟩, ⟨0x10000, scratchWords p * 8⟩, ⟨0x5004, 12⟩]

theorem pkTr_verified (p : Params) (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    Verified X86.target (pkTr p) (Spec.MlDsa.pkTrContract p X86.abi 56) := by
  refine Piece.verified (((topLeaf (body_nosp p) (body_piece hp)).pre_mono (fun _ h => pre_of h)
    fun _ _ _ _ h => pub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hd, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    have r : Done p s₀ s := hd
    simp only [Done, addr0] at r
    exact r
  · rcases hp with rfl | rfl | rfl
    · exact ⟨pkTrSat mlDsa44, by sig_sat_check [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, pkTrSat, satState, satMem]⟩
    · exact ⟨pkTrSat mlDsa65, by sig_sat_check [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, pkTrSat, satState, satMem]⟩
    · exact ⟨pkTrSat mlDsa87, by sig_sat_check [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, pkTrSat, satState, satMem]⟩

theorem pkTr44_verified : Verified X86.target (pkTr mlDsa44) (Spec.MlDsa.pkTrContract mlDsa44 X86.abi 56) :=
  pkTr_verified _ (.inl rfl)
theorem pkTr65_verified : Verified X86.target (pkTr mlDsa65) (Spec.MlDsa.pkTrContract mlDsa65 X86.abi 56) :=
  pkTr_verified _ (.inr (.inl rfl))
theorem pkTr87_verified : Verified X86.target (pkTr mlDsa87) (Spec.MlDsa.pkTrContract mlDsa87 X86.abi 56) :=
  pkTr_verified _ (.inr (.inr rfl))

end VG.Proof.MlDsa.X86.PkTr
