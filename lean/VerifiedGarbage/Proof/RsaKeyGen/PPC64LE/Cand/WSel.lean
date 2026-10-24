module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Witness
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Candidate
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.WUni
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.WForced
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.RangeCover

/-!
# A candidate on PPC64LE: a witness from a draw

`witness_ok`: the draw `x` in array 4 becomes `RsaKeyGen.witness (c − 1) x`'s
witness, `x` if it is uniform, else the forced one (`witness_eq`), selected
under the mask of the flag; the flag is added to the uniform witnesses so far
(`hUni`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Witness (witness hUni)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth)
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.Bignum (slot wv)

/-- The registers `witness` writes. -/
def witRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r8, .r9, .r14, .r15, .r16, .r17, .r20, .r21]

/-- What `witness` changes: arrays 3, 4 and 6, and `hUni`. -/
def witRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * hUni, 8), (slot w 3, 8 * (w + 2)), (slot w 4, 8 * (w + 2)), (slot w 6, 8 * (w + 2))]

theorem witness_ok {s : State} {B : Addr} {Z w c u : Nat} (h : Env s B Z w)
    (h35 : slot w VG.Impl.RsaKeyGen.PPC64LE.Candidate.nArr ≤ Z) (hc : wv s.mem B (slot w 0) w = c)
    (hc2 : c % 2 = 1) (hcb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w) (hcR : c < 2 ^ (64 * w))
    (hu : VG.Proof.Mont.word s.mem B (8 * hUni) = BitVec.ofNat 64 u) :
    WP isa witness s fun t =>
      (arr t.mem B w 4 = (Spec.RsaKeyGen.witness (c - 1) (wv s.mem B (slot w 4) w)).1 ∧
        VG.Proof.Mont.word t.mem B (8 * hUni) = BitVec.ofNat 64
          (u + if (Spec.RsaKeyGen.witness (c - 1) (wv s.mem B (slot w 4) w)).2 then 1 else 0) ∧
        Env t B Z w ∧ VG.Proof.Mont.Outs B (witRanges w) s.mem t.mem) ∧ Keep witRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  have hZ := h35
  simp only [VG.Impl.RsaKeyGen.PPC64LE.Candidate.nArr] at hZ
  rw [slot_lin] at hZ
  generalize hx : wv s.mem B (slot w 4) w = x
  have hxR : x < 2 ^ (64 * w) := by rw [← hx]; exact VG.Proof.Bignum.wv_lt _ _ _ _
  rw [VG.Proof.RsaKeyGen.witness_eq hc2 hcb hxR]
  generalize hP : (decide (2 ≤ x) && decide (x + (1 - x % 2) < c)) = P
  unfold witness
  refine WP.seq (WP.mono (uniform_ok h h35 hc hcR) fun t₁ ⟨⟨a21, e₁, o₁⟩, k₁⟩ => ?_)
  rw [hx] at a21
  have hx₁ : wv t₁.mem B (slot w 4) w = x := by
    rw [← hx, ← Pre.val32_eq_wv, ← Pre.val32_eq_wv]
    exact o₁.val32 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;> rw [slot_lin, slot_lin] <;> omega) (by rw [slot_lin]; omega)
  refine WP.seq (WP.mono (forced_ok e₁) fun t₂ ⟨⟨f3, z3, o₂, e₂⟩, k₂⟩ => ?_)
  rw [hx₁] at f3
  have r21₂ : t₂.gpr .r21 = BitVec.ofNat 64 (if P then 1 else 0) := by
    rw [k₂.gpr _ (by decide), a21, ← hP]
    by_cases e1 : 2 ≤ x <;> by_cases e2 : x + (1 - x % 2) < c <;> simp [e1, e2]
  refine WP.seq (WP.mono (WP.keep [.r0, .r20] (Q := fun t => t.gpr .r20 = BitVec.ofNat 64 0 -
      BitVec.ofNat 64 (if P then 1 else 0) ∧ t.mem = t₂.mem) (by prun [r21₂]) (by decide))
    fun t₃ ⟨⟨a20, m₃⟩, k₃⟩ => ?_)
  have e₃ := e₂.keep k₃ (by decide)
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.PPC64LE.sel_ok e₃ (b := P) (o := 6) (a := 4) (t := 3) (by decide)
    (by decide) (by decide) (by decide) (by decide) a20) fun t₄ ⟨⟨v₄, o₄⟩, k₄⟩ => ?_)
  have e₄ := e₃.keep k₄ (by decide)
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.PPC64LE.copy_ok e₄ (o := 4) (a := 6) (by decide) (by decide)
    (by decide)) fun t₅ ⟨⟨v₅, o₅⟩, k₅⟩ => ?_)
  have e₅ := e₄.keep k₅ (by decide)
  have r21₅ : t₅.gpr .r21 = BitVec.ofNat 64 (if P then 1 else 0) := by
    rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), r21₂]
  have s3 : 256 ≤ slot w 3 := by rw [slot_lin]; omega
  have s4 : 256 ≤ slot w 4 := by rw [slot_lin]; omega
  have s6 : 256 ≤ slot w 6 := by rw [slot_lin]; omega
  have u₅ : VG.Proof.Mont.word t₅.mem B (8 * hUni) = BitVec.ofNat 64 u := by
    simp only [hUni] at hu ⊢
    rw [o₅.word (by omega) (by omega), o₄.word (by omega) (by omega), m₃, o₂.word (by omega) (by omega),
      VG.Proof.Mont.Outs.word o₁ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only [] <;> omega) (by omega), hu]
  have hs₅ := e₅.hs
  refine WP.mono (WP.keep [.r3] (Q := fun t => t.mem = t₅.mem.writeW (VG.Proof.Mont.off B (8 * hUni))
      (BitVec.ofNat 64 (u + if P then 1 else 0))) (by
    simp only [ldh, sth, hUni] at u₅ ⊢
    prun [e₅.h31, u₅, r21₅, hs₅.ld (d := 16) (n := 8) (by omega), hs₅.st (d := 16) (n := 8) (by omega),
      BitVec.ofNat_add_ofNat]) (by decide)) fun t ⟨tm, kt⟩ => ?_
  have K := ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans kt
  have hm4 : VG.Proof.Mont.val32 t₃.mem B (slot w 4) (2 * w) = x := by
    rw [m₃, Pre.val32_eq_wv, ← hx₁, ← Pre.val32_eq_wv, ← Pre.val32_eq_wv]
    exact o₂.val32 (by rw [slot_lin, slot_lin]; omega) (by rw [slot_lin]; omega)
  have hm3 : VG.Proof.Mont.val32 t₃.mem B (slot w 3) (2 * w) = (x ||| 2) % 2 ^ (64 * w - 1) := by
    rw [m₃, Pre.val32_eq_wv, f3]
  refine ⟨⟨?_, ?_, e₅.keep kt (by decide), ?_⟩, K.mono (by simp [witRegs, uniRegs, fdRegs,
    VG.Proof.MillerRabin.PPC64LE.selRegs, VG.Proof.MillerRabin.PPC64LE.copyRegs])⟩
  · show VG.Proof.Mont.val32 t.mem B (slot w 4) (2 * w) = _
    rw [tm, (VG.Proof.Mont.writeW_outside t₅.mem B (d := 8 * hUni) _ (by simp only [hUni]; omega)).val32
      (by simp only [hUni]; omega) (by rw [slot_lin]; omega)]
    show arr t₅.mem B w 4 = _
    rw [v₅]; show VG.Proof.Mont.val32 t₄.mem B (slot w 6) (2 * w) = _
    rw [v₄, hm4, hm3]
  · rw [tm]; exact VG.Proof.Mont.word_writeW_self _ _ _ _
  · intro y hy
    simp only [witRanges, hUni, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hy
    obtain ⟨y1, y3, y4, y6⟩ := hy
    rw [tm, VG.Proof.Mont.writeW_outside t₅.mem B (d := 8 * hUni) _ (by simp only [hUni]; omega) y
      (by simp only [hUni]; omega), o₅ y y4, o₄ y y6, m₃,
      o₂ y (by omega), o₁ y (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only [] <;> omega)]

end VG.Proof.RsaKeyGen.PPC64LE.Cand
