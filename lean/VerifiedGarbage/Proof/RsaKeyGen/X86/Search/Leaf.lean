module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Entry
public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Zero
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.X86.Common
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Entry
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Zero
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86.Common

/-! # Zeros at `out` (i686)

`zeroOut` writes `out_len` zeros at `out` and changes nothing else but the
scratch registers (`zeroOut_ok`), with the loop of FFDH's controller
(`Proof/Ffdh/X86/KeySearch/Zero.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Impl.RsaKeyGen.X86.Search
open VG.Impl.Mont.X86 (at_)
open VG.Proof.Mont.X86 (Keeps)
open VG.Proof.Ffdh.X86.KeySearch (ZInv zeroStep_ok)

theorem Keep.ofKeeps {rs : List Reg} {s t : State} (h : Keeps rs s t) : Keep rs s t := ⟨h.1, h.2.1, h.2.2⟩

theorem zeroOut_ok {p : SearchPublic} {o s : State} (hb : SearchBase p o s) :
    WP isa zeroOut s fun u => (Frame [oR o] s.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem (p.op.setWidth 64) p.len = List.replicate p.len 0) ∧
        Keep [.eax, .ecx, .edx] s u ∧ u.syms = s.syms := by
  have A := hb.input.abi
  have hv := hb.input.len_valid
  have hop : p.op = arg o 0 := by rw [← hb.input.2]; rfl
  have hlen : BitVec.ofNat 32 p.len = arg o 1 := by
    rw [← hb.input.2]; change BitVec.ofNat 32 (arg o 1).toNat = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hpl : p.len = (arg o 1).toNat := by rw [← hb.input.2]; rfl
  have hR : (⟨(arg o 0).setWidth 64, p.len⟩ : Region) ∈ s.wr := by
    rw [hb.wr, A.wr, hpl]; simp
  have hbnd : (arg o 0).toNat + p.len ≤ 2 ^ 32 := by rw [← hb.input.2]; exact A.oBound
  refine WP.mono_syms (Q := fun u => (Frame [oR o] s.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem (p.op.setWidth 64) p.len = List.replicate p.len 0) ∧
        Keep [.eax, .ecx, .edx] s u) ?_ fun u h sy => ⟨h.1, h.2, sy⟩
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.eax, .ecx, .edx] (Q := fun t => t.gpr .edx = arg o 0 ∧
      t.gpr .ecx = arg o 1 ∧ t.gpr .eax = 0 ∧ t.mem = s.mem) ?_ (by rfl)) fun t ⟨⟨hd, hc, ha, hm⟩, k⟩ => ?_)
  · simp only [param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
    xrun [State.ea, at_, hb.arg_ea (i := 0) (d := 20) rfl, hb.arg_ea (i := 1) (d := 24) rfl,
      hb.arg_in (i := 0) (by decide), hb.arg_in (i := 1) (by decide), hb.arg_val (i := 0) (by decide),
      hb.arg_val (i := 1) (by decide)]
  have I₀ : ZInv t (arg o 0) p.len 0 t := ⟨by rw [hd, BitVec.add_zero], by rw [hc, Nat.sub_zero, hlen], ha,
    Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _), Keeps.refl _ _⟩
  have hRt : (⟨(arg o 0).setWidth 64, p.len⟩ : Region) ∈ t.wr := by rw [k.2.2]; exact hR
  refine WP.loop (M := isa) (fun (j : Nat) (u : State) => ∃ k, j = p.len - k ∧ k < p.len ∧ ZInv t (arg o 0) p.len k u)
    (fun j u hu => ?_) _ t ⟨0, rfl, by omega, I₀⟩
  obtain ⟨i, rfl, hk, I⟩ := hu
  refine WP.mono (zeroStep_ok hRt hbnd (by omega) hk I) fun v ⟨J, z⟩ => ?_
  by_cases he : p.len - (i + 1) = 0
  · left
    refine ⟨by simp only [eval, z, he, decide_true, Option.map_some, Bool.not_true], ⟨?_, ?_⟩, ?_⟩
    · have f := J.frame
      rw [hm] at f
      rw [show oR o = ⟨(arg o 0).setWidth 64, p.len⟩ by rw [← hb.input.2]; rfl]
      exact f
    · rw [hop]
      apply List.ext_getElem
      · simp [Spec.Rsa.bytesAt]
      · intro j h₁ _
        simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
        simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁
        exact J.zero j (by omega)
    · exact (k.trans (Keep.ofKeeps J.keeps)).mono (by simp)
  · right
    exact ⟨by simp only [eval, z, he, decide_false, Option.map_some, Bool.not_false], _, by omega,
      i + 1, rfl, by omega, J⟩

end VG.Proof.RsaKeyGen.X86.Search
