import VerifiedGarbage.Proof.RsaPss.X86_64.SignPro

/-!
# RSASSA-PSS signing on x86-64: refusing

`signFail` writes zeros to `out` and returns 0 (`signFail_ok`), changing
nothing else of the working space or the frame.
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

/-- `Rep` across changes outside the working space and the frame. -/
theorem Rep.of_outside {m m' : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W)
    {O : Region} (hm : ∀ x, ¬ O.Contains x 1 → m' x = m x) (hS : O.Disjoint ⟨S, oRsa⟩)
    (hF : O.Disjoint ⟨F, frameBytes⟩) (G : Geo F S) : Rep m' F S V W where
  scr o ho := by
    rw [hm _ fun h => hS _ h (Offset.contains_base _ (by omega) (by unfold oRsa at *; omega)), R.scr o ho]
  fr k hk := by
    rw [← R.fr k hk]
    refine Mem.readW_congr fun i hi => hm _ fun h => hF _ h ?_
    have := G.Fw
    rw [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.contains_base _ (by unfold nW frameBytes at *; omega) (by unfold nW frameBytes at *; omega)

structure ZI (u₀ : State) (p : Addr) (j : Nat) (v : State) : Prop where
  keep : Keep [.r8] u₀ v
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  mem : ∀ x, v.mem x = if (⟨p, j⟩ : Region).Contains x 1 then 0 else u₀.mem x

/-- Zeros to the `n` bytes at `p` (`rdi`), a byte at a time. -/
theorem zeroOut_ok {u₀ : State} {p : Addr} {n : Nat} {cnt : Src} (hs : StepOk cnt n u₀ [.r8]) (hn : 0 < n)
    (hpn : p.toNat + n ≤ 2 ^ 64) (hw : (⟨p, n⟩ : Region) ∈ u₀.wr)
    (hdi : u₀.gpr .rdi = p) (hax : u₀.gpr .rax = 0) (h8 : u₀.gpr .r8 = BitVec.ofNat 64 0) :
    WP isa (byteLoop [.store8 (ix .rdi .r8) .rax] cnt) u₀ fun u' => Keep [.r8] u₀ u' ∧
      ∀ x, u'.mem x = if (⟨p, n⟩ : Region).Contains x 1 then 0 else u₀.mem x := by
  refine WP.mono (byteLoop_ok hn hs (ZI u₀ p) ?_ (u := u₀)
    ⟨Keep.refl _ _, h8, fun x => by simp [Region.Contains]⟩) fun u' I => ⟨I.keep, I.mem⟩
  intro j hj v I
  have hdv : v.gpr .rdi = p := (I.keep.gpr (by decide)).trans hdi
  have hav : v.gpr .rax = 0 := (I.keep.gpr (by decide)).trans hax
  have hea : p + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = p + BitVec.ofNat 64 j := by
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  have hin : InRegions v.wr (p + BitVec.ofNat 64 j) 1 :=
    ⟨_, I.keep.2.2 ▸ hw, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (WP.keep [] (Q := fun v' => v'.gpr .r8 = BitVec.ofNat 64 j ∧
      v'.mem = v.mem.writeW (p + BitVec.ofNat 64 j) (0 : Byte)) ?_ rfl)
    fun v' ⟨⟨h8', hm⟩, k⟩ => ⟨(I.keep.trans k).mono (by decide), h8', fun v'' k' hm' h8'' => ?_⟩
  · xrun [ea_ix, hdv, I.r8, hea, hin, hav]
    rfl
  refine ⟨(I.keep.trans (k.trans k')).mono (by decide), h8'', fun x => ?_⟩
  rw [hm', hm, VG.WriteBytes.writeW8_apply, I.mem x]
  have hx : (x - p).toNat < 2 ^ 64 := (x - p).isLt
  by_cases he : x = p + BitVec.ofNat 64 j
  · subst he
    rw [ifp rfl]
    exact (ifp (show (⟨p, j + 1⟩ : Region).Contains (p + BitVec.ofNat 64 j) 1 from
      Offset.contains_base _ (by omega) (by omega)) _ _).symm
  · rw [ifn he]
    have hne : (x - p).toNat ≠ j := fun h => he (by
      rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel])
    have iff : (⟨p, j + 1⟩ : Region).Contains x 1 ↔ (⟨p, j⟩ : Region).Contains x 1 := by
      simp only [Region.Contains]; omega
    by_cases h1 : (⟨p, j⟩ : Region).Contains x 1
    · rw [ifp h1, ifp (iff.mpr h1)]
    · rw [ifn h1, ifn (fun h => h1 (iff.mp h))]

/-- Zeros to `out` (`k` bytes) and 0 in `rax`. -/
theorem signFail_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {out : Addr} {k : Nat} (ho : W 16 = out) (hk : W 17 = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk2 : k ≤ 1024) (hw : (⟨out, k⟩ : Region) ∈ u.wr) (hpn : out.toNat + k ≤ 2 ^ 64)
    (hS : (⟨out, k⟩ : Region).Disjoint ⟨S, oRsa⟩) (hF : (⟨out, k⟩ : Region).Disjoint ⟨F, frameBytes⟩) :
    WP isa signFail u fun u' => Lay u' F S ∧ Keep [.rdi, .r10, .rax, .r8] u u' ∧ Rep u'.mem F S V W ∧
      u'.gpr .rax = 0 ∧ Spec.Rsa.bytesAt u'.mem out k = List.replicate k 0 ∧
      (∀ x, ¬ (⟨out, k⟩ : Region).Contains x 1 → u'.mem x = u.mem x) := by
  refine WP.seq (WP.mono (WP.keep [.rdi, .r10, .rax, .r8] (Q := fun v => v.gpr .rdi = out ∧
      v.gpr .r10 = BitVec.ofNat 64 k ∧ v.gpr .rax = 0 ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₁₀, h₂, h₃, hm⟩, hkv⟩ => ?_)
  · xrun [signFail, ea_sp, L.rsp, L.ld (d := sOut) (by decide), L.ld (d := sK) (by decide),
      R.rd (d := sOut) 16 rfl (by decide), R.rd (d := sK) 17 rfl (by decide), ho, hk]
  refine WP.mono (zeroOut_ok (stepR_ok (by omega) v (show Reg.r10 ∉ [Reg.r8] by decide) (by decide) h₁₀)
    (by omega) hpn (by rw [hkv.2.2]; exact hw) h₁ h₂ h₃) fun w ⟨kw, hmw⟩ => ?_
  have hout : ∀ x, ¬ (⟨out, k⟩ : Region).Contains x 1 → w.mem x = u.mem x := fun x hx => by
    rw [hmw, ifn hx, hm]
  have Rw : Rep w.mem F S V W := R.of_outside hout hS hF L.geo
  refine ⟨L.of_rep R Rw ((kw.gpr (by decide)).trans (hkv.gpr (by decide))) (kw.2.2.trans hkv.2.2),
    (hkv.trans kw).mono (by decide), Rw, (kw.gpr (by decide)).trans h₂, ?_, hout⟩
  simp only [Spec.Rsa.bytesAt]
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
  rw [hmw, ifp (Offset.contains_base _ (by simp at h₁; omega) (by simp at h₁; omega))]

end VG.Proof.RsaPss.X86_64
