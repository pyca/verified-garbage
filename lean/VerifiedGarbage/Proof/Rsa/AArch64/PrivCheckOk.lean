import VerifiedGarbage.Proof.Rsa.AArch64.PrivRelease

/-!
# `vg_rsa_private_checked` on AArch64: what follows the CRT

`check_ok` runs everything after the call of the CRT, from any state the
frames allow: whatever `M` holds and whatever the CRT returned (`r₁`), it
releases `M` to `out` (and returns 1) only if `r₁` is odd, `n` is a valid
modulus and the public operation of `M` with `e`, within BoringSSL's
limits, is the input; otherwise `out` is zeros (`released`, `checkResult`).
This is the fault tolerance of the check.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked
open VG.Proof.Rsa (released checkResult gOf result)

/-- The bytes of a region that a frame's regions miss are unchanged. -/
theorem frame_bytesAt {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- The words of a region that a frame's regions miss are unchanged. -/
theorem frame_wordsAt {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 8 * n⟩ r) (hn : 8 * n < 2 ^ 64) :
    Spec.Rsa.wordsAt m' p n = Spec.Rsa.wordsAt m p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf.readW (r := ⟨p, 8 * n⟩) (Offset.contains_base _ (by omega) (by omega)) hd (by decide)

theorem check_eq (pcName : String) (pc : Prog isa) (pdName : String) (pd : Prog isa) :
    seqs (check pcName pc pdName pd) =
      .seq (.block pcArgs) (.seq (.call pcName pc) (.seq (.block pdArgs) (.seq (.call pdName pd)
        (seqs tail)))) := rfl

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

namespace Ctx
variable {t : State} (hc : Ctx L g vv m₀ t) (hL : L.Ok)
include hc hL

theorem n_bytes : Spec.Rsa.bytesAt t.mem L.n L.k.toNat = Spec.Rsa.bytesAt m₀ L.n L.k.toNat :=
  frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [hL.on.symm, hL.nsc, hL.kn.symm]) (by have := hL.bn; omega)

theorem e_bytes : Spec.Rsa.bytesAt t.mem L.e L.el.toNat = Spec.Rsa.bytesAt m₀ L.e L.el.toNat :=
  frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [hL.oe.symm, hL.esc, hL.ke.symm]) (by have := hL.be; omega)

theorem inp_bytes : Spec.Rsa.bytesAt t.mem L.inp L.k.toNat = Spec.Rsa.bytesAt m₀ L.inp L.k.toNat := by
  have h := frame_bytesAt hc.frame (p := L.inp) (n := L.il.toNat) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [hL.oi.symm, hL.isc, hL.ki.symm]) (by have := hL.bi; omega)
  rwa [hL.ilk] at h

end Ctx

/-- A slot, in the inner frame below `M`, misses what the calls write. -/
theorem slot_disj (hL : L.Ok) {d : Nat} (hd : 80 ≤ d ∧ d + 8 ≤ oM) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ L.PRE ∧ Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ L.SC ∧
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ L.M ∧
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ ⟨L.out, L.k.toNat⟩ ∧
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, 8⟩ ⟨L.B, 16⟩ := by
  have hnB := hL.nB
  have hk := hL.khi
  have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 d, 8⟩ L.STK := Offset.sub_base _ (by simp only [oM, stackBytes] at hd ⊢; omega)
  refine ⟨Offset.disjoint _ (.inl (by simp only [oM, oPre] at hd ⊢; omega)) (by simp only [oM] at hd; omega)
      (by simp only [oPre, Lay.pw]; omega), (hL.ksc.sub_left hs),
    Offset.disjoint _ (.inl hd.2) (by simp only [oM] at hd; omega) (by simp only [oM]; omega), ?_,
    Offset.disjoint_base _ (by omega) (by simp only [oM] at hd; omega)⟩
  rw [show (⟨L.out, L.k.toNat⟩ : Region) = L.OUT by rw [Lay.OUT, hL.olk]]
  exact hL.ko.sub_left hs

/-- Everything after the CRT, from any state the frames allow: whatever `M`
holds and the CRT returned. -/
theorem check_ok (v : CrtImpl) (hL : L.Ok) (ha : ArgsAt L m₀) {t : State} (hc : Ctx L g vv m₀ t)
    (hs : Slots L t.mem) :
    WP isa (seqs (check v.pcName v.pc v.pdName v.pd)) t fun t' => Ctx L g vv m₀ t' ∧
      t'.gpr .x0 = checkResult (t.gpr .x0) (Spec.Rsa.bytesAt m₀ L.n L.k.toNat)
        (Spec.Rsa.bytesAt m₀ L.e L.el.toNat) (Spec.Rsa.bytesAt m₀ L.inp L.k.toNat)
        (Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat) ∧
      Spec.Rsa.bytesAt t'.mem L.out L.k.toNat =
        (if released (t.gpr .x0) (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) (Spec.Rsa.bytesAt m₀ L.e L.el.toNat)
            (Spec.Rsa.bytesAt m₀ L.inp L.k.toNat) (Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat)
          then Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat
          else List.replicate L.k.toNat 0) ∧
      Spec.Rsa.bytesAt t'.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat = List.replicate L.k.toNat 0 := by
  have hnB := hL.nB
  have hk := hL.khi
  have hMs : Region.Sub L.M L.STK := hL.M_sub
  have hM := hL.stk_sub hMs
  have hOk : (⟨L.out, L.k.toNat⟩ : Region) = L.OUT := by rw [Lay.OUT, hL.olk]
  rw [check_eq]
  refine WP.seq (WP.mono (pcArgs_ok hL ha hc hs) fun t₁ ⟨hc₁, hs₁, pa, hR1, f₁⟩ => ?_)
  refine WP.seq (WP.mono (pc_call v hL hc₁ hs₁ pa) fun t₂ ⟨hc₂, hs₂, f₂, hpc⟩ => ?_)
  refine WP.seq (WP.mono (pdArgs_ok hL ha hc₂ hs₂) fun t₃ ⟨hc₃, hs₃, pda, hR3, f₃⟩ => ?_)
  refine WP.seq (WP.mono (pd_call v hL hc₃ hs₃ pda) fun t₄ ⟨hc₄, hs₄, f₄, hpd⟩ => ?_)
  -- The slots `r₁` and `r₃`.
  have d1 := slot_disj hL (d := oR1) (by decide)
  have d3 := slot_disj hL (d := oR3) (by decide)
  have d13 : Region.Disjoint ⟨L.B + BitVec.ofNat 64 oR1, 8⟩ ⟨L.B + BitVec.ofNat 64 oR3, 8⟩ :=
    Offset.disjoint _ (.inl (by decide)) (by simp only [oR1]; omega) (by simp only [oR3]; omega)
  have r1₄ : t₄.mem.readW (L.B + BitVec.ofNat 64 oR1) 64 = t.gpr .x0 := by
    rw [f₄.readW (Region.contains_self _ _) (by
        simp only [pdWr, List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl); exacts [d1.2.2.2.1, d1.2.1]) (by decide),
      f₃.readW (Region.contains_self _ _) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl); exacts [d13, d1.2.2.2.2]) (by decide),
      f₂.readW (Region.contains_self _ _) (by
        simp only [pcWr, List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl); exacts [d1.1, d1.2.1]) (by decide)]
    exact hR1
  have r3₄ : t₄.mem.readW (L.B + BitVec.ofNat 64 oR3) 64 = t₂.gpr .x0 := by
    rw [f₄.readW (Region.contains_self _ _) (by
        simp only [pdWr, List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl); exacts [d3.2.2.2.1, d3.2.1]) (by decide)]
    exact hR3
  -- `M`, `n`'s values, and the inputs.
  have hMk : L.k.toNat ≤ 2 ^ 64 := by omega
  have hMR1 : L.M.Disjoint ⟨L.B + BitVec.ofNat 64 oR1, 8⟩ := d1.2.2.1.symm
  have hMR3 : L.M.Disjoint ⟨L.B + BitVec.ofNat 64 oR3, 8⟩ := d3.2.2.1.symm
  have hMP : L.M.Disjoint L.PRE :=
    Offset.disjoint _ (.inl (by simp only [oM, oPre]; omega)) (by simp only [oM]; omega)
      (by simp only [oPre, Lay.pw]; omega)
  have hMB : L.M.Disjoint ⟨L.B, 16⟩ := Offset.disjoint_base _ (by decide) (by simp only [oM]; omega)
  have m₃ : Spec.Rsa.bytesAt t₃.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat =
      Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat := by
    rw [frame_bytesAt f₃ (p := L.B + BitVec.ofNat 64 oM) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl); exacts [hMR3, hMB]) hMk,
      frame_bytesAt f₂ (p := L.B + BitVec.ofNat 64 oM) (by
        simp only [pcWr, List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl); exacts [hMP, hM.2.2.2.2.2.2.2.2.2]) hMk,
      frame_bytesAt f₁ (p := L.B + BitVec.ofNat 64 oM) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r rfl; exact hMR1) hMk]
  have m₄ : Spec.Rsa.bytesAt t₄.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat =
      Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat := by
    rw [frame_bytesAt f₄ (p := L.B + BitVec.ofNat 64 oM) (by
        simp only [pdWr, List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · rw [hOk]; exact hM.1
        · exact hM.2.2.2.2.2.2.2.2.2) hMk, m₃]
  have hpre : Spec.Rsa.wordsAt t₃.mem (L.B + BitVec.ofNat 64 oPre) L.pw =
      Spec.Rsa.wordsAt t₂.mem (L.B + BitVec.ofNat 64 oPre) L.pw := by
    have hP16 : L.PRE.Disjoint ⟨L.B, 16⟩ :=
      Offset.disjoint_base _ (by decide) (by simp only [oPre, Lay.pw]; omega)
    refine frame_wordsAt f₃ (fun r hr => ?_) (by unfold Lay.pw; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (by rw [Nat.mul_comm]; exact d3.1.symm)
    · exact (by rw [Nat.mul_comm]; exact hP16)
  have hn₁ := hc₁.n_bytes hL
  have he₃ := hc₃.e_bytes hL
  have hi₄ := hc₄.inp_bytes hL
  simp only [PcOut, PdOut] at hpc hpd
  rw [hn₁] at hpc
  rw [he₃, m₃] at hpd
  refine WP.mono (tail_ok hL hc₄ hs₄ r1₄ r3₄) fun t' ⟨hc', hax, hout, hM'⟩ => ⟨hc', ?_, ?_, ?_⟩
  all_goals rw [hi₄] at hax hout
  all_goals rw [m₄] at hout
  all_goals
    have h3 : match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) with
        | some _ => (t₂.gpr .x0).setWidth 32 = 1
        | none => (t₂.gpr .x0).setWidth 32 = 0 := by
      cases hcs : Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) <;>
        simp only [hcs] at hpc ⊢ <;> exact hpc.1
    have hl := Proof.Rsa.check_logic (r₁ := t.gpr .x0) (r₂ := t₄.gpr .x0) (r₃ := t₂.gpr .x0)
      (eB := Spec.Rsa.bytesAt m₀ L.e L.el.toNat)
      (mB := Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat)
      (outB := Spec.Rsa.bytesAt t₄.mem L.out L.k.toNat)
      (xB := Spec.Rsa.bytesAt m₀ L.inp L.k.toNat) h3 (fun hsm => by
        obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp hsm
        rw [hws] at hpc
        have := hpd _ (Proof.Rsa.bytesAt_length' _ _ _) (by rw [hws, hpre, hpc.2])
        cases hpo : Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt m₀ L.n L.k.toNat)
            (Spec.Rsa.bytesAt m₀ L.e L.el.toNat)
            (Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat) <;>
          simp only [hpo, Spec.Rsa.written] at this ⊢
        · exact this.1
        · exact this)
  · rw [hax]; exact hl.1
  · rw [hout]; simp only [hl.2]
  · exact hM'

end

end VG.Proof.Rsa.AArch64
