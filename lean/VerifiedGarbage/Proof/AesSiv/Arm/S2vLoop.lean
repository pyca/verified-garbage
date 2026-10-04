import VerifiedGarbage.Proof.AesSiv.Arm.S2vAd
import VerifiedGarbage.Spec.Siv.Contract

/-!
# AES-SIV on ARMv7: S2V over the components of associated data

Untrusted: everything here is checked by Lean. The `N` descriptors at `a`
(8 bytes each: a 32-bit address and a 32-bit length) list the components
in the memory on entry `m₀` (`Ads`). Each iteration of `s2vAds` loads the
next descriptor (`adNext`), computes the CMAC of its component into the
state at `W + 176` (`cmacOf_ok`) and folds it into `D` (`adStep_ok`), so
`D` is S2V's state of the components so far (`AInv`, `aStep_ok`), and of all
of them after the loop (`s2vAds_ok`). The code writes only within `W` but its
first 16 bytes (the synthetic IV) and our caller's saved registers, and the
stack below `sp` (`wR`); S2V's end also writes its result (`oR`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Proof.AesGcm.Arm (ofNat_sub32 z_cmp gpr_subFlags z_subFlags bytesAt_frame covers_left covers_off
  add32_ofNat_assoc eval_eq' eval_ne' Keeps in_off)
open VG.Proof.AesCcm.Arm (blw)
open VG.Proof.MdStream.Arm (wp_ldr)

/-- What the code writes: `W` but the synthetic IV (at `W`) and our caller's
saved registers (at `W + 128`), and the stack below `sp`. -/
abbrev wR (w sp : BitVec 32) : List Region :=
  [⟨State.addr w + BitVec.ofNat 64 16, 112⟩, ⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, blw sp]

/-- What S2V's end writes: `wR` and its result at `W + out`. -/
abbrev oR (w sp : BitVec 32) (out : Nat) : List Region :=
  ⟨State.addr w + BitVec.ofNat 64 out, 16⟩ :: wR w sp

theorem frame_oR {w sp : BitVec 32} {m m' : Mem} (out : Nat) (h : Frame (wR w sp) m m') :
    Frame (oR w sp out) m m' :=
  h.mono fun _ hr => List.mem_cons_of_mem _ hr

/-- With the result at `W + tOff`, S2V's end writes within `wR`. -/
theorem frame_oR_tOff {w sp : BitVec 32} {m m' : Mem} (h : Frame (oR w sp tOff) m m') : Frame (wR w sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 16, 112⟩, by simp, fun _ h => h⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, fun _ h => h⟩
    · exact ⟨blw sp, by simp, fun _ h => h⟩

/-- Word `j` (0: the address, 1: the length) of descriptor `i` at `a`, in `m`. -/
abbrev descW (m : Mem) (a : BitVec 32) (i j : Nat) : BitVec 32 :=
  m.readW (State.addr a + BitVec.ofNat 64 (8 * i + 4 * j)) 32

/-- The `N` descriptors at `a`, readable apart from `W` and the stack, and
the components they list in `m₀`, each a buffer the code may read. -/
structure Ads (w sp a : BitVec 32) (N : Nat) (m₀ : Mem) (s : State) : Prop where
  desc : Covers [⟨State.addr a, 8 * N⟩] (s.rd ++ s.wr)
  fit : a.toNat + 8 * N ≤ 2 ^ 32
  dw : (⟨State.addr a, 8 * N⟩ : Region).Disjoint ⟨State.addr w, 2576⟩
  ds : (blw sp).Disjoint ⟨State.addr a, 8 * N⟩
  comp : ∀ i < N, Buf w sp s (descW m₀ a i 0) (descW m₀ a i 1).toNat

theorem Ads.of_eq {w sp a : BitVec 32} {N : Nat} {m₀ : Mem} {s s' : State} (h : Ads w sp a N m₀ s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Ads w sp a N m₀ s' :=
  { h with desc := by rw [hrd, hwr]; exact h.desc, comp := fun i hi => (h.comp i hi).of_eq hrd hwr }

/-- The `i`-th component, `i < N`. -/
theorem components_getElem (m : Mem) (a : BitVec 32) {N i : Nat} (hi : i < N) :
    (Spec.Siv.components 32 m (State.addr a) N)[i]'(by simp [Spec.Siv.components, Sig.listed, hi]) =
      bytesAt m (State.addr (descW m a i 0)) (descW m a i 1).toNat := by
  simp only [Spec.Siv.components, Sig.listed, List.getElem_map, List.getElem_range, Elem.size, Nat.mul_one,
    descW, State.addr]
  rw [show i * (2 * (32 / 8)) = 8 * i + 4 * 0 by omega, show (32 / 8 : Nat) = 4 from rfl, BitVec.add_assoc,
    BitVec.ofNat_add_ofNat, show 8 * i + 4 * 0 + 4 = 8 * i + 4 by omega]

theorem length_components (m : Mem) (p : Addr) (N : Nat) : (Spec.Siv.components 32 m p N).length = N := by
  simp [Spec.Siv.components, Sig.listed]

theorem s2vAcc_snoc (mac : List Byte → List Byte) (xs : List (List Byte)) (x : List Byte) :
    Spec.Siv.s2vAcc mac (xs ++ [x]) = Spec.Siv.s2vStep mac (Spec.Siv.s2vAcc mac xs) x := by
  simp [Spec.Siv.s2vAcc, List.foldl_append]

/-- Before the `i`-th component (and, for `i = N`, after the last): `D` is
S2V's state of the first `i`, `r8` and `r7` the next descriptor's address
and how many are left. -/
structure AInv (c w sp a : BitVec 32) (R N : Nat) (m₀ : Mem) (σ : State) (i : Nat) (s : State) : Prop where
  env : Env c w sp R s
  ads : Ads w sp a N m₀ s
  r8 : s.gpr .r8 = a + BitVec.ofNat 32 (8 * i)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (N - i)
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  frame : Frame (wR w sp) m₀ s.mem
  acc : bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac m₀ (State.addr c) R) ((Spec.Siv.components 32 m₀ (State.addr a) N).take i)

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp)
include L

omit L in
theorem macR_wR : ∀ r ∈ macR w sp, ∃ r' ∈ wR w sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨blw sp, by simp, fun _ h => h⟩

omit L in
theorem dD_wR : ∀ r ∈ [(⟨State.addr w + BitVec.ofNat 64 dOff, 16⟩ : Region)], ∃ r' ∈ wR w sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩

omit L in
/-- A region apart from `W` and the stack below `sp` is apart from `wR`. -/
theorem dis_wR {r : Region} (hw : r.Disjoint ⟨State.addr w, 2576⟩) (hs : (blw sp).Disjoint r) :
    ∀ r' ∈ wR w sp, r.Disjoint r' := by
  intro r' hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hs.symm

omit L in
/-- `adNext`: the address and the length of descriptor `i`'s component in
`r6` and `r5`. -/
theorem adNext_ok {m₀ : Mem} {a : BitVec 32} {N i : Nat} {s : State} (hA : Ads w sp a N m₀ s) (hi : i < N)
    (hf : Frame (wR w sp) m₀ s.mem) (h8 : s.gpr .r8 = a + BitVec.ofNat 32 (8 * i)) :
    WP isa (.block adNext) s fun s' => s'.gpr .r6 = descW m₀ a i 0 ∧ s'.gpr .r5 = descW m₀ a i 1 ∧
      (∀ r, r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have fit := hA.fit
  have word {j : Nat} (hj : j < 2) :
      State.addr (s.gpr .r8 + BitVec.ofNat 32 (4 * j)) = State.addr a + BitVec.ofNat 64 (8 * i + 4 * j) ∧
      InRegions (s.rd ++ s.wr) (State.addr a + BitVec.ofNat 64 (8 * i + 4 * j)) 4 ∧
      s.mem.readW (State.addr a + BitVec.ofNat 64 (8 * i + 4 * j)) 32 = descW m₀ a i j := by
    refine ⟨by rw [h8, add32_ofNat_assoc]; exact addr_add (by omega),
      in_off hA.desc (by omega) (by omega), ?_⟩
    exact hf.readW (r := ⟨State.addr a + BitVec.ofNat 64 (8 * i + 4 * j), 4⟩) (Region.contains_self _ _)
      (dis_wR (w := w) (sp := sp) (hA.dw.sub_left (Offset.sub_base _ (by omega)))
        (hA.ds.sub_right (Offset.sub_base _ (by omega)))) (by decide)
  obtain ⟨a₀, i₀, v₀⟩ := word (j := 0) (by decide)
  obtain ⟨a₁, i₁, v₁⟩ := word (j := 1) (by decide)
  simp only [Nat.mul_zero, Nat.mul_one] at a₀ i₀ v₀ a₁ i₁ v₁
  rw [show BitVec.ofNat 32 0 = (0 : BitVec 32) from rfl] at a₀
  simp only [adNext]
  refine wp_ldr (a := State.addr a + BitVec.ofNat 64 (8 * i + 0)) (by decide) a₀ i₀ fun s₁ u₁ => ?_
  refine wp_ldr (a := State.addr a + BitVec.ofNat 64 (8 * i + 4)) (by decide)
    (by rw [u₁.other _ (by decide)]; exact a₁) (by rw [u₁.rd, u₁.wr]; exact i₁) fun s₂ u₂ => WP.block_nil ?_
  refine ⟨by rw [u₂.other _ (by decide), u₁.gpr, v₀], by rw [u₂.gpr, u₁.mem, v₁],
    fun r h5 h6 => by rw [u₂.other _ h5, u₁.other _ h6], ⟨by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
      by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩⟩

/-- One iteration of the loop, for the component `i < N`. -/
theorem aStep_ok (hR : R = 10 ∨ R = 12 ∨ R = 14) {a : BitVec 32} {N : Nat} {m₀ : Mem} {σ : State} {i : Nat}
    {s : State} (h : AInv c w sp a R N m₀ σ i s) (hi : i < N) :
    WP isa (.seq (.block adNext) (.seq (cmacOf stOff) (.block adStep))) s fun s' =>
      AInv c w sp a R N m₀ σ (i + 1) s' ∧ s'.z = decide (N - (i + 1) = 0) := by
  have fit := h.ads.fit
  have hN32 : N - i < 2 ^ 32 := by omega
  refine WP.seq (WP.mono (adNext_ok h.ads hi h.frame h.r8) fun s₁ ⟨h6₁, h5₁, g₁, k₁⟩ => ?_)
  have he₁ : Env c w sp R s₁ := h.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have hP : Buf w sp s₁ (descW m₀ a i 0) (descW m₀ a i 1).toNat := (h.ads.comp i hi).of_eq k₁.rd k₁.wr
  refine WP.seq (WP.mono (cmacOf_ok L he₁ hR hP (BitVec.isLt _) h6₁ (by rw [h5₁, BitVec.ofNat_toNat,
    BitVec.setWidth_eq])) fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, out₂⟩ => ?_)
  have h8₂ : s₂.gpr .r8 = a + BitVec.ofNat 32 (8 * i) := by
    rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide), h.r8]
  have h7₂ : s₂.gpr .r7 = BitVec.ofNat 32 (N - i) := by
    rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide), h.r7]
  refine WP.mono (adStep_ok L he₂ (k := N - i) (by omega) hN32 h8₂ h7₂)
    fun s₃ ⟨he₃, rd₃, wr₃, g₃, h8₃, h7₃, hz₃, f₃, out₃⟩ => ?_
  -- The memory.
  have fs := h.frame
  have f₀₂ : Frame (wR w sp) m₀ s₂.mem := fs.trans (by rw [← k₁.mem]; exact f₂.sub macR_wR)
  have f₀₃ : Frame (wR w sp) m₀ s₃.mem := f₀₂.trans (f₃.sub dD_wR)
  have hRb := rounds_le hR
  have dc : ∀ r ∈ wR w sp, (⟨State.addr c, 512⟩ : Region).Disjoint r := dis_wR L.c_w L.stk_c
  have mac₁ : Spec.Siv.ctxMac s₁.mem (State.addr c) R = Spec.Siv.ctxMac m₀ (State.addr c) R := by
    rw [k₁.mem]; exact ctxMac_frame fs dc hRb
  have comp₁ : bytesAt s₁.mem (State.addr (descW m₀ a i 0)) (descW m₀ a i 1).toNat =
      bytesAt m₀ (State.addr (descW m₀ a i 0)) (descW m₀ a i 1).toNat := by
    rw [k₁.mem]; exact bytesAt_frame fs (dis_wR (h.ads.comp i hi).w (h.ads.comp i hi).stk) (by omega)
  have dD₂ : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 dOff) 16 =
      bytesAt s₁.mem (State.addr w + BitVec.ofNat 64 dOff) 16 := by
    refine bytesAt_frame f₂ (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
  have hl := length_components m₀ (State.addr a) N
  refine ⟨⟨he₃, (h.ads.of_eq (by rw [rd₃, rd₂, k₁.rd]) (by rw [wr₃, wr₂, k₁.wr])), ?_, ?_,
    by rw [rd₃, rd₂, k₁.rd, h.rd], by rw [wr₃, wr₂, k₁.wr, h.wr], f₀₃, ?_⟩, ?_⟩
  · rw [h8₃, add32_ofNat_assoc]; congr 2
  · rw [h7₃]; congr 1
  · rw [out₃, out₂, dD₂, mac₁, comp₁, k₁.mem, h.acc, List.take_succ_eq_append_getElem (by omega), s2vAcc_snoc,
      components_getElem m₀ a hi]
    rfl
  · rw [hz₃]; congr 1

/-- S2V over all the components, from S2V's first state in `D`. -/
theorem s2vAds_ok (hR : R = 10 ∨ R = 12 ∨ R = 14) {a : BitVec 32} {N : Nat} {m₀ : Mem} {σ : State}
    {s : State} (h : AInv c w sp a R N m₀ σ 0 s) (hN : N < 2 ^ 32) :
    WP isa s2vAds s (AInv c w sp a R N m₀ σ N) := by
  obtain ⟨s₁, run₁, hz₁, k₁⟩ : ∃ s₁, runBlock isa [.cmp .r7 (imm 0)] s = some s₁ ∧ s₁.z = decide (N = 0) ∧
      s₁.gpr = s.gpr ∧ Keeps s s₁ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp only [z_subFlags, h.r7, Nat.sub_zero]; exact z_cmp hN (by decide)
    · rfl
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨g₁, k₁⟩ := k₁
  have h₁ : AInv c w sp a R N m₀ σ 0 s₁ :=
    ⟨h.env.keep (fun r _ => by rw [g₁]) k₁.sp k₁.rd k₁.wr, h.ads.of_eq k₁.rd k₁.wr, by rw [g₁, h.r8],
      by rw [g₁, h.r7], by rw [k₁.rd, h.rd], by rw [k₁.wr, h.wr], by rw [k₁.mem]; exact h.frame,
      by rw [k₁.mem]; exact h.acc⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : N = 0
  · subst h0
    exact WP.ite true (eval_eq' (by rw [hz₁]; rfl)) (fun _ => WP.block_nil h₁) (fun h => by cases h)
  · refine WP.ite false (eval_eq' (by rw [hz₁]; simp [h0])) (fun h => by cases h) fun _ => ?_
    refine WP.loop (M := isa) (fun (n : Nat) (t : State) => ∃ j, n = N - j ∧ j < N ∧ AInv c w sp a R N m₀ σ j t)
      ?_ (N - 0) s₁ ⟨0, rfl, by omega, h₁⟩
    rintro n t ⟨j, rfl, hj, hI⟩
    refine WP.mono (aStep_ok L hR hI hj) fun t' ⟨hI', hz⟩ => ?_
    have ev : isa.eval .ne t' = some !decide (N - (j + 1) = 0) := eval_ne' hz
    by_cases hz' : N - (j + 1) = 0
    · left
      refine ⟨by rw [ev]; simp [hz'], ?_⟩
      have e : j + 1 = N := by omega
      rw [e] at hI'; exact hI'
    · right
      exact ⟨by rw [ev]; simp [hz'], N - (j + 1), by omega, j + 1, rfl, by omega, hI'⟩

end

end VG.Proof.AesSiv.Arm
