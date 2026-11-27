module

public import VerifiedGarbage.Proof.AesSiv.Long
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.AesGcm.Arm.Env
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesSiv.CtrPart
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesSiv.Words
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Siv.Spec
public import VerifiedGarbage.Spec.Siv.Contract
public import VerifiedGarbage.Proof.AesSiv.Arm.CmacOf
public import VerifiedGarbage.Impl.AesSiv.Arm
import VerifiedGarbage.Proof.CmacAes.Arm.Verified

/-! ### `AesSiv.Arm.FinishShort`, which this module and modules that import it used -/

section

/-! ### `AesSiv.Arm.S2vLoop`, which this module and modules that import it used -/

section

/-! ### `AesSiv.Arm.S2vAd`, which this module and modules that import it used -/

section

/-!
# AES-SIV on ARMv7: a step of S2V over the associated data

Untrusted: everything here is checked by Lean. After the CMAC of a
component into the state at `W + 176` (`cmacOf_ok`), the code doubles `D`
(at `W + 2560`) in place and XORs the CMAC into it, so `D` is then
`dbl(D) ⊕ CMAC(S)` (`Spec.Siv.s2vStep`); then it moves to the next
descriptor and counts one fewer left (`adStep_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Impl.CmacAes.Arm (mov xor4)
open VG.Proof.AesGcm.Arm (ofNat_sub32 z_cmp gpr_subFlags z_subFlags bytesAt_frame covers_left mem_subFlags rd_subFlags wr_subFlags sp_subFlags)
open VG.Proof.CmacAes.Arm (xorBlk xorBlk_ok dbl_wp dblMem dblMem_bytes dblMem_frame)
open VG.Proof.MdStream.Arm (wp_mov op2_reg)

theorem xor4_eq (pb qb cb : Reg) (pd qd cd : Nat) : xor4 pb qb cb pd qd cd = xorBlk .r12 .lr pb qb cb pd qd cd :=
  rfl

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp)
include L

/-- `adStep`: `dbl(D)` in place with the CMAC state XORed into it, then the
descriptor pointer advanced by 8 and the count decremented, `Z` set when
none are left. -/
theorem adStep_ok {s : State} (he : Env c w sp R s) {a : BitVec 32} {k : Nat} (hk : 0 < k) (hk32 : k < 2 ^ 32)
    (h8 : s.gpr .r8 = a) (h7 : s.gpr .r7 = BitVec.ofNat 32 k) :
    WP isa (.block adStep) s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r12 →
        r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.gpr .r8 = a + BitVec.ofNat 32 8 ∧ s'.gpr .r7 = BitVec.ofNat 32 (k - 1) ∧ s'.z = decide (k - 1 = 0) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 dOff, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 dOff) 16 =
        Spec.Siv.xor (Spec.Siv.dbl (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16))
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 stOff) 16) := by
  have ww := L.ww
  rw [adStep, List.cons_append]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  have h6₁ : s₁.gpr .r6 = w := by rw [u₁.gpr, he.r11]
  simp only [List.append_eq, List.append_assoc]
  refine dbl_wp (K := w) h6₁ (src := dOff) (dst := dOff) (by decide) (by decide) (by omega) (by omega)
    (by rw [u₁.rd, u₁.wr]; exact covers_left (he.perm.wC (by decide)))
    (by rw [u₁.wr]; exact he.perm.wC (by decide)) fun s₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
  have h11₂ : s₂.gpr .r11 = w := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u₁.other _ (by decide),
      he.r11]
  rw [xor4_eq]
  refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h11₂]; simp only [dOff]; omega_using [ww])
    (by rw [h11₂]; simp only [stOff]; omega_using [ww]) (by rw [h11₂]; simp only [dOff]; omega_using [ww])
    (by rw [h11₂, rd₂, wr₂, u₁.rd, u₁.wr]; exact covers_left (he.perm.wC (by decide)))
    (by rw [h11₂, rd₂, wr₂, u₁.rd, u₁.wr]; exact covers_left (he.perm.wC (by decide)))
    (by rw [h11₂, wr₂, u₁.wr]; exact he.perm.wC (by decide)) fun s₃ g₃ => ?_
  have h7₃ : s₃.gpr .r7 = BitVec.ofNat 32 k := by
    rw [g₃.gpr _ (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), u₁.other _ (by decide), h7]
  have h8₃ : s₃.gpr .r8 = a := by
    rw [g₃.gpr _ (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), u₁.other _ (by decide), h8]
  have e1 : BitVec.ofNat 32 k - BitVec.ofNat 32 1 = BitVec.ofNat 32 (k - 1) := ofNat_sub32 (by omega_using [hk]) hk32
  refine WP.of_runBlock ⟨_, by arun [h7₃, h8₃], ?_⟩
  have dD : (⟨State.addr w + BitVec.ofNat 64 dOff, 16⟩ : Region).Disjoint
      ⟨State.addr w + BitVec.ofNat 64 stOff, 16⟩ := L.w_w (.inr (by decide)) (by decide) (by decide)
  refine ⟨he.keep (fun r hr => ?_) (by simp [sp_setReg, g₃.sp, sp₂, u₁.sp])
      (by simp [rd_setReg, g₃.rd, rd₂, u₁.rd]) (by simp [wr_setReg, g₃.wr, wr₂, u₁.wr]),
    by simp [rd_setReg, g₃.rd, rd₂, u₁.rd], by simp [wr_setReg, g₃.wr, wr₂, u₁.wr], fun r a0 a1 a2 a3 a4 a6 a7 a8 a12 alr => ?_,
    by simp [gpr_setReg, h8₃], by simp [gpr_setReg, h7₃, e1], ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      simp [gpr_setReg, g₃.gpr _ (by decide : Reg.r9 ≠ .r12) (by decide), g₃.gpr _ (by decide : Reg.r10 ≠ .r12) (by decide),
        g₃.gpr _ (by decide : Reg.r11 ≠ .r12) (by decide), g₂, u₁.other]
  · simp only [gpr_setReg, gpr_subFlags, a7, a8, ite_false, reduceCtorEq]
    rw [g₃.gpr r a12 alr, g₂ r a0 a1 a2 a3 a4 a12, u₁.other r a6]
  · simp only [z_setReg, z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h7₃]
    rw [z_cmp hk32 (by decide)]
    simp only [decide_eq_decide]; omega_using [hk]
  · simp only [mem_setReg, mem_subFlags, g₃.mem, m₂, u₁.mem, h11₂]
    exact (dblMem_frame _ _ _ _).trans (Proof.Cmac.xor4Mem_frame _ _ _ _)
  · simp only [mem_setReg, mem_subFlags, g₃.mem, m₂, u₁.mem, h11₂]
    rw [Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint dD), dblMem_bytes,
      bytesAt_frame (dblMem_frame _ _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dD.symm) (by decide)]
    rfl

end

end VG.Proof.AesSiv.Arm

end

end

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

@[expose] public section

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
  rw [show i * (2 * (32 / 8)) = 8 * i + 4 * 0 by omega_using [], show (32 / 8 : Nat) = 4 from rfl, BitVec.add_assoc,
    BitVec.ofNat_add_ofNat, show 8 * i + 4 * 0 + 4 = 8 * i + 4 by omega_using []]

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
    refine ⟨by rw [h8, add32_ofNat_assoc]; exact addr_add (by omega_using [hi, fit, hj]),
      in_off hA.desc (by omega_using [hi, hj]) (by omega_using [fit]), ?_⟩
    exact hf.readW (r := ⟨State.addr a + BitVec.ofNat 64 (8 * i + 4 * j), 4⟩) (Region.contains_self _ _)
      (dis_wR (w := w) (sp := sp) (hA.dw.sub_left (Offset.sub_base _ (by omega_using [hi, hj])))
        (hA.ds.sub_right (Offset.sub_base _ (by omega_using [hi, hj])))) (by decide)
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
  have hN32 : N - i < 2 ^ 32 := by omega_using [fit]
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
  refine WP.mono (adStep_ok L he₂ (k := N - i) (by omega_using [hi]) hN32 h8₂ h7₂)
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
    rw [k₁.mem]; exact bytesAt_frame fs (dis_wR (h.ads.comp i hi).w (h.ads.comp i hi).stk) (by omega_using [])
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
  · rw [out₃, out₂, dD₂, mac₁, comp₁, k₁.mem, h.acc, List.take_succ_eq_append_getElem (by omega_using [hi, hl]), s2vAcc_snoc,
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
      ?_ (N - 0) s₁ ⟨0, rfl, by omega_using [h0], h₁⟩
    rintro n t ⟨j, rfl, hj, hI⟩
    refine WP.mono (aStep_ok L hR hI hj) fun t' ⟨hI', hz⟩ => ?_
    have ev : isa.eval .ne t' = some !decide (N - (j + 1) = 0) := eval_ne' hz
    by_cases hz' : N - (j + 1) = 0
    · left
      refine ⟨by rw [ev]; simp [hz'], ?_⟩
      have e : j + 1 = N := by omega_using [hj, hz']
      rw [e] at hI'; exact hI'
    · right
      exact ⟨by rw [ev]; simp [hz'], N - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hz'], hI'⟩

end

end VG.Proof.AesSiv.Arm

end

end

/-!
# AES-SIV on ARMv7: finishing S2V with a string shorter than a block

Untrusted: everything here is checked by Lean. For a last string `P` of
`L < 16` bytes, `shortTail` copies `P` onto the zeroed tail at `W + 32` and
puts `0x80` after it, so the tail is `pad(P)`, doubles `D` into `W + 192`
and XORs it into the tail (`shortTail_ok`); `shortMac out` finalizes the
tail, one complete block, from a zero state at `W + out`
(`shortMac_ok`), which is S2V's end (`Siv.s2vFinish_short`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI copyLoop)
open VG.Impl.CmacAes.Arm (mov xor4)
open VG.Proof.AesGcm.Arm (z_cmp gpr_subFlags z_subFlags mem_subFlags rd_subFlags wr_subFlags sp_subFlags
  bytesAt_frame covers_left covers_off eval_eq' Keeps LoopPre LoopOut copyLoop_ok in_off)
open VG.Proof.CmacAes.Arm (xorBlk xorBlk_ok dbl_wp dblMem dblMem_bytes dblMem_frame b80)
open VG.Proof.MdStream.Arm (wp_mov wp_add wp_strb op2_imm op2_reg)
open VG.Proof.AesSiv (chain_blocks_nil)
open VG.Proof.AesCcm.Arm (blw)

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp)
include L

/-- The tail after `shortTail`: `pad(P) ⊕ dbl(D)`. -/
theorem shortTail_ok {s : State} (he : Env c w sp R s) {P : BitVec 32} {n : Nat} (hP : Buf w sp s P n)
    (hn : n < 16) (h6 : s.gpr .r6 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa shortTail s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r6 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (wR w sp) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 tailOff) 16 =
        Spec.Cmac.xor (Spec.Siv.pad (bytesAt s.mem (State.addr P) n))
          (Spec.Siv.dbl (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16)) := by
  have ww := L.ww
  obtain eT := L.wA (d := tailOff) (by decide)
  obtain hlen : (bytesAt s.mem (State.addr P) n).length = n := Proof.Cmac.bytesAt_length _ _ _
  -- The tail zeroed, and the arguments of the copy.
  rw [shortTail]
  refine WP.seq (zero16_ok L he (d := tailOff) (by decide) fun s₁ g₁ m₁ rd₁ wr₁ sp₁ => ?_)
  obtain ⟨s₂, run₂, h1₂, h2₂, h3₂, hz₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [mov .r1 .r6, addI .r2 .r11 tailOff,
      mov .r3 .r5, .cmp .r5 (imm 0)] s₁ = some s₂ ∧ s₂.gpr .r1 = P ∧ s₂.gpr .r2 = w + BitVec.ofNat 32 tailOff ∧
      s₂.gpr .r3 = BitVec.ofNat 32 n ∧ s₂.z = decide (n = 0) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    obtain h6₁ : s₁.gpr .r6 = P := by rw [g₁ _ (by decide), h6]
    obtain h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 n := by rw [g₁ _ (by decide), h5]
    obtain h11₁ : s₁.gpr .r11 = w := by rw [g₁ _ (by decide), he.r11]
    refine ⟨_, by simp only [mov, tailOff]; arun [h11₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h6₁]
    · simp [gpr_setReg, h11₁]
    · simp [gpr_setReg, h5₁]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5₁]
      exact z_cmp (by omega_arith) (by decide)
    · intro r a b d; simp [gpr_setReg, a, b, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  -- The copy, if any: the tail is `P` followed by zeros.
  obtain pmem : bytesAt s₁.mem (State.addr P) n = bytesAt s.mem (State.addr P) n := by
    rw [m₁]
    exact bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.fit; omega_arith)
  obtain copied : WP isa (.ite .eq (.block []) copyLoop) s₂ fun s₃ =>
      s₃.mem = writeBytes s₁.mem (State.addr w + BitVec.ofNat 64 tailOff) (bytesAt s.mem (State.addr P) n) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₃.gpr r = s₂.gpr r) ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr ∧ s₃.sp = s₂.sp := by
    by_cases h0 : n = 0
    · subst h0
      refine WP.ite true (eval_eq' (by rw [hz₂]; rfl)) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨?_, fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
      rw [k₂.mem]; simp [bytesAt, writeBytes_nil]
    · refine WP.ite false (eval_eq' (by rw [hz₂]; simp [h0])) (fun h => by cases h) fun _ => ?_
      obtain lp : LoopPre s₂ P (w + BitVec.ofNat 32 tailOff) n :=
        ⟨h1₂, h2₂, h3₂, by omega_arith, by omega_arith, hP.fit, by rw [L.wN (by decide)]; simp only [tailOff]; omega_arith,
          by rw [k₂.rd, k₂.wr, rd₁, wr₁]; exact hP.rd,
          by rw [eT, k₂.wr, wr₁]; exact he.perm.wC (by simp only [tailOff]; omega_arith),
          by rw [eT]; exact hP.w.sub_right (Lay.wSub (by simp only [tailOff]; omega_arith))⟩
      refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨m₃, lo⟩ => ?_
      refine ⟨by rw [m₃, k₂.mem, eT, pmem], lo.other, lo.rd, lo.wr, lo.sp⟩
  refine WP.seq (WP.mono copied fun s₃ ⟨m₃, g₃, rd₃, wr₃, sp₃⟩ => ?_)
  -- `0x80` after `P`, and `r6 := W`.
  obtain h11₃ : s₃.gpr .r11 = w := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide),
      g₁ _ (by decide), he.r11]
  obtain h5₃ : s₃.gpr .r5 = BitVec.ofNat 32 n := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide),
      g₁ _ (by decide), h5]
  refine wp_add (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₅ u₅ => ?_
  obtain a80 : State.addr (s₅.gpr .r2 + BitVec.ofNat 32 tailOff) =
      State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 n := by
    rw [u₅.other _ (by decide), u₄.gpr, h11₃, h5₃, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      L.wA (by simp only [tailOff]; omega_arith),
      Offset.add_add, Nat.add_comm]
  refine wp_strb (by decide) a80 (by
      rw [u₅.wr, u₄.wr, wr₃, k₂.wr, wr₁, Offset.add_add]
      exact in_off he.perm.w (by simp only [tailOff]; omega_arith) (by decide)) fun s₆ v₆ => ?_
  refine wp_mov (op2_reg _ _) fun s₇ u₇ => ?_
  obtain h6₇ : s₇.gpr .r6 = w := by rw [u₇.gpr, v₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), h11₃]
  obtain h11₇ : s₇.gpr .r11 = w := by
    rw [u₇.other _ (by decide), v₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), h11₃]
  obtain hrw : s₇.rd ++ s₇.wr = s.rd ++ s.wr := by
    rw [u₇.rd, u₇.wr, v₆.rd, v₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, rd₃, wr₃, k₂.rd, k₂.wr, rd₁, wr₁]
  obtain hw₇ : s₇.wr = s.wr := by rw [u₇.wr, v₆.wr, u₅.wr, u₄.wr, wr₃, k₂.wr, wr₁]
  obtain m₇ : s₇.mem = (writeBytes (Proof.Cmac.zero4 s.mem (State.addr w + BitVec.ofNat 64 tailOff))
      (State.addr w + BitVec.ofNat 64 tailOff) (bytesAt s.mem (State.addr P) n)).writeW
      (State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 n) (0x80 : Byte) := by
    obtain b : (BitVec.setWidth 8 (BitVec.ofNat 32 128) : Byte) = 0x80 := by decide
    rw [u₇.mem, v₆.mem, u₅.gpr, u₅.mem, u₄.mem, m₃, m₁, b]
  refine dbl_wp (K := w) h6₇ (src := dOff) (dst := dbOff) (by decide) (by decide) (by simp only [dOff]; omega_arith)
    (by simp only [dbOff]; omega_arith) (by rw [hrw]; exact covers_left (he.perm.wC (by decide)))
    (by rw [hw₇]; exact he.perm.wC (by decide)) fun s₈ g₈ m₈ rd₈ wr₈ sp₈ => ?_
  obtain h11₈ : s₈.gpr .r11 = w := by
    rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h11₇]
  rw [xor4_eq]
  refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h11₈]; simp only [tailOff]; omega_arith)
    (by rw [h11₈]; simp only [dbOff]; omega_arith) (by rw [h11₈]; simp only [tailOff]; omega_arith)
    (by rw [h11₈, rd₈, wr₈, hrw]; exact covers_left (he.perm.wC (by decide)))
    (by rw [h11₈, rd₈, wr₈, hrw]; exact covers_left (he.perm.wC (by decide)))
    (by rw [h11₈, wr₈, hw₇]; exact he.perm.wC (by decide)) fun s₉ g₉ => WP.block_nil ?_
  -- The registers.
  obtain gT : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r6 → r ≠ .r12 → r ≠ .lr →
      s₉.gpr r = s.gpr r := fun r a0 a1 a2 a3 a4 a6 a12 alr => by
    rw [g₉.gpr r a12 alr, g₈ r a0 a1 a2 a3 a4 a12, u₇.other r a6, v₆.gpr, u₅.other r a12, u₄.other r a2,
      g₃ r a0 a1 a2 a3 a12, g₂ r a1 a2 a3, g₁ r a12]
  obtain rd₉ : s₉.rd = s.rd := by rw [g₉.rd, rd₈, u₇.rd, v₆.rd, u₅.rd, u₄.rd, rd₃, k₂.rd, rd₁]
  obtain wr₉ : s₉.wr = s.wr := by rw [g₉.wr, wr₈, hw₇]
  obtain sp₉ : s₉.sp = s.sp := by rw [g₉.sp, sp₈, u₇.sp, v₆.sp, u₅.sp, u₄.sp, sp₃, k₂.sp, sp₁]
  -- The memory.
  obtain dTB : (⟨State.addr w + BitVec.ofNat 64 tailOff, 16⟩ : Region).Disjoint
      ⟨State.addr w + BitVec.ofNat 64 dbOff, 16⟩ := L.w_w (.inl (by decide)) (by decide) (by decide)
  obtain m₉ : s₉.mem = Proof.Cmac.xor4Mem (dblMem s₇.mem (State.addr w) dOff dbOff)
      (State.addr w + BitVec.ofNat 64 tailOff) (State.addr w + BitVec.ofNat 64 tailOff)
      (State.addr w + BitVec.ofNat 64 dbOff) := by rw [g₉.mem, m₈, h11₈]
  obtain f₇ : Frame [⟨State.addr w + BitVec.ofNat 64 tailOff, 16⟩] s.mem s₇.mem := by
    rw [m₇]
    refine ((Proof.Cmac.frame_store4 _ _ _ _ _).trans (writeBytes_frame _ _ _ ?_)).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
    rw [hlen]
    simpa using Offset.contains_base (State.addr w + BitVec.ofNat 64 tailOff) (d := 0) (n := n) (k := 16)
      (by omega_arith) (by decide)
  obtain f₉ : Frame [⟨State.addr w + BitVec.ofNat 64 tailOff, 16⟩, ⟨State.addr w + BitVec.ofNat 64 dbOff, 16⟩]
      s.mem s₉.mem := by
    rw [m₉]
    exact ((f₇.mono (by simp)).trans ((dblMem_frame _ _ _ _).mono (by simp))).trans
      ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))
  refine ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact gT _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)) sp₉ rd₉ wr₉, rd₉, wr₉, fun r hr h4 h6 hlr => ?_,
    f₉.sub fun r hr => ?_, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact gT r a.1 a.2.1 a.2.2.1 a.2.2.2.1 h4 h6 a.2.2.2.2 hlr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · have dD : (⟨State.addr w + BitVec.ofNat 64 dOff, 16⟩ : Region).Disjoint
        ⟨State.addr w + BitVec.ofNat 64 tailOff, 16⟩ := L.w_w (.inr (by decide)) (by decide) (by decide)
    obtain pad := Proof.Cmac.padded_bytes (Proof.Cmac.zero4 s.mem (State.addr w + BitVec.ofNat 64 tailOff))
      (State.addr w + BitVec.ofNat 64 tailOff) (bytesAt s.mem (State.addr P) n) (by rw [hlen]; exact hn)
      (Proof.Cmac.zero4_bytes _ _)
    rw [hlen] at pad
    rw [m₉, Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint dTB),
      dblMem_bytes, bytesAt_frame (dblMem_frame _ _ _ _) (p := State.addr w + BitVec.ofNat 64 tailOff) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dTB) (by omega_arith),
      bytesAt_frame f₇ (p := State.addr w + BitVec.ofNat 64 dOff) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dD) (by omega_arith),
      m₇, pad, Spec.Siv.pad, hlen, Spec.Siv.dbl, show 16 - n - 1 = 15 - n by omega_arith]
    rfl

omit L in
/-- The CMAC of one block. -/
theorem macWith_one (ciph : Spec.Cmac.Cipher) (k1 k2 T : List Byte) (hT : T.length = 16) :
    Spec.Cmac.macWith ciph 16 k1 k2 T = ciph (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 k1 k2 T) (Spec.Cmac.zeros 16)) := by
  rw [Siv.macWith_chained, hT, show Spec.Cmac.chainedLen 16 16 = 0 from rfl, List.take_zero, List.drop_zero,
    chain_blocks_nil, Proof.Cmac.xor_comm]

/-- `shortArgs out`: the state at `W + out` zeroed, and the arguments of
`vg_cmac_aes_finalize` of the tail, one complete block. -/
theorem shortArgs_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {out : Nat}
    (hout : out = 0 ∨ out = tOff) :
    WP isa (.block (shortArgs out)) s fun s₂ => Env c w sp R s₂ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.mem = Proof.Cmac.zero4 s.mem (State.addr w + BitVec.ofNat 64 out) ∧
      FArgs s₂ c (w + BitVec.ofNat 32 out) (w + BitVec.ofNat 32 tailOff) (w + BitVec.ofNat 32 256) 16 R := by
  have ww := L.ww
  obtain ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  obtain hoT : out + 16 ≤ tailOff ∨ tailOff + 32 ≤ out := by rcases hout with rfl | rfl <;> decide
  obtain eo : encodable (BitVec.ofNat 32 out) = true := by rcases hout with rfl | rfl <;> decide
  obtain eT := L.wA (d := tailOff) (by decide)
  rw [shortArgs, List.append_assoc]
  refine zero16_ok L he (d := out) (by omega_arith) fun s₁ g₁ m₁ rd₁ wr₁ sp₁ => ?_
  obtain h11₁ : s₁.gpr .r11 = w := by rw [g₁ _ (by decide), he.r11]
  obtain he₁ : Env c w sp R s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide)) sp₁ rd₁ wr₁
  obtain ⟨s₂, run₂, he₂, g₂, k₂, F⟩ : ∃ s₂, runBlock isa (macArgs out ++ [addI .r3 .r11 tailOff, .mov .r12 (imm 16)])
      s₁ = some s₂ ∧ Env c w sp R s₂ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ ∧
      FArgs s₂ c (w + BitVec.ofNat 32 out) (w + BitVec.ofNat 32 tailOff) (w + BitVec.ofNat 32 256) 16 R := by
    refine ⟨_, by simp only [macArgs, csOff, tailOff, mov]; arun [he₁.r9, he₁.r10, he₁.r11, eo], ?_⟩
    refine ⟨he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
      fun r a b c' d e f => by simp [gpr_setReg, a, b, c', d, e, f], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    refine fargs_of L ?_ hR (st := out) (by omega_arith) (n := 16) (by decide)
      (by rw [L.wN (by decide)]; simp only [tailOff]; omega_arith) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
    · rw [eT]; exact L.w_w (by omega_arith) (by decide) (by omega_arith)
    · rw [eT]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [eT]; exact L.stk_w' (by decide)
    · rw [eT]; exact covers_left (he₁.perm.wC (by decide))
    · simp [gpr_setReg, he₁.r10]
    · simp [gpr_setReg, he₁.r9]
    · simp [gpr_setReg, he₁.r11]
    · simp [gpr_setReg, he₁.r11]
    · simp [gpr_setReg]
    · simp [gpr_setReg, he₁.r11]
  exact WP.of_runBlock ⟨s₂, run₂, he₂, fun r a b c' d e f => by rw [g₂ r a b c' d e f, g₁ r e],
    by rw [k₂.rd, rd₁], by rw [k₂.wr, wr₁], by rw [k₂.mem, m₁], F⟩

/-- `shortMac out`: the CMAC of the tail, one block, at `W + out`. -/
theorem shortMac_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {out : Nat}
    (hout : out = 0 ∨ out = tOff) :
    WP isa (shortMac out) s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧ Frame (oR w sp out) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 out) 16 =
        Spec.Siv.ctxMac s.mem (State.addr c) R (bytesAt s.mem (State.addr w + BitVec.ofNat 64 tailOff) 16) := by
  have ww := L.ww
  obtain ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  obtain hoT : out + 16 ≤ tailOff ∨ tailOff + 32 ≤ out := by rcases hout with rfl | rfl <;> decide
  obtain eo : encodable (BitVec.ofNat 32 out) = true := by rcases hout with rfl | rfl <;> decide
  obtain eT := L.wA (d := tailOff) (by decide)
  obtain eO := L.wA (d := out) (by omega_arith)
  rw [shortMac]
  refine WP.seq (WP.mono (shortArgs_ok L he hR hout) fun s₂ ⟨he₂, g₂, rd₂, wr₂, m₂, F⟩ => ?_)
  refine WP.mono (fin_call F) fun s₃ h₃ => ?_
  obtain hb := blw16_eq (s := s₂) he₂.sp
  have f₃ := h₃.frame
  rw [eO, L.wA (d := 256) (by decide), hb] at f₃
  obtain f₁ : Frame (oR w sp out) s.mem s₂.mem := by
    rw [m₂]
    exact (Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  obtain f₃' : Frame (oR w sp out) s₂.mem s₃.mem := by
    exact f₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨blw sp, by simp, fun _ h => h⟩
  obtain fT := f₁.trans f₃'
  refine ⟨he₂.of_saved h₃.saved h₃.sp h₃.rd h₃.wr, by rw [h₃.rd, rd₂], by rw [h₃.wr, wr₂],
    fun r hr hlr => ?_, fT, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h₃.saved r hr hlr, g₂ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr]
  · -- What the call reads is as on entry.
    obtain f₂ : Frame [⟨State.addr w + BitVec.ofNat 64 out, 16⟩] s.mem s₂.mem := by
      rw [m₂]; exact Proof.Cmac.frame_store4 _ _ _ _ _
    obtain hRb := rounds_le hR
    have cK {d k : Nat} (hd : d + k ≤ 512) :
        bytesAt s₂.mem (State.addr c + BitVec.ofNat 64 d) k = bytesAt s.mem (State.addr c + BitVec.ofNat 64 d) k :=
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.c_w' hd (by omega_arith)) (by omega_arith)
    obtain sch := cK (d := 0) (k := 16 * (R + 1)) (by omega_arith)
    rw [BitVec.add_zero] at sch
    obtain tl : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 tailOff) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 tailOff) 16 :=
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega_arith) (by decide) (by omega_arith)) (by decide)
    obtain z : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
      rw [m₂, Proof.Cmac.zero4_bytes]
    have out₃ := h₃.out
    rw [eO, eT, sch, cK (d := 240) (k := 16) (by decide), cK (d := 256) (k := 16) (by decide), tl, z] at out₃
    rw [out₃, Spec.Siv.ctxMac, Spec.Siv.schedCiph, macWith_one _ _ _ _ (Proof.Cmac.bytesAt_length _ _ _)]
    rfl

/-- S2V's end for a string `P` shorter than a block, into `W + out`. -/
theorem short_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {n : Nat}
    (hP : Buf w sp s P n) (hn : n < 16) (h6 : s.gpr .r6 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) {out : Nat}
    (hout : out = 0 ∨ out = tOff) :
    WP isa (.seq shortTail (shortMac out)) s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r6 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (oR w sp out) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 out) 16 =
        Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (State.addr c) R)
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16) (bytesAt s.mem (State.addr P) n) := by
  refine WP.seq (WP.mono (shortTail_ok L he hP hn h6 h5) fun s₁ ⟨he₁, rd₁, wr₁, g₁, f₁, t₁⟩ => ?_)
  refine WP.mono (shortMac_ok L he₁ hR hout) fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, o₂⟩ => ?_
  refine ⟨he₂, by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun r hr h4 h6 hlr => by rw [g₂ r hr hlr, g₁ r hr h4 h6 hlr],
    (frame_oR out f₁).trans f₂, ?_⟩
  rw [o₂, t₁, ctxMac_frame f₁ (dis_wR L.c_w L.stk_c) (rounds_le hR),
    Siv.s2vFinish_short _ _ (by rw [Proof.Cmac.bytesAt_length]; exact hn), Siv.xor_eq, Proof.Cmac.xor_comm]

end

end VG.Proof.AesSiv.Arm

end

end

/-!
# AES-SIV on ARMv7: finishing S2V with a string of a block or more

Untrusted: everything here is checked by Lean. For a last string `P` of
`L ≥ 16` bytes, `longTail` computes `16 k` (`kBlock_ok`, `kOf`), copies the
last `T = L − 16 k` bytes of `P` to the tail at `W + 32` and XORs `D` into
its last 16 (`tailCopy_ok`, `xorend_mem4`); `longMac out` chains the `k`
blocks of `P`, then the first `j` blocks of the tail, and finalizes the rest
(`longMac_ok`), which is S2V's end (`long_spec`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI copyLoop)
open VG.Impl.CmacAes.Arm (mov xor4)
open VG.Proof.AesGcm.Arm (z_cmp gpr_subFlags z_subFlags mem_subFlags rd_subFlags wr_subFlags sp_subFlags
  bytesAt_frame covers_left covers_off eval_eq' Keeps LoopPre LoopOut copyLoop_ok in_off ofNat_sub32 shr4 addr_toNat
  add32_ofNat_assoc)
open VG.Proof.CmacAes.Arm (xorBlk xorBlk_ok)
open VG.Proof.MdStream.Arm (wp_sub wp_add op2_reg)
open VG.Proof.AesCcm.Arm (blw UArgs UPost upd_call)
open VG.Proof.CmacAes.Stream.Arm (blw16)
open VG.Proof.AesSiv (kOf jOf kOf_lt kOf_ge kOf_tail jOf_rest jOf_le take_bytesAt drop_bytesAt long_spec)

/-- XORing `D` into the last 16 of `T` bytes, a word at a time. -/
theorem xorend_mem4 (m : Mem) {B Q : Addr} {T : Nat} (hT : 16 ≤ T) (hw : B.toNat + T ≤ 2 ^ 64)
    (hd : (⟨B, T⟩ : Region).Disjoint ⟨Q, 16⟩) :
    bytesAt (Proof.Cmac.xor4Mem m (B + BitVec.ofNat 64 (T - 16)) (B + BitVec.ofNat 64 (T - 16)) Q) B T =
      Spec.Siv.xorend (bytesAt m B T) (bytesAt m Q 16) := by
  obtain hc : Region.Sub ⟨B + BitVec.ofNat 64 (T - 16), 16⟩ ⟨B, T⟩ := Offset.sub_base B (by omega_arith)
  obtain e : T = (T - 16) + 16 := by omega_arith
  obtain hs := Proof.Cmac.Stream.bytesAt_append (Proof.Cmac.xor4Mem m (B + BitVec.ofNat 64 (T - 16))
    (B + BitVec.ofNat 64 (T - 16)) Q) B (T - 16) 16
  rw [← e] at hs
  rw [hs, Spec.Siv.xorend, Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length]
  obtain tk := take_bytesAt m B (a := T - 16) (b := 16)
  obtain dr := drop_bytesAt m B (a := T - 16) (b := 16)
  rw [← e] at tk dr
  rw [tk, dr, Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint B (by omega_arith) (by omega_arith)) (by omega_arith),
    Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (hd.sub_left hc)),
    Siv.xor_eq]

/-- `kBlock`: `16 k` in `r4`. -/
theorem kBlock_ok {s : State} {n : Nat} (h16 : 16 ≤ n) (hn : n < 2 ^ 32) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa kBlock s fun s' => s'.gpr .r4 = BitVec.ofNat 32 (16 * kOf n) ∧
      (∀ r, r ≠ .r4 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain e1 : BitVec.ofNat 32 n - 1#32 = BitVec.ofNat 32 (n - 1) := ofNat_sub32 (by omega_arith) hn
  obtain e2 : BitVec.ofNat 32 (n - 1) >>> 4 = BitVec.ofNat 32 ((n - 1) / 16) := shr4 (by omega_arith)
  obtain ⟨s₁, run₁, h12₁, h4₁, hz₁, g₁, k₁⟩ : ∃ s₁, runBlock isa [.dp .sub .r12 .r5 (imm 1),
      .mov .r12 (.shifted .r12 .lsr 4), .mov .r4 (imm 0), .cmp .r12 (imm 0)] s = some s₁ ∧
      s₁.gpr .r12 = BitVec.ofNat 32 ((n - 1) / 16) ∧ s₁.gpr .r4 = 0 ∧ s₁.z = decide ((n - 1) / 16 = 0) ∧
      (∀ r, r ≠ .r4 → r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [h5], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h5, e1, e2]
    · simp [gpr_setReg]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, e1, e2]
      exact z_cmp (by omega_arith) (by decide)
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : (n - 1) / 16 = 0
  · refine WP.ite true (eval_eq' (by rw [hz₁]; simp [h0])) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨by rw [h4₁, kOf_lt (by omega_arith)]; rfl, g₁, k₁⟩
  · refine WP.ite false (eval_eq' (by rw [hz₁]; simp [h0])) (fun h => by cases h) fun _ => ?_
    obtain e3 : BitVec.ofNat 32 ((n - 1) / 16) - 1#32 = BitVec.ofNat 32 ((n - 1) / 16 - 1) :=
      ofNat_sub32 (by omega_arith) (by omega_arith)
    obtain e4 : BitVec.ofNat 32 ((n - 1) / 16 - 1) <<< 4 = BitVec.ofNat 32 (16 * ((n - 1) / 16 - 1)) :=
      shl4 (by omega_arith)
    refine WP.of_runBlock ⟨_, by arun [h12₁], ?_, ?_, ?_⟩
    · simp [gpr_setReg, h12₁, e3, e4, kOf_ge (show ¬ n < 17 by omega_arith)]
    · intro r a b; simp [gpr_setReg, a, b, g₁ r a b]
    · exact ⟨k₁.mem, k₁.rd, k₁.wr, k₁.sp⟩

theorem bytesAt_writeBytes_self (m : Mem) (p : Addr) (xs : List Byte) (hn : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p xs.length = xs := by
  rw [Proof.AesCcm.bytesAt_writeBytes_base m p xs (Nat.le_refl _) hn,
    List.drop_eq_nil_of_le (by rw [Proof.Cmac.bytesAt_length]), List.append_nil]

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp)
include L

/-- `longTail`: `16 k` in `r4`, and the tail `P[16k..] xorend D` at `W + 32`. -/
theorem longTail_ok {s : State} (he : Env c w sp R s) {P : BitVec 32} {n : Nat} (hP : Buf w sp s P n)
    (h16 : 16 ≤ n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa longTail s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.gpr .r4 = BitVec.ofNat 32 (16 * kOf n) ∧ Frame (wR w sp) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 tailOff) (n - 16 * kOf n) =
        Spec.Siv.xorend ((bytesAt s.mem (State.addr P) n).drop (16 * kOf n))
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16) := by
  have ww := L.ww
  obtain hT := kOf_tail h16
  generalize hK : 16 * kOf n = K at hT ⊢
  obtain eT := L.wA (d := tailOff) (by decide)
  refine WP.seq (WP.mono (kBlock_ok h16 hn h5) fun s₁ ⟨h4₁, g₁, k₁⟩ => ?_)
  rw [hK] at h4₁
  obtain he₁ : Env c w sp R s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  obtain h6₁ : s₁.gpr .r6 = P := by rw [g₁ _ (by decide) (by decide), h6]
  obtain h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 n := by rw [g₁ _ (by decide) (by decide), h5]
  obtain hq : Buf w sp s₁ (P + BitVec.ofNat 32 K) (n - K) :=
    (hP.sub (j := K) (k := n - K) (by omega_arith) (by omega_arith)).of_eq k₁.rd k₁.wr
  obtain eK : BitVec.ofNat 32 n - BitVec.ofNat 32 K = BitVec.ofNat 32 (n - K) := ofNat_sub32 (by omega_arith) hn
  rw [tailCopy]
  refine WP.seq (WP.of_runBlock ⟨_, by simp only [tailOff]; arun [h6₁, h5₁, h4₁, he₁.r11], ?_⟩)
  -- The copy of the last `T` bytes.
  refine WP.seq (WP.mono (copyLoop_ok (S := P + BitVec.ofNat 32 K) (D := w + BitVec.ofNat 32 tailOff)
      (n := n - K) _ ⟨by simp [gpr_setReg, h6₁, h4₁], by simp [gpr_setReg, he₁.r11],
      by simp [gpr_setReg, h5₁, h4₁, eK], by omega_arith, by omega_arith, hq.fit,
      by rw [L.wN (by decide)]; simp only [tailOff]; omega_arith, hq.rd,
      by rw [eT]; exact he₁.perm.wC (by simp only [tailOff]; omega_arith),
      by rw [eT]; exact hq.w.sub_right (Lay.wSub (by simp only [tailOff]; omega_arith))⟩) fun s₃ ⟨m₃, lo⟩ => ?_)
  obtain h11₃ : s₃.gpr .r11 = w := by
    rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [gpr_setReg, he₁.r11]
  obtain h5₃ : s₃.gpr .r5 = BitVec.ofNat 32 n := by
    rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [gpr_setReg, h5₁]
  obtain h4₃ : s₃.gpr .r4 = BitVec.ofNat 32 K := by
    rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [gpr_setReg, h4₁]
  refine wp_sub (op2_reg _ _) fun s₄ u₄ => wp_add (op2_reg _ _) fun s₅ u₅ => ?_
  obtain h0₅ : s₅.gpr .r0 = w + BitVec.ofNat 32 (n - K) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₄.gpr, h11₃, h5₃, h4₃, eK]
  obtain h11₅ : s₅.gpr .r11 = w := by rw [u₅.other _ (by decide), u₄.other _ (by decide), h11₃]
  obtain eA : State.addr (w + BitVec.ofNat 32 (n - K)) + BitVec.ofNat 64 16 =
      State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 (n - K - 16) := by
    rw [L.wA (by omega_arith), Offset.add_add, Offset.add_add]; congr 2; simp only [tailOff]; omega_arith
  obtain hrw : s₅.rd ++ s₅.wr = s.rd ++ s.wr := by
    rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, lo.rd, lo.wr]; simp only [rd_setReg, wr_setReg, k₁.rd, k₁.wr]
  obtain hw₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, lo.wr]; simp only [wr_setReg, k₁.wr]
  rw [xor4_eq]
  refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h0₅, L.wN (by omega_arith)]; omega_arith)
    (by rw [h11₅]; simp only [dOff]; omega_arith) (by rw [h0₅, L.wN (by omega_arith)]; omega_arith)
    (by rw [h0₅, eA, hrw, Offset.add_add]; exact covers_left (he.perm.wC (by simp only [tailOff]; omega_arith)))
    (by rw [h11₅, hrw]; exact covers_left (he.perm.wC (by decide)))
    (by rw [h0₅, eA, hw₅, Offset.add_add]; exact he.perm.wC (by simp only [tailOff]; omega_arith)) fun s₆ g₆ => WP.block_nil ?_
  obtain gT : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr →
      s₆.gpr r = s.gpr r := fun r a0 a1 a2 a3 a4 a12 alr => by
    rw [g₆.gpr r a12 alr, u₅.other r a0, u₄.other r a0, lo.other r a0 a1 a2 a3 a12]
    simp only [gpr_setReg, a1, a2, a3, ite_false, reduceCtorEq]
    rw [g₁ r a4 a12]
  obtain rd₆ : s₆.rd = s.rd := by
    rw [g₆.rd, u₅.rd, u₄.rd, lo.rd]; simp only [rd_setReg, k₁.rd]
  obtain wr₆ : s₆.wr = s.wr := by rw [g₆.wr, hw₅]
  obtain sp₆ : s₆.sp = s.sp := by
    rw [g₆.sp, u₅.sp, u₄.sp, lo.sp]; simp only [sp_setReg, k₁.sp]
  obtain aP : State.addr (P + BitVec.ofNat 32 K) = State.addr P + BitVec.ofNat 64 K := hP.addr (by omega_arith)
  obtain m₅ : s₅.mem = writeBytes s.mem (State.addr w + BitVec.ofNat 64 tailOff)
      (bytesAt s.mem (State.addr P + BitVec.ofNat 64 K) (n - K)) := by
    rw [u₅.mem, u₄.mem, m₃, eT, aP]; simp only [mem_setReg, k₁.mem]
  obtain hlx : (bytesAt s.mem (State.addr P + BitVec.ofNat 64 K) (n - K)).length = n - K :=
    Proof.Cmac.bytesAt_length _ _ _
  obtain fW : Frame [⟨State.addr w + BitVec.ofNat 64 tailOff, n - K⟩] s.mem s₅.mem := by
    rw [m₅]; exact writeBytes_frame _ _ _ (by rw [hlx]; exact Region.contains_self _ _)
  obtain m₆ : s₆.mem = Proof.Cmac.xor4Mem s₅.mem
      (State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 (n - K - 16))
      (State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 (n - K - 16))
      (State.addr w + BitVec.ofNat 64 dOff) := by rw [g₆.mem, h0₅, h11₅, eA]
  obtain dTD : (⟨State.addr w + BitVec.ofNat 64 tailOff, n - K⟩ : Region).Disjoint
      ⟨State.addr w + BitVec.ofNat 64 dOff, 16⟩ := L.w_w (.inl (by simp only [tailOff, dOff]; omega_arith))
        (by simp only [tailOff]; omega_arith) (by decide)
  refine ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact gT _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) sp₆ rd₆ wr₆, rd₆, wr₆, fun r hr h4 hlr => ?_, ?_, ?_, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact gT r a.1 a.2.1 a.2.2.1 a.2.2.2.1 h4 a.2.2.2.2 hlr
  · rw [g₆.gpr _ (by decide) (by decide), u₅.other _ (by decide), u₄.other _ (by decide), h4₃]
  · rw [m₆]
    refine (fW.sub fun r hr => ?_).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr w + BitVec.ofNat 64 16, 112⟩, by simp,
        Offset.sub _ (by simp only [tailOff]; omega_arith) (by simp only [tailOff]; omega_arith)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨⟨State.addr w + BitVec.ofNat 64 16, 112⟩, by simp, ?_⟩
      rw [Offset.add_add]; exact Offset.sub _ (by simp only [tailOff]; omega_arith) (by simp only [tailOff]; omega_arith)
  · have hBw : (State.addr w + BitVec.ofNat 64 tailOff).toNat + (n - K) ≤ 2 ^ 64 := by
      rw [← eT, addr_toNat, L.wN (by decide)]; simp only [tailOff]; omega_arith
    rw [m₆, xorend_mem4 _ (by omega_arith) hBw dTD,
      m₅, bytesAt_frame (writeBytes_frame _ _ _ (R := ⟨State.addr w + BitVec.ofNat 64 tailOff, n - K⟩)
        (by rw [hlx]; exact Region.contains_self _ _)) (p := State.addr w + BitVec.ofNat 64 dOff)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dTD.symm) (by decide)]
    obtain ws := bytesAt_writeBytes_self s.mem (State.addr w + BitVec.ofNat 64 tailOff)
      (bytesAt s.mem (State.addr P + BitVec.ofNat 64 K) (n - K)) (by omega_arith)
    rw [hlx] at ws
    rw [ws]
    obtain dr := drop_bytesAt s.mem (State.addr P) (a := K) (b := n - K)
    rw [show K + (n - K) = n by omega_arith] at dr
    rw [dr]

omit L in
/-- `jBlock`: `j` in `r7`. -/
theorem jBlock_ok {s : State} {n : Nat} (h16 : 16 ≤ n) (hn : n < 2 ^ 32) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa jBlock s fun s' => s'.gpr .r7 = BitVec.ofNat 32 (jOf n) ∧
      (∀ r, r ≠ .r7 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain e1 : BitVec.ofNat 32 n - 1#32 = BitVec.ofNat 32 (n - 1) := ofNat_sub32 (by omega_arith) hn
  obtain e2 : BitVec.ofNat 32 (n - 1) >>> 4 = BitVec.ofNat 32 ((n - 1) / 16) := shr4 (by omega_arith)
  obtain ⟨s₁, run₁, h7₁, hz₁, g₁, k₁⟩ : ∃ s₁, runBlock isa [.dp .sub .r12 .r5 (imm 1),
      .mov .r12 (.shifted .r12 .lsr 4), .mov .r7 (imm 0), .cmp .r12 (imm 0)] s = some s₁ ∧
      s₁.gpr .r7 = 0 ∧ s₁.z = decide ((n - 1) / 16 = 0) ∧
      (∀ r, r ≠ .r7 → r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [h5], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, e1, e2]
      exact z_cmp (by omega_arith) (by decide)
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : (n - 1) / 16 = 0
  · refine WP.ite true (eval_eq' (by rw [hz₁]; simp [h0])) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨by rw [h7₁]; simp [jOf, show n < 17 by omega_arith], g₁, k₁⟩
  · refine WP.ite false (eval_eq' (by rw [hz₁]; simp [h0])) (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg, jOf, show ¬ n < 17 by omega_arith]
    · intro r a b; simp [gpr_setReg, a, g₁ r a b]
    · exact ⟨k₁.mem, k₁.rd, k₁.wr, k₁.sp⟩

/-- What `longMac out` computes, from the memory `m` before it: the CMAC of
the `k` blocks of `P`, the first `j` blocks of the tail, and the rest of the
tail. -/
def longVal (m : Mem) (C W P : Addr) (R n : Nat) : List Byte :=
  Spec.Siv.schedCiph m C R (Spec.Cmac.xor
    (Spec.Cmac.lastBlock 16 (bytesAt m (C + BitVec.ofNat 64 240) 16) (bytesAt m (C + BitVec.ofNat 64 256) 16)
      ((bytesAt m (W + BitVec.ofNat 64 tailOff) (n - 16 * kOf n)).drop (16 * jOf n)))
    (Spec.Cmac.chain (Spec.Siv.schedCiph m C R)
      (Spec.Cmac.chain (Spec.Siv.schedCiph m C R) (Spec.Cmac.zeros 16)
        (Spec.Cmac.blocks 16 ((bytesAt m P n).take (16 * kOf n))))
      (Spec.Cmac.blocks 16 ((bytesAt m (W + BitVec.ofNat 64 tailOff) (n - 16 * kOf n)).take (16 * jOf n)))))

/-- What the calls of `longMac out` write. -/
abbrev outR (w sp : BitVec 32) (out : Nat) : List Region :=
  [⟨State.addr w + BitVec.ofNat 64 out, 16⟩, scrR w, blw sp]

/-- `longArgs₁ out`: the state at `W + out` zeroed, and the arguments of
`vg_cmac_aes_update` over the `K / 16` blocks of the string. -/
theorem longArgs₁_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32}
    {n K : Nat} (hP : Buf w sp s P n) (hKn : K ≤ n) (hK16 : 16 * (K / 16) = K) (hn : n < 2 ^ 32)
    (h6 : s.gpr .r6 = P) (h4 : s.gpr .r4 = BitVec.ofNat 32 K) {out : Nat} (hout : out = 0 ∨ out = tOff) :
    WP isa (.block (longArgs₁ out)) s fun s₂ => Env c w sp R s₂ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.mem = Proof.Cmac.zero4 s.mem (State.addr w + BitVec.ofNat 64 out) ∧
      UArgs s₂ c (w + BitVec.ofNat 32 out) P (w + BitVec.ofNat 32 256) R (K / 16) := by
  have ww := L.ww
  obtain ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  obtain eo : encodable (BitVec.ofNat 32 out) = true := by rcases hout with rfl | rfl <;> decide
  rw [longArgs₁, List.append_assoc]
  refine zero16_ok L he (d := out) (by omega_arith) fun s₁ g₁ m₁ rd₁ wr₁ sp₁ => ?_
  obtain he₁ : Env c w sp R s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide)) sp₁ rd₁ wr₁
  obtain hq := (hP.take (k := K) hKn).of_eq rd₁ wr₁
  obtain hsh : BitVec.ofNat 32 K >>> 4 = BitVec.ofNat 32 (K / 16) := shr4 (by omega_arith)
  obtain ⟨s₂, run₂, he₂, g₂, k₂, U₁⟩ : ∃ s₂, runBlock isa (macArgs out ++ [mov .r3 .r6, .mov .r12 (.shifted .r4 .lsr 4)])
      s₁ = some s₂ ∧ Env c w sp R s₂ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ ∧
      UArgs s₂ c (w + BitVec.ofNat 32 out) P (w + BitVec.ofNat 32 256) R (K / 16) := by
    obtain h6₁ : s₁.gpr .r6 = P := by rw [g₁ _ (by decide), h6]
    obtain h4₁ : s₁.gpr .r4 = BitVec.ofNat 32 K := by rw [g₁ _ (by decide), h4]
    refine ⟨_, by simp only [macArgs, csOff, mov]; arun [he₁.r9, he₁.r10, he₁.r11, eo], ?_⟩
    refine ⟨he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
      fun r a b c' d e f => by simp [gpr_setReg, a, b, c', d, e, f], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    refine uargs_of L ?_ hR (st := out) (by omega_arith) (n := K / 16) (by omega_arith)
      (by rw [show 16 * (K / 16) = K by omega_arith]; exact hq.fit) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
    · rw [show 16 * (K / 16) = K by omega_arith]; exact hq.w.sub_right (Lay.wSub (by omega_arith))
    · rw [show 16 * (K / 16) = K by omega_arith]; exact hq.w.sub_right (Lay.wSub (by decide))
    · rw [show 16 * (K / 16) = K by omega_arith]; exact hq.stk
    · rw [show 16 * (K / 16) = K by omega_arith]; exact hq.rd
    · simp [gpr_setReg, he₁.r10]
    · simp [gpr_setReg, he₁.r9]
    · simp [gpr_setReg, he₁.r11]
    · simp [gpr_setReg, h6₁]
    · simp [gpr_setReg, h4₁, hsh]
    · simp [gpr_setReg, he₁.r11]
  exact WP.of_runBlock ⟨s₂, run₂, he₂, fun r a b c' d e f => by rw [g₂ r a b c' d e f, g₁ r e],
    by rw [k₂.rd, rd₁], by rw [k₂.wr, wr₁], by rw [k₂.mem, m₁], U₁⟩

/-- `longArgs₂ out`: the arguments of `vg_cmac_aes_update` over the first `j`
blocks of the tail. -/
theorem longArgs₂_ok {s₄ : State} (he₄ : Env c w sp R s₄) (hR : R = 10 ∨ R = 12 ∨ R = 14) {out : Nat}
    (hout : out = 0 ∨ out = tOff) {j : Nat} (hj1 : j ≤ 1) (h7₄ : s₄.gpr .r7 = BitVec.ofNat 32 j) :
    ∃ s₅, runBlock isa (longArgs₂ out) s₄ = some s₅ ∧ Env c w sp R s₅ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ ∧
      UArgs s₅ c (w + BitVec.ofNat 32 out) (w + BitVec.ofNat 32 tailOff) (w + BitVec.ofNat 32 256) R j := by
  have ww := L.ww
  obtain ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  obtain hoT : out + 16 ≤ tailOff ∨ tailOff + 32 ≤ out := by rcases hout with rfl | rfl <;> decide
  obtain eo : encodable (BitVec.ofNat 32 out) = true := by rcases hout with rfl | rfl <;> decide
  obtain eT := L.wA (d := tailOff) (by decide)
  refine ⟨_, by simp only [longArgs₂, macArgs, csOff, tailOff, mov]; arun [he₄.r9, he₄.r10, he₄.r11, eo], ?_⟩
  refine ⟨he₄.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
    fun r a b c' d e f => by simp [gpr_setReg, a, b, c', d, e, f], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  refine uargs_of L ?_ hR (st := out) (by omega_arith) (n := j) (by omega_arith)
    (by rw [L.wN (by decide)]; simp only [tailOff]; omega_arith) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact he₄.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
  · rw [eT]; exact L.w_w (by simp only [tailOff] at hoT ⊢; omega_arith) (by simp only [tailOff]; omega_arith) (by omega_arith)
  · rw [eT]; exact L.w_w (.inl (by simp only [tailOff]; omega_arith)) (by simp only [tailOff]; omega_arith) (by decide)
  · rw [eT]; exact L.stk_w' (by simp only [tailOff]; omega_arith)
  · rw [eT]; exact covers_left (he₄.perm.wC (by simp only [tailOff]; omega_arith))
  · simp [gpr_setReg, he₄.r10]
  · simp [gpr_setReg, he₄.r9]
  · simp [gpr_setReg, he₄.r11]
  · simp [gpr_setReg, he₄.r11]
  · simp [gpr_setReg, h7₄]
  · simp [gpr_setReg, he₄.r11]

/-- `longArgs₃ out`: the arguments of `vg_cmac_aes_finalize` over the rest of
the tail. -/
theorem longArgs₃_ok {s₆ : State} (he₆ : Env c w sp R s₆) (hR : R = 10 ∨ R = 12 ∨ R = 14) {out : Nat}
    (hout : out = 0 ∨ out = tOff) {n K j : Nat} (hn : n < 2 ^ 32) (hT : 16 ≤ n - K ∧ n - K ≤ 32)
    (hJ : 16 * j ≤ n - K ∧ 0 < n - K - 16 * j ∧ n - K - 16 * j ≤ 16) (hj1 : j ≤ 1)
    (h7₆ : s₆.gpr .r7 = BitVec.ofNat 32 j) (h5₆ : s₆.gpr .r5 = BitVec.ofNat 32 n)
    (h4₆ : s₆.gpr .r4 = BitVec.ofNat 32 K) :
    ∃ s₇, runBlock isa (longArgs₃ out) s₆ = some s₇ ∧ Env c w sp R s₇ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₇.gpr r = s₆.gpr r) ∧ Keeps s₆ s₇ ∧
      FArgs s₇ c (w + BitVec.ofNat 32 out) (w + BitVec.ofNat 32 (tailOff + 16 * j)) (w + BitVec.ofNat 32 256)
        (n - K - 16 * j) R := by
  have ww := L.ww
  obtain ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  obtain hoT : out + 16 ≤ tailOff ∨ tailOff + 32 ≤ out := by rcases hout with rfl | rfl <;> decide
  obtain eo : encodable (BitVec.ofNat 32 out) = true := by rcases hout with rfl | rfl <;> decide
  obtain e7 : BitVec.ofNat 32 j <<< 4 = BitVec.ofNat 32 (16 * j) := shl4 (by omega_arith)
  obtain eR : BitVec.ofNat 32 n - BitVec.ofNat 32 K - BitVec.ofNat 32 (16 * j) =
      BitVec.ofNat 32 (n - K - 16 * j) := by
    rw [ofNat_sub32 (by omega_arith) hn, ofNat_sub32 (by omega_arith) (by omega_arith)]
  obtain eA : w + BitVec.ofNat 32 tailOff + BitVec.ofNat 32 (16 * j) = w + BitVec.ofNat 32 (tailOff + 16 * j) :=
    add32_ofNat_assoc _ _ _
  refine ⟨_, by simp only [longArgs₃, macArgs, csOff, mov]; arun [he₆.r9, he₆.r10, he₆.r11, eo], ?_⟩
  refine ⟨he₆.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
    fun r a b c' d e f => by simp [gpr_setReg, a, b, c', d, e, f], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  refine fargs_of L ?_ hR (st := out) (by omega_arith) (n := n - K - 16 * j) (by omega_arith)
    (by rw [L.wN (by simp only [tailOff]; omega_arith)]; simp only [tailOff]; omega_arith) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact he₆.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
  · rw [L.wA (by simp only [tailOff]; omega_arith)]
    exact L.w_w (by simp only [tailOff] at hoT ⊢; omega_arith) (by simp only [tailOff]; omega_arith) (by omega_arith)
  · rw [L.wA (by simp only [tailOff]; omega_arith)]
    exact L.w_w (.inl (by simp only [tailOff]; omega_arith)) (by simp only [tailOff]; omega_arith) (by decide)
  · rw [L.wA (by simp only [tailOff]; omega_arith)]; exact L.stk_w' (by simp only [tailOff]; omega_arith)
  · rw [L.wA (by simp only [tailOff]; omega_arith)]; exact covers_left (he₆.perm.wC (by simp only [tailOff]; omega_arith))
  · simp [gpr_setReg, he₆.r10]
  · simp [gpr_setReg, he₆.r9]
  · simp [gpr_setReg, he₆.r11]
  · simp [gpr_setReg, he₆.r11, h7₆, e7, eA]
  · simp [gpr_setReg, h5₆, h4₆, h7₆, e7, eR]
  · simp [gpr_setReg, he₆.r11]

/-- `longMac out`: S2V's end for a long string, from its tail, at `W + out`. -/
theorem longMac_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {n : Nat}
    (hP : Buf w sp s P n) (h16 : 16 ≤ n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = P)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 n) (h4 : s.gpr .r4 = BitVec.ofNat 32 (16 * kOf n)) {out : Nat}
    (hout : out = 0 ∨ out = tOff) :
    WP isa (longMac out) s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r7 → r ≠ .lr → s'.gpr r = s.gpr r) ∧ Frame (outR w sp out) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 out) 16 =
        longVal s.mem (State.addr c) (State.addr w) (State.addr P) R n := by
  have ww := L.ww
  obtain hT := kOf_tail h16
  obtain hJ := jOf_rest h16
  obtain hj1 := jOf_le n
  obtain ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  obtain hoT : out + 16 ≤ tailOff ∨ tailOff + 32 ≤ out := by rcases hout with rfl | rfl <;> decide
  obtain eo : encodable (BitVec.ofNat 32 out) = true := by rcases hout with rfl | rfl <;> decide
  obtain eT := L.wA (d := tailOff) (by decide)
  obtain eO := L.wA (d := out) (by omega_arith)
  obtain eS := L.wA (d := 256) (by decide)
  obtain hRb := rounds_le hR
  generalize hK : 16 * kOf n = K at hT hJ h4 ⊢
  obtain hKk : K / 16 = kOf n := by omega_arith
  generalize hj : jOf n = j at hJ hj1 ⊢
  -- The first call's arguments.
  rw [longMac]
  refine WP.seq (WP.mono (longArgs₁_ok L he hR hP (by omega_arith) (by omega_arith) hn h6 h4 hout)
    fun s₂ ⟨he₂, g₂, rd₂, wr₂, m₂, U₁⟩ => ?_)
  refine WP.seq (WP.mono (upd_call U₁) fun s₃ h₃ => ?_)
  obtain he₃ := he₂.of_saved h₃.saved h₃.sp h₃.rd h₃.wr
  obtain g₃ : ∀ r ∈ preserved, r ≠ .lr → s₃.gpr r = s.gpr r := fun r hr hlr => by
    obtain a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h₃.saved r hr hlr, g₂ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr]
  obtain h5₃ : s₃.gpr .r5 = BitVec.ofNat 32 n := by rw [g₃ _ (by decide) (by decide), h5]
  obtain h4₃ : s₃.gpr .r4 = BitVec.ofNat 32 K := by rw [g₃ _ (by decide) (by decide), h4]
  -- `j`.
  refine WP.seq (WP.mono (jBlock_ok h16 hn h5₃) fun s₄ ⟨h7₄, g₄, k₄⟩ => ?_)
  rw [hj] at h7₄
  obtain he₄ : Env c w sp R s₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide)) k₄.sp k₄.rd k₄.wr
  obtain h5₄ : s₄.gpr .r5 = BitVec.ofNat 32 n := by rw [g₄ _ (by decide) (by decide), h5₃]
  obtain h4₄ : s₄.gpr .r4 = BitVec.ofNat 32 K := by rw [g₄ _ (by decide) (by decide), h4₃]
  -- The second call's arguments: the first `j` blocks of the tail.
  obtain ⟨s₅, run₅, he₅, g₅, k₅, U₂⟩ := longArgs₂_ok L he₄ hR hout hj1 h7₄
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  refine WP.seq (WP.mono (upd_call U₂) fun s₆ h₆ => ?_)
  obtain he₆ := he₅.of_saved h₆.saved h₆.sp h₆.rd h₆.wr
  obtain g₆ : ∀ r ∈ preserved, r ≠ .r7 → r ≠ .lr → s₆.gpr r = s₄.gpr r := fun r hr h7 hlr => by
    obtain a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h₆.saved r hr hlr, g₅ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr]
  obtain h7₆ : s₆.gpr .r7 = BitVec.ofNat 32 j := by
    rw [h₆.saved _ (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h7₄]
  obtain h5₆ : s₆.gpr .r5 = BitVec.ofNat 32 n := by rw [g₆ _ (by decide) (by decide) (by decide), h5₄]
  obtain h4₆ : s₆.gpr .r4 = BitVec.ofNat 32 K := by rw [g₆ _ (by decide) (by decide) (by decide), h4₄]
  -- The third call's arguments: the rest of the tail.
  obtain ⟨s₇, run₇, he₇, g₇, k₇, F⟩ := longArgs₃_ok L he₆ hR hout hn hT hJ hj1 h7₆ h5₆ h4₆
  refine WP.seq (WP.of_runBlock ⟨s₇, run₇, ?_⟩)
  refine WP.mono (fin_call F) fun s₈ h₈ => ?_
  obtain hb₂ := blw16_eq (s := s₂) he₂.sp
  obtain hb₅ := blw16_eq (s := s₅) he₅.sp
  obtain hb₇ := blw16_eq (s := s₇) he₇.sp
  -- What each step writes.
  obtain F₃ : Frame (outR w sp out) s₂.mem s₃.mem := by
    have := h₃.frame; rw [eO, eS, hb₂] at this; exact this
  obtain F₆ : Frame (outR w sp out) s₅.mem s₆.mem := by
    have := h₆.frame; rw [eO, eS, hb₅] at this; exact this
  obtain F₈ : Frame (outR w sp out) s₇.mem s₈.mem := by
    have := h₈.frame; rw [eO, eS, hb₇] at this; exact this
  obtain F₀₂ : Frame (outR w sp out) s.mem s₂.mem := by
    rw [m₂]; exact (Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp)
  obtain F₀₃ : Frame (outR w sp out) s.mem s₃.mem := F₀₂.trans F₃
  obtain F₀₅ : Frame (outR w sp out) s.mem s₅.mem := by rw [k₅.mem, k₄.mem]; exact F₀₃
  obtain F₀₆ : Frame (outR w sp out) s.mem s₆.mem := F₀₅.trans F₆
  obtain F₀₇ : Frame (outR w sp out) s.mem s₇.mem := by rw [k₇.mem]; exact F₀₆
  refine ⟨he₇.of_saved h₈.saved h₈.sp h₈.rd h₈.wr, by rw [h₈.rd, k₇.rd, h₆.rd, k₅.rd, k₄.rd, h₃.rd, rd₂],
    by rw [h₈.wr, k₇.wr, h₆.wr, k₅.wr, k₄.wr, h₃.wr, wr₂], fun r hr h7 hlr => ?_, F₀₇.trans F₈, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h₈.saved r hr hlr, g₇ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr, g₆ r hr h7 hlr, g₄ r h7 a.2.2.2.2,
      g₃ r hr hlr]
  -- What the calls read is as on entry, but the state.
  obtain dc : ∀ {d k : Nat}, d + k ≤ 512 → ∀ r ∈ outR w sp out, (⟨State.addr c + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hd r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.c_w' hd (by omega_arith)
    · exact L.c_w' hd (by decide)
    · exact (L.stk_c' hd).symm
  obtain dt : ∀ {d k : Nat}, tailOff + d + k ≤ 64 → ∀ r ∈ outR w sp out,
      (⟨State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hd r hr
    rw [Offset.add_add]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.w_w (by simp only [tailOff] at hoT hd ⊢; omega_arith) (by omega_arith) (by omega_arith)
    · exact L.w_w (.inl (by simp only [tailOff] at hd ⊢; omega_arith)) (by omega_arith) (by decide)
    · exact (L.stk_w' (by omega_arith)).symm
  obtain dp : ∀ r ∈ outR w sp out, (⟨State.addr P, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hP.w.sub_right (Lay.wSub (by omega_arith))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm
  have cK {m' : Mem} (hf : Frame (outR w sp out) s.mem m') {d k : Nat} (hd : d + k ≤ 512) :
      bytesAt m' (State.addr c + BitVec.ofNat 64 d) k = bytesAt s.mem (State.addr c + BitVec.ofNat 64 d) k :=
    bytesAt_frame hf (dc hd) (by omega_arith)
  have cT {m' : Mem} (hf : Frame (outR w sp out) s.mem m') {d k : Nat} (hd : tailOff + d + k ≤ 64) :
      bytesAt m' (State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 d) k =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 d) k :=
    bytesAt_frame hf (dt hd) (by omega_arith)
  obtain k0 : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => BitVec.add_zero a
  obtain sch₂ := cK F₀₂ (d := 0) (k := 16 * (R + 1)) (by omega_arith)
  obtain sch₅ := cK F₀₅ (d := 0) (k := 16 * (R + 1)) (by omega_arith)
  obtain sch₇ := cK F₀₇ (d := 0) (k := 16 * (R + 1)) (by omega_arith)
  rw [k0] at sch₂ sch₅ sch₇
  obtain k1 := cK F₀₇ (d := 240) (k := 16) (by decide)
  obtain k2 := cK F₀₇ (d := 256) (k := 16) (by decide)
  obtain pK : bytesAt s₂.mem (State.addr P) K = bytesAt s.mem (State.addr P) K :=
    bytesAt_frame F₀₂ (fun r hr => (dp r hr).sub_left (Region.sub_prefix (by omega_arith))) (by omega_arith)
  obtain tJ := cT F₀₅ (d := 0) (k := 16 * j) (by simp only [tailOff]; omega_arith)
  obtain tR := cT F₀₇ (d := 16 * j) (k := n - K - 16 * j) (by simp only [tailOff]; omega_arith)
  rw [k0] at tJ
  obtain z₂ : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
    rw [m₂, Proof.Cmac.zero4_bytes]
  have o₃ := h₃.out
  have o₆ := h₆.out
  have o₈ := h₈.out
  rw [eO, sch₂, z₂, Proof.Cmac.Stream.blocksAt_eq, show 16 * (K / 16) = K by omega_arith, pK] at o₃
  rw [eO, eT, sch₅, k₅.mem, k₄.mem, o₃, Proof.Cmac.Stream.blocksAt_eq, ← k₄.mem, ← k₅.mem, tJ] at o₆
  rw [eO, L.wA (by simp only [tailOff]; omega_arith), ← Offset.add_add, sch₇, k1, k2, tR, k₇.mem, o₆] at o₈
  rw [o₈, longVal, Spec.Siv.schedCiph, hK, hj]
  -- The pieces of `P` and of the tail.
  obtain tk := take_bytesAt s.mem (State.addr P) (a := K) (b := n - K)
  rw [show K + (n - K) = n by omega_arith] at tk
  obtain tk' := take_bytesAt s.mem (State.addr w + BitVec.ofNat 64 tailOff) (a := 16 * j) (b := n - K - 16 * j)
  rw [show 16 * j + (n - K - 16 * j) = n - K by omega_arith] at tk'
  obtain dr' := drop_bytesAt s.mem (State.addr w + BitVec.ofNat 64 tailOff) (a := 16 * j) (b := n - K - 16 * j)
  rw [show 16 * j + (n - K - 16 * j) = n - K by omega_arith] at dr'
  rw [tk, tk', dr']

omit L in
theorem outR_oR {out : Nat} : ∀ r ∈ outR w sp out, ∃ r' ∈ oR w sp out, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨blw sp, by simp, fun _ h => h⟩

/-- S2V's end for a string `P` of a block or more, into `W + out`. -/
theorem long_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {n : Nat}
    (hP : Buf w sp s P n) (h16 : 16 ≤ n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = P)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 n) {out : Nat} (hout : out = 0 ∨ out = tOff) :
    WP isa (.seq longTail (longMac out)) s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r7 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (oR w sp out) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 out) 16 =
        Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (State.addr c) R)
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16) (bytesAt s.mem (State.addr P) n) := by
  obtain ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  refine WP.seq (WP.mono (longTail_ok L he hP h16 hn h6 h5) fun s₁ ⟨he₁, rd₁, wr₁, g₁, h4₁, f₁, t₁⟩ => ?_)
  obtain h6₁ : s₁.gpr .r6 = P := by rw [g₁ _ (by decide) (by decide) (by decide), h6]
  obtain h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 n := by rw [g₁ _ (by decide) (by decide) (by decide), h5]
  refine WP.mono (longMac_ok L he₁ hR (hP.of_eq rd₁ wr₁) h16 hn h6₁ h5₁ h4₁ hout)
    fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, o₂⟩ => ?_
  refine ⟨he₂, by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun r hr h4 h7 hlr => by rw [g₂ r hr h7 hlr, g₁ r hr h4 hlr],
    (frame_oR out f₁).trans (f₂.sub outR_oR), ?_⟩
  obtain hRb := rounds_le hR
  obtain dc : ∀ {d k : Nat}, d + k ≤ 512 → ∀ r ∈ wR w sp, (⟨State.addr c + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hd => dis_wR (L.c_w.sub_left (Lay.cSub hd)) (L.stk_c' hd)
  have cK {d k : Nat} (hd : d + k ≤ 512) :
      bytesAt s₁.mem (State.addr c + BitVec.ofNat 64 d) k = bytesAt s.mem (State.addr c + BitVec.ofNat 64 d) k :=
    bytesAt_frame f₁ (dc hd) (by omega_arith)
  obtain sch := cK (d := 0) (k := 16 * (R + 1)) (by omega_arith)
  rw [BitVec.add_zero] at sch
  obtain pP : bytesAt s₁.mem (State.addr P) n = bytesAt s.mem (State.addr P) n :=
    bytesAt_frame f₁ (dis_wR hP.w hP.stk) (by omega_arith)
  rw [o₂, longVal, Spec.Siv.schedCiph, sch, cK (d := 240) (k := 16) (by decide), cK (d := 256) (k := 16) (by decide),
    t₁, pP, Spec.Siv.ctxMac, Spec.Siv.schedCiph, show (240 : Addr) = BitVec.ofNat 64 240 from rfl,
    show (256 : Addr) = BitVec.ofNat 64 256 from rfl]
  obtain hl : 16 ≤ (bytesAt s.mem (State.addr P) n).length := by rw [Proof.Cmac.bytesAt_length]; exact h16
  obtain ls := long_spec (Spec.Cmac.aesWith R (bytesAt s.mem (State.addr c) (16 * (R + 1))))
    (bytesAt s.mem (State.addr c + BitVec.ofNat 64 240) 16) (bytesAt s.mem (State.addr c + BitVec.ofNat 64 256) 16)
    (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16) (bytesAt s.mem (State.addr P) n)
    (Proof.Cmac.bytesAt_length _ _ _) hl
  rw [Proof.Cmac.bytesAt_length s.mem (State.addr P) n] at ls
  exact ls

omit L in
/-- `finish`'s first block: `Z` set iff the string is shorter than a block. -/
theorem finishPre_ok {s : State} {n : Nat} (hn : n < 2 ^ 32) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    ∃ s₁, runBlock isa [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)] s =
      some s₁ ∧ s₁.z = decide (n / 16 = 0) ∧ (∀ r, r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
  refine ⟨_, by arun [h5], ?_, ?_, ?_⟩
  · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, shr4 hn]
    exact z_cmp (by omega_arith) (by decide)
  · intro r a; simp [gpr_setReg, a]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- `finish out`: S2V's end with the string `P` (`n` bytes, in `r6` and
`r5`) from `D`, into `W + out`. -/
theorem finish_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {n : Nat}
    (hP : Buf w sp s P n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 n)
    {out : Nat} (hout : out = 0 ∨ out = tOff) :
    WP isa (finish out) s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (oR w sp out) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 out) 16 =
        Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (State.addr c) R)
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16) (bytesAt s.mem (State.addr P) n) := by
  obtain ⟨s₁, run₁, hz₁, g₁, k₁⟩ := finishPre_ok hn h5
  obtain he₁ : Env c w sp R s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  obtain hP₁ := hP.of_eq k₁.rd k₁.wr
  obtain h6₁ : s₁.gpr .r6 = P := by rw [g₁ _ (by decide), h6]
  obtain h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 n := by rw [g₁ _ (by decide), h5]
  obtain gP : ∀ r ∈ preserved, s₁.gpr r = s.gpr r := fun r hr => g₁ r (by
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  rw [finish]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : n / 16 = 0
  · refine WP.ite true (eval_eq' (by rw [hz₁]; simp [h0])) (fun _ => ?_) (fun h => by cases h)
    refine WP.mono (short_ok L he₁ hR hP₁ (by omega_arith) h6₁ h5₁ hout) fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, o₂⟩ => ?_
    refine ⟨he₂, by rw [rd₂, k₁.rd], by rw [wr₂, k₁.wr], fun r hr h4 h6 _ hlr => by rw [g₂ r hr h4 h6 hlr, gP r hr],
      by rw [← k₁.mem]; exact f₂, by rw [o₂, k₁.mem]⟩
  · refine WP.ite false (eval_eq' (by rw [hz₁]; simp [h0])) (fun h => by cases h) fun _ => ?_
    refine WP.mono (long_ok L he₁ hR hP₁ (by omega_arith) hn h6₁ h5₁ hout) fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, o₂⟩ => ?_
    refine ⟨he₂, by rw [rd₂, k₁.rd], by rw [wr₂, k₁.wr], fun r hr h4 _ h7 hlr => by rw [g₂ r hr h4 h7 hlr, gP r hr],
      by rw [← k₁.mem]; exact f₂, by rw [o₂, k₁.mem]⟩

end

end VG.Proof.AesSiv.Arm
