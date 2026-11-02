module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.MrExponentRt
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.HalfPassWord
import VerifiedGarbage.Proof.Mont.Halve32
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedGeometry
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.MillerRabin.X86.Copy
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Rt.Step

/-! # Array 27 halved in place at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MrExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.MrExponentRt

/-- A pointer into the working space, from `edi` at its base. -/
theorem ptr_edi {t : State} {W : Addr} {L x : Nat} (S : Scr t W L) {r : Reg} (P : PtrAt t W r x) (_fit : x < L) :
    t.gpr r = t.gpr .edi + BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  have nowrap := S.nowrap
  rw [P, BitVec.toNat_add, BitVec.toNat_ofNat, S.edi_toNat]
  omega

/-- One word of an in-place pass, at `ebp`, and `esi` down one. -/
theorem halfStep_ok {t : State} {W : Addr} {L x : Nat} (S : Scr t W L) (bp : PtrAt t W .ebp x)
    (aligned : x % 4 = 0) (fit : x + 8 ≤ L) {choice : Bool} (mask : t.gpr .ecx = cmask choice) :
    WP isa (.block halfStep) t fun u =>
      Outside W x 4 t.mem u.mem ∧
      w32 u.mem W x = (if choice then w32 t.mem W x / 2 + 2 ^ 31 * (w32 t.mem W (x + 4) % 2) else w32 t.mem W x) ∧
      PtrAt u W .ebp (x + 4) ∧ u.gpr .esi = t.gpr .esi - 1 ∧ u.zf = some (t.gpr .esi - 1 == 0) ∧
      Keeps [.eax, .ebx, .edx, .ebp, .esi] t u := by
  have index : 0 + 4 * (x / 4) = x := by omega
  have pointer : t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (x / 4)) := by
    rw [ptr_edi S bp (by omega)]; congr 2; omega
  unfold halfStep
  refine WP.block_append (WP.mono (VG.Proof.RsaKeyGen.X86.HalfPass.step_ok (src := 0) (out := 0) S pointer
    (by omega) (by omega) mask) fun a ⟨O, V, K⟩ => ?_)
  refine wp_addS rfl fun b B _ => wp_subZ rfl fun u U Z => WP.block_nil ?_
  rw [index] at O V
  have esiB : b.gpr .esi = t.gpr .esi := by rw [B.other .esi (by decide), K.1 .esi (by decide)]
  refine ⟨by rw [U.mem, B.mem]; exact O, by rw [U.mem, B.mem, V],
    ?_, by rw [U.gpr, esiB], by rw [Z, esiB], ((K.mono (by decide)).widen B.keeps).widen U.keeps⟩
  rw [PtrAt, U.other .ebp (by decide), B.gpr, K.1 .ebp (by decide), ptr_add bp]
  rfl

theorem halfLoop_ok {t₀ : State} {W : Addr} {L x N : Nat} (S : Scr t₀ W L) (positive : 0 < N)
    (aligned : x % 4 = 0) (fit : x + 4 * (N + 1) ≤ L) (top : w32 t₀.mem W (x + 4 * N) = 0)
    (bp : PtrAt t₀ W .ebp x) (count : (t₀.gpr .esi).toNat = N) {choice : Bool} (mask : t₀.gpr .ecx = cmask choice) :
    WP isa (.loop (.block halfStep) .ne) t₀ fun u =>
      Outside W x (4 * N) t₀.mem u.mem ∧
      val32 u.mem W x N = (if choice then val32 t₀.mem W x N / 2 else val32 t₀.mem W x N) ∧
      PtrAt u W .ebp (x + 4 * N) ∧ Keeps [.eax, .ebx, .edx, .ebp, .esi] t₀ u := by
  have nowrap := S.nowrap
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.countLoop positive (fun j t =>
      Keeps [.eax, .ebx, .edx, .ebp, .esi] t₀ t ∧ Outside W x (4 * j) t₀.mem t.mem ∧
      (∀ i < j, w32 t.mem W (x + 4 * i) =
        if choice then w32 t₀.mem W (x + 4 * i) / 2 + 2 ^ 31 * (w32 t₀.mem W (x + 4 * i + 4) % 2)
        else w32 t₀.mem W (x + 4 * i)) ∧
      PtrAt t W .ebp (x + 4 * j) ∧ (t.gpr .esi).toNat = N - j) ?_
    ⟨Keeps.refl _ _, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _), by simpa using bp,
      by simpa using count⟩) ?_
  · rintro j t index ⟨K, O, V, P, esi⟩
    have St := S.of_keeps K (by decide)
    refine WP.mono (halfStep_ok (choice := choice) St P (by omega) (by omega) (by rw [K.1 .ecx (by decide)]; exact mask))
      fun u ⟨Ou, value, Pu, esiU, Z, Ku⟩ => ?_
    obtain ⟨next, last⟩ := VG.Proof.Bignum.X86.PublicRt.count1_zf esi index
    have sameLo : w32 t.mem W (x + 4 * j) = w32 t₀.mem W (x + 4 * j) := O.w32 (by omega) (by omega)
    have sameHi : w32 t.mem W (x + 4 * j + 4) = w32 t₀.mem W (x + 4 * j + 4) := O.w32 (by omega) (by omega)
    refine ⟨⟨K.trans Ku, (O.mono (by omega) (by omega)).trans (Ou.mono (by omega) (by omega)), ?_,
      by rw [show x + 4 * (j + 1) = x + 4 * j + 4 by omega]; exact Pu, by rw [esiU]; exact next⟩,
      by rw [Z, last]⟩
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with before | rfl
    · rw [Ou.w32 (by omega) (by omega)]
      exact V i before
    · rw [value, sameLo, sameHi]
  · rintro u ⟨K, O, V, P, _⟩
    refine ⟨O, ?_, P, K⟩
    cases choice
    · exact val32_congr_at t₀.mem u.mem W N x x V
    · apply val32_halve_at t₀.mem u.mem W N x x
      intro i hi
      rw [V i hi, show x + 4 * i + 4 = x + 4 * (i + 1) by omega]
      by_cases last : i + 1 = N
      · rw [ite_eq_left last, last, top]
        rfl
      · rw [ite_eq_right last]
        rfl

/-- `half`: array 27 halved in place where the mask `ecx` is all ones. -/
theorem half_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) (S : Scr s g.W g.L)
    (top : w32 s.mem g.W (g.array 27 + 4 * g.words) = 0) {choice : Bool} (mask : s.gpr .ecx = cmask choice) :
    WP isa half s fun t =>
      Outside g.W (g.array 27) (4 * g.words) s.mem t.mem ∧
      val32 t.mem g.W (g.array 27) g.words =
        (if choice then val32 s.mem g.W (g.array 27) g.words / 2 else val32 s.mem g.W (g.array 27) g.words) ∧
      PtrAt t g.W .ebp (g.array 27 + 4 * g.words) ∧ Keeps [.eax, .ebx, .edx, .ebp, .esi] s t := by
  have fit := VG.Proof.RsaKeyGen.X86.Prepared.paddedFit v (j := 27) (by decide)
  have positive := v.minWidth
  unfold half
  refine WP.seq (WP.block_append (WP.mono (C.ptr v 27 (by decide) .ebp (by decide) (by decide))
    fun a ⟨P, Ma, Ka⟩ => ?_))
  have Ca := C.keepMem Ka (by decide) Ma
  refine WP.mono (words_ok v Ca) fun b ⟨count, Mb, Kb⟩ => ?_
  have K : Keeps [.edx, .ebp, .esi] s b := (Ka.mono (by decide)).widen Kb
  have Pb : PtrAt b g.W .ebp (g.array 27) := by rw [PtrAt, Kb.1 .ebp (by decide)]; exact P
  have M : b.mem = s.mem := Mb.trans Ma
  refine WP.mono (halfLoop_ok (choice := choice) (S.of_keeps K (by decide)) (by unfold Geometry.words; omega)
    (by simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega)
    (by unfold Geometry.words; omega) (by rw [M]; exact top) Pb count
    (by rw [K.1 .ecx (by decide)]; exact mask)) fun t ⟨O, V, Pt, Kt⟩ => ?_
  rw [M] at O V
  exact ⟨O, V, Pt, (K.mono (by decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.MrExponentRt
