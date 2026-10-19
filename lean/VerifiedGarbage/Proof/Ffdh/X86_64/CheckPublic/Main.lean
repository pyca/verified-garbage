module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Context
public import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Subgroup
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math

/-! # FFDH public-key validation on x86-64: the main computation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh VG.Proof.MlKem.X86_64
open VG.Spec.Ffdh

/-- `publicValid`, on the integers. -/
theorem publicValid_iff (a : Parameters) (y : Nat) :
    publicValid ⟨a, y⟩ = true ↔ (1 < y ∧ y < a.p - 1) ∧ ∀ q, a.q = some q → y ^ q % a.p = 1 := by
  unfold publicValid
  cases hq : a.q with
  | none => simp
  | some q => simp [powMod_eq]

/-- After `domHead`, for a valid modulus p: `main`. -/
theorem cpMain_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {s t : State} (c : CpCtx s)
    (h0 : t.gpr .rdi = s.gpr .r9) (hs : Scr t (s.gpr .r9) ((scrLen s).toNat * 8))
    (hD : word t.mem (s.gpr .r9) (8 * sDom) = s.gpr .rdi)
    (hL : word t.mem (s.gpr .r9) (8 * sDomLen) = s.gpr .rsi)
    (hK : word t.mem (s.gpr .r9) (8 * sK) = BitVec.ofNat 64 (s.gpr .rdx).toNat)
    (hY : word t.mem (s.gpr .r9) (8 * sY) = s.gpr .rcx)
    (hQ : word t.mem (s.gpr .r9) (8 * sQ) = s.gpr .rdi + BitVec.ofNat 64 (2 * (s.gpr .rdx).toNat))
    (i₀ : InScr (s.gpr .r9) ((scrLen s).toNat * 8) s.mem t.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hval : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rdx).toNat))
      (s.gpr .rdx).toNat = true) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.main M.mm E.code (.seq (.block r2Head) R.code)) t fun t' =>
      (t'.gpr .rax = if publicValid ⟨domainOf (s.gpr .rdx).toNat (cpDom s),
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)⟩ then 1 else 0) ∧
      t'.gpr .rdi = s.gpr .r9 ∧ InScr (s.gpr .r9) ((scrLen s).toNat * 8) t.mem t'.mem ∧
      (∀ i < 6, word t'.mem (s.gpr .r9) (8 * i) = word t.mem (s.gpr .r9) (8 * i)) ∧ Keep (.rdi :: mmRegs) t t' := by
  obtain ⟨hk1, hk2, hdl, hyl, hZ, -, hdom, hy⟩ := c
  have hn := hs.nowrap
  simp only [cpDom] at *
  generalize s.gpr .r9 = B at *
  generalize (scrLen s).toNat * 8 = Z at *
  generalize hkk : (s.gpr .rdx).toNat = k at *
  rw [hyl] at hy ⊢
  have hroom := room_k hk1 hZ
  obtain ⟨hodd, hp1, hlo⟩ := valid_facts hval hk1
  have hsrcD := hdom.congr i₀ hrd hwr
  have hpS : Src t B Z (s.gpr .rdi) (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k) := by
    have := src_slice (off := 0) (len := k) hsrcD (by rcases hdl with h | h <;> rw [h] <;> omega_arith)
    simpa using this
  have hyS : Src t B Z (s.gpr .rcx) (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) := hy.congr i₀ hrd hwr
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPublic.main
  rw [show [.block VG.Impl.Rsa.X86_64.head] ++ pSetup ++ Crt.loadArr aXm sY sK ++ rangeTest aXm ++
      [Code.ite .e (VG.Impl.Ffdh.X86_64.Domain.retInner 0)
        (.seq (.block (leave :: qTest)) (.ite .e (VG.Impl.Ffdh.X86_64.Domain.ret 1)
          (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup M.mm E.code (.seq (.block r2Head) R.code)))))] =
    ([.block VG.Impl.Rsa.X86_64.head] ++ pSetup) ++ (Crt.loadArr aXm sY sK ++ (rangeTest aXm ++
      [Code.ite .e (VG.Impl.Ffdh.X86_64.Domain.retInner 0)
        (.seq (.block (leave :: qTest)) (.ite .e (VG.Impl.Ffdh.X86_64.Domain.ret 1)
          (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup M.mm E.code (.seq (.block r2Head) R.code)))))])) by
    simp only [List.append_assoc]]
  -- The workspaces.
  refine wp_seqs_append (by simp) (by simp [Crt.loadArr]) (WP.mono (setup_ok hs h0 hk1 hk2 hZ hD hK hpS
    (bytesAt_length _ _ _) hodd) fun u₁ ⟨mi, hc₁, hv₁, hWs₁, f₁, k₁⟩ => ?_)
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hi8 : 8 * 32 ≤ inner ((k + 7) / 8) := by simp only [inner, slot, hdrBytes]; omega_arith
  have hiZ : inner ((k + 7) / 8) + slot ((k + 7) / 8) 8 ≤ Z := by unfold tabBytes at hroom; omega_arith
  have hp₁ : ∀ i < 32, i ≠ sW → i ≠ sWs → (i < sArr 0 ∨ sArr 0 + 8 ≤ i) →
      word u₁.mem B (8 * i) = word t.mem B (8 * i) := fun i hi h1 h2 h3 =>
    f₁.word_eq (fun r hr => by
      simp only [setupR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> unfold sW sWs sArr sFn at * <;> omega_arith) (by omega_arith)
  have i₁ : InScr B Z t.mem u₁.mem := InScr.of_frm f₁ fun r hr => by
    simp only [setupR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> unfold sW sWs sArr sFn at * <;> omega_arith
  have hY₁ : word u₁.mem B (8 * sY) = s.gpr .rcx := by
    rw [hp₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hY
  have hK₁ : word u₁.mem B (8 * sK) = BitVec.ofNat 64 k := by
    rw [hp₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hK
  -- y into `aXm`.
  refine wp_seqs_append (by simp [Crt.loadArr]) (by simp [rangeTest, range, gt1, ltArr, cmpArr])
    (WP.mono (primeLoad_ok hc₁ (by omega_arith) (Nat.le_refl _) (by omega_arith) (show aXm < 8 by decide) (show sY < 32 by decide)
      (show sK < 32 by decide) hY₁ (by rw [bytesAt_length]; exact hK₁) (hyS.congrK i₁ k₁) (by rw [bytesAt_length]; omega_arith)
      (by rw [bytesAt_length]; omega_arith) (by rw [bytesAt_length])) fun u₂ ⟨hc₂, hy₂, ho₂, k₂⟩ => ?_)
  have f₂ : Frm (off B (inner ((k + 7) / 8))) [(slot ((k + 7) / 8) aXm, 8 * ((k + 7) / 8 + 2))] u₁.mem u₂.mem :=
    Frm.of_outside ho₂ (by simp)
  have hv₂ := hv₁.of_frmA hc₁.good.scr.nowrap (by omega_arith) f₂ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact arr_off _ (by decide) (by decide))
  -- `1 < y < p − 1`.
  refine wp_seqs_append (by simp [rangeTest, range, gt1, ltArr, cmpArr]) (by simp) (WP.mono (rangeTest_ok hc₂.good (Nat.le_refl _)
    (by omega_arith) (by omega_arith) (show aXm < 8 by decide) (by decide) hv₂.one) fun u₃ ⟨h9₃, hz₃, _, f₃, k₃⟩ => ?_)
  rw [hy₂, hv₂.n] at h9₃
  have hpk : (domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)).p =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k) := domainOf_p _ _ (by rcases hdl with h | h <;> omega_arith)
  have hrange : (1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) ∧
      2 * (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) / 2) + 1 <
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k)) ↔
      (1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) ∧ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) <
        (domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)).p - 1) := by
    rw [hpk, lt_pm1 hodd]
  have K₃ : Keep (.rdi :: mmRegs) t u₃ := keep_trans (keep_trans k₁ (k₂.mono (by decide))) (k₃.mono (by decide))
  have r₃ : ∀ r ∈ [(slot ((k + 7) / 8) aTmp, 8 * ((k + 7) / 8)), (8 * sF, 8)], 8 * 17 ≤ r.1 ∧
      r.1 + r.2 ≤ slot ((k + 7) / 8) 8 := by
    have := slot_le (w := (k + 7) / 8) (show aTmp < 8 by decide)
    have := hdr_lt_slot ((k + 7) / 8) aTmp (show 31 < 32 by decide)
    have := hdr_lt_slot ((k + 7) / 8) 8 (show sF < 32 by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> unfold sF sFn at * <;> omega_arith
  have hc₃ := hc₂.of_frm f₃ r₃ k₃.2.2 (k₃.gpr (by decide))
  have hv₃ := hv₂.of_frmA hc₂.good.scr.nowrap (by omega_arith) f₃ (fun r hr => by
    have := slot_le (w := (k + 7) / 8) (show aTmp < 8 by decide)
    have := hdr_lt_slot ((k + 7) / 8) aN (show sF < 32 by decide)
    have := hdr_lt_slot ((k + 7) / 8) aOne (show sF < 32 by decide)
    have s1 := slot_sep (w := (k + 7) / 8) (show aTmp ≠ aN by decide)
    have s2 := slot_sep (w := (k + 7) / 8) (show aTmp ≠ aOne by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith)
  obtain ⟨hb₂, hi₂⟩ := child_frm hc₁ (by unfold inner at hroom ⊢; omega_arith) f₂ (fun r hr => by
    rw [List.mem_singleton.mp hr]; have := slot_le (w := (k + 7) / 8) (show aXm < 8 by decide)
    unfold tabBytes; simp only; omega_arith)
  obtain ⟨hb₃, hi₃⟩ := child_frm hc₂ (by unfold inner at hroom ⊢; omega_arith) f₃ (fun r hr => by
    have := r₃ r hr; unfold tabBytes; omega_arith)
  have hw₃ : ∀ i < 32, word u₃.mem B (8 * i) = word u₁.mem B (8 * i) := fun i hi => by rw [hb₃ i hi, hb₂ i hi]
  have i₃ : InScr B Z t.mem u₃.mem := (i₁.trans hi₂).trans hi₃
  have saved₃ : ∀ i < 6, word u₃.mem B (8 * i) = word t.mem B (8 * i) := by
    intro i hi
    rw [hw₃ i (by omega), hp₁ i (by omega) (by unfold sW; omega) (by unfold sWs sFn; omega)
      (by unfold sArr; omega)]
  simp only [seqs]
  refine WP.ite (!decide (1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) ∧
    2 * (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) / 2) + 1 <
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k)))
    (by rw [hy₂, hv₂.n] at hz₃; simp [eval, hz₃]) (fun hn => ?_) (fun hp => ?_)
  · have hP : ¬ (1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) ∧
        2 * (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) / 2) + 1 <
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k)) := by simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using hn
    refine WP.seq (WP.mono (leave_ok hc₃) fun u₄ ⟨hdi₄, hm₄, k₄⟩ => ?_)
    refine WP.mono (ret_ok u₄ (r := 0) (by decide)) fun t' ⟨hax, hmret, k'⟩ => ⟨?_,
      (k'.gpr (by decide)).trans hdi₄, (by rw [hmret, hm₄]; exact i₃),
      (fun i hi => by rw [hmret, hm₄, saved₃ i hi]), keep_trans (keep_trans K₃ (k₄.mono (by decide))) (k'.mono (by decide))⟩
    rw [hax, ite_eq_right (by rw [publicValid_iff]; exact fun h => hP (hrange.mpr h.1))]; rfl
  have hP : 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) ∧
      2 * (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) / 2) + 1 <
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k) := by simpa only [Bool.not_eq_false', decide_eq_true_iff] using hp
  have hR := hrange.mp hP
  -- Back to the outer workspace, and whether there is q.
  refine WP.seq (WP.mono (leaveQ_ok hc₃ (dl := (s.gpr .rsi).toNat) (k := k)
    (by rw [hw₃ _ (by decide), hp₁ _ (by decide) (by decide) (by decide) (by decide), hL, ofNat_toNat64])
    (by rw [hw₃ _ (by decide)]; exact hK₁) (by rcases hdl with h | h <;> omega_arith)
    (by rcases hdl with h | h <;> omega_arith)) fun u₄ ⟨h0₄, h3₄, hz₄, hm₄, k₄⟩ => ?_)
  have K₄ : Keep (.rdi :: mmRegs) t u₄ := keep_trans K₃ (k₄.mono (by decide))
  rcases hdl with hdl | hdl
  · -- No q.
    have hq : (domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)).q = none := by
      rw [hdl]; exact domainOf_q2 _ _ (by omega_arith)
    refine WP.ite true (by simp [eval, hz₄, hdl]) (fun _ => ?_) (fun h => by simp at h)
    refine WP.mono (ret_ok u₄ (by decide)) fun t' ⟨h0', hmret, k'⟩ => ⟨?_, (k'.gpr (by decide)).trans h0₄, (by rw [hmret, hm₄]; exact i₃),
      (fun i hi => by rw [hmret, hm₄, saved₃ i hi]), keep_trans K₄ (k'.mono (by decide))⟩
    rw [h0', ite_eq_left (by rw [publicValid_iff, hq]; exact ⟨hR, fun _ h => by simp at h⟩)]; rfl
  · -- With q.
    have hq : (domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)).q =
        some (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi + BitVec.ofNat 64 (2 * k)) k)) := by
      rw [hdl]; exact domainOf_q3 _ _ _
    refine WP.ite false (by simp [eval, hz₄, hdl, show 3 * k ≠ 2 * k by omega]) (fun h => by simp at h)
      (fun _ => ?_)
    have hc₄ := hc₃.toMem.congr hm₄ k₄.2.2
    have hv₄ : XVals u₄ B (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k)) :=
      ⟨by rw [hm₄]; exact hv₃.n, by rw [hm₄]; exact hv₃.inv, by rw [hm₄]; exact hv₃.one⟩
    have hw₄ : ∀ i < 32, word u₄.mem B (8 * i) = word u₁.mem B (8 * i) := fun i hi => by rw [hm₄, hw₃ i hi]
    have i₄ : InScr B Z t.mem u₄.mem := i₃.trans (by rw [hm₄]; exact InScr.refl _ _ _)
    rw [hdl] at hsrcD
    refine WP.mono (cpQ_ok M E R hc₄ hv₄ hval hk1 hk2 hZ h0₄ (by rw [hw₄ _ (by decide)]; exact hWs₁)
      (by rw [hw₄ _ (by decide)]; exact hK₁)
      (by rw [hw₄ _ (by decide), hp₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hQ)
      (by rw [hw₄ _ (by decide)]; exact hY₁) (hsrcD.congrK i₄ K₄) (hyS.congrK i₄ K₄))
      fun t' ⟨h0', hdi', hFrameQ, hSavedQ, k'⟩ => ⟨?_, hdi', i₄.trans hFrameQ, (fun i hi => by rw [hSavedQ i hi, hm₄, saved₃ i hi]), keep_trans K₄ (k'.mono (by decide))⟩
    have e : publicValid ⟨domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat),
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k)⟩ = true ↔
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) ^
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi + BitVec.ofNat 64 (2 * k)) k) %
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k) = 1 := by
      rw [publicValid_iff, hq, hpk]
      simp only [Option.some.injEq, forall_eq']
      exact ⟨fun h => h.2, fun h => ⟨hpk ▸ hR, h⟩⟩
    rw [h0']; unfold bit; exact if_congr e.symm rfl rfl


end VG.Proof.Ffdh.X86_64.CheckPublic
