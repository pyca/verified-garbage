module
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Context
public import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Ffdh.X86_64.Scan
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Entry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead

/-! ### `Ffdh.X86_64.CheckPublic.Main`, which only this module used -/

section

/-! ### `Ffdh.X86_64.CheckPublic.Subgroup`, which only this module used -/

section

/-! # FFDH public-key validation on x86-64: subgroup membership -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh VG.Proof.MlKem.X86_64

/-- With q: its first nonzero octet, `R² mod p`, `y^q mod p` and whether it is 1. -/
theorem cpQ_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {u : State} {B : Addr} {Z k : Nat} {mi : BitVec 64}
    {m₀ : Mem} {dp yp : Addr}
    (hc : SubMem u B Z (inner ((k + 7) / 8)) ((k + 7) / 8) ((k + 7) / 8) mi)
    (hv : XVals u B (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ dp k)))
    (hval : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ dp k)) k = true) (hk1 : 64 ≤ k)
    (hk2 : k ≤ 1024) (hZ : 128 * k + 256 ≤ Z) (h0 : u.gpr .rdi = B)
    (hWs : word u.mem B (8 * sWs) = off B (inner ((k + 7) / 8))) (hK : word u.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hQ : word u.mem B (8 * sQ) = dp + BitVec.ofNat 64 (2 * k)) (hY : word u.mem B (8 * sY) = yp)
    (hdom : Src u B Z dp (Spec.Rsa.bytesAt m₀ dp (3 * k)))
    (hy : Src u B Z yp (Spec.Rsa.bytesAt m₀ yp k)) :
    WP isa (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup M.mm E.code (.seq (.block r2Head) R.code))) u fun t =>
      t.gpr .rax = bit (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ yp k) ^
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k) %
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ dp k) = 1) ∧ t.gpr .rdi = B ∧ InScr B Z u.mem t.mem ∧ (∀ i < 6, word t.mem B (8 * i) = word u.mem B (8 * i)) ∧ Keep (.rdi :: mmRegs) u t := by
  obtain hroom := room_k hk1 hZ
  obtain hO : Outer u B Z ((k + 7) / 8) := Outer.of_mem hc h0 hroom (by omega_arith) (by omega_arith)
  obtain hq := src_slice (off := 2 * k) (len := k) hdom (by omega_arith)
  obtain hql : (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k).length = k := bytesAt_length _ _ _
  obtain hne : Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k ≠ [] := by
    intro h; rw [h] at hql; simp at hql; omega_arith
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- The first nonzero octet of q.
  refine wp_seqs_append (by simp [scan]) (by simp) (WP.mono (scan_ok hO (show sQ < 32 by decide) hQ
    (by rw [hql]; exact hK) hne (by omega_arith) hq) fun u₁ ⟨hEp, hEl, _, f₁, k₁⟩ => ?_)
  obtain hr₁ : ∀ r ∈ [(8 * sEp, 8), (8 * sEl, 8)], 8 * 16 ≤ r.1 ∧ r.1 + r.2 ≤ 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [sEp, sEl, sFn] <;> omega_arith
  obtain hc₁ := hc.of_parent f₁ hr₁ k₁.2.2
  obtain hv₁ := hv.of_parent hc f₁ (fun r hr => (hr₁ r hr).2)
  obtain hO₁ : Outer u₁ B Z ((k + 7) / 8) := Outer.of_mem hc₁ ((k₁.gpr (by decide)).trans h0) hroom (by omega_arith)
    (by omega_arith)
  obtain hs₁ : ∀ i < 32, i ≠ sEp → i ≠ sEl → word u₁.mem B (8 * i) = word u.mem B (8 * i) := fun i hi h1 h2 =>
    f₁.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> unfold sEp sEl sFn at * <;> omega_arith) (by omega_arith)
  obtain i₁ : InScr B Z u.mem u₁.mem := InScr.of_frm f₁ fun r hr => by
    have := (hr₁ r hr).2; have := hroom; unfold inner slot hdrBytes at this; omega_arith
  -- Into the inner workspace, and `R² mod p`.
  obtain hWs₁ : word u₁.mem B (8 * sWs) = off B (inner ((k + 7) / 8)) := by
    rw [hs₁ _ (by decide) (by decide) (by decide)]; exact hWs
  refine wp_seqs_cons (by simp) (WP.mono (enter_ok hO₁ hWs₁) fun u₂ ⟨h0₂, hm₂, k₂⟩ => ?_)
  obtain hc₂ : SubCtx u₂ B Z (inner ((k + 7) / 8)) ((k + 7) / 8) ((k + 7) / 8) mi :=
    ⟨hc₁.scr.congr k₂.2.2, h0₂, by rw [hm₂]; exact hc₁.hdr, by rw [hm₂]; exact hc₁.link, by rw [hm₂]; exact hc₁.nw,
      by rw [hm₂]; exact hc₁.narr, hc₁.lo, hc₁.hi⟩
  obtain hv₂ : XVals u₂ B (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ dp k)) :=
    ⟨by rw [hm₂]; exact hv₁.n, by rw [hm₂]; exact hv₁.inv, by rw [hm₂]; exact hv₁.one⟩
  refine wp_seqs_cons (by simp [pow, Crt.loadArr]) (WP.mono (r2_ctx M R hc₂ hv₂ hval hk1 hk2 hZ)
    fun u₃ ⟨hm₃, f₃, k₃⟩ => ?_)
  -- The power and its comparison with 1.
  obtain hlead := lead_lt hne
  rw [hql] at hlead
  obtain ⟨hb₃, hi₃⟩ := child_frm hc₂ (by have := hroom; unfold inner at this ⊢; omega_arith) f₃ (fun r hr => by
    have := r2Ranges_le ((k + 7) / 8) r hr; unfold tabBytes; omega_arith)
  obtain hw₃ : ∀ i < 32, i ≠ sEp → i ≠ sEl → word u₃.mem B (8 * i) = word u.mem B (8 * i) := fun i hi h1 h2 => by
    rw [hb₃ i hi, hm₂, hs₁ i hi h1 h2]
  obtain hs₃ : InScr B Z u.mem u₃.mem := (i₁.trans (by rw [hm₂]; exact InScr.refl _ _ _)).trans hi₃
  obtain K₃ : Keep (.rdi :: mmRegs) u u₃ :=
    keep_trans (keep_trans (k₁.mono (by decide)) (k₂.mono (by decide))) (k₃.mono (by decide))
  obtain heS := src_slice (off := lead (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k))
    (len := k - lead (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k)) hq (by omega_arith)
  rw [← List.append_assoc]
  refine wp_seqs_append (by simp [pow, Crt.loadArr]) (by simp) (WP.mono (powOne_ok M E hm₃ (bp := sY) (bl := sK)
    (ep := sEp) (el := sEl) (by decide) (by decide) (by decide) (by decide)
    (by rw [hw₃ _ (by decide) (by decide) (by decide)]; exact hY)
    (by rw [hw₃ _ (by decide) (by decide) (by decide), bytesAt_length]; exact hK)
    (hy.congrK hs₃ K₃) (by rw [bytesAt_length]; omega_arith) (by rw [bytesAt_length])
    (by rw [hb₃ _ (by decide), hm₂]; exact hEp)
    (by rw [hb₃ _ (by decide), hm₂, bytesAt_length, hEl, hql])
    (heS.congrK hs₃ K₃) (by rw [bytesAt_length]; omega_arith) (by rw [bytesAt_length]; omega_arith))
    fun u₄ ⟨hc₄, h9₄, f₄, k₄⟩ => ?_)
  obtain ⟨hb₄, hi₄⟩ := child_frm hm₃.sub hm₃.wide f₄ (fun r hr => (powRanges_ok _ r hr).2)
  refine WP.mono (leave_ok hc₄.sub) fun t ⟨hdi, hm, k₅⟩ => ⟨?_, hdi, ?_, ?_, ?_⟩
  · rw [(k₅.gpr (by decide) : t.gpr .rax = u₄.gpr .rax), h9₄]
    obtain e : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k) +
        BitVec.ofNat 64 (lead (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k)))
        (k - lead (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k))) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k) := by
      rw [← VG.Proof.Dsa.bytesAt_slice m₀ _ (show lead _ + (k - lead _) ≤ k by omega_arith)]
      generalize Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k = L at hql ⊢
      rw [List.take_of_length_le (by simp; omega_arith), os2ip_drop_lead]
    rw [e]
  · rw [hm]; exact hs₃.trans hi₄
  · intro i hi
    rw [hm, hb₄ i (by omega_using [hi]), hw₃ i (by omega_using [hi]) (by unfold sEp sFn; omega_using [hi]) (by unfold sEl sFn; omega_using [hi])]
  · exact keep_trans (keep_trans K₃ (k₄.mono (by decide))) (k₅.mono (by decide))


end VG.Proof.Ffdh.X86_64.CheckPublic

end

end


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
  obtain hroom := room_k hk1 hZ
  obtain ⟨hodd, hp1, hlo⟩ := valid_facts hval hk1
  obtain hsrcD := hdom.congr i₀ hrd hwr
  obtain hpS : Src t B Z (s.gpr .rdi) (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k) := by
    have := src_slice (off := 0) (len := k) hsrcD (by rcases hdl with h | h <;> rw [h] <;> omega_arith)
    simpa using this
  obtain hyS : Src t B Z (s.gpr .rcx) (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) := hy.congr i₀ hrd hwr
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
  obtain h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  obtain hi8 : 8 * 32 ≤ inner ((k + 7) / 8) := by simp only [inner, slot, hdrBytes]; omega_arith
  obtain hiZ : inner ((k + 7) / 8) + slot ((k + 7) / 8) 8 ≤ Z := by unfold tabBytes at hroom; omega_arith
  obtain hp₁ : ∀ i < 32, i ≠ sW → i ≠ sWs → (i < sArr 0 ∨ sArr 0 + 8 ≤ i) →
      word u₁.mem B (8 * i) = word t.mem B (8 * i) := fun i hi h1 h2 h3 =>
    f₁.word_eq (fun r hr => by
      simp only [setupR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> unfold sW sWs sArr sFn at * <;> omega_arith) (by omega_arith)
  obtain i₁ : InScr B Z t.mem u₁.mem := InScr.of_frm f₁ fun r hr => by
    simp only [setupR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> unfold sW sWs sArr sFn at * <;> omega_arith
  obtain hY₁ : word u₁.mem B (8 * sY) = s.gpr .rcx := by
    rw [hp₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hY
  obtain hK₁ : word u₁.mem B (8 * sK) = BitVec.ofNat 64 k := by
    rw [hp₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hK
  -- y into `aXm`.
  refine wp_seqs_append (by simp [Crt.loadArr]) (by simp [rangeTest, range, gt1, ltArr, cmpArr])
    (WP.mono (primeLoad_ok hc₁ (by omega_arith) (Nat.le_refl _) (by omega_arith) (show aXm < 8 by decide) (show sY < 32 by decide)
      (show sK < 32 by decide) hY₁ (by rw [bytesAt_length]; exact hK₁) (hyS.congrK i₁ k₁) (by rw [bytesAt_length]; omega_arith)
      (by rw [bytesAt_length]; omega_arith) (by rw [bytesAt_length])) fun u₂ ⟨hc₂, hy₂, ho₂, k₂⟩ => ?_)
  obtain f₂ : Frm (off B (inner ((k + 7) / 8))) [(slot ((k + 7) / 8) aXm, 8 * ((k + 7) / 8 + 2))] u₁.mem u₂.mem :=
    Frm.of_outside ho₂ (by simp)
  obtain hv₂ := hv₁.of_frmA hc₁.good.scr.nowrap (by omega_arith) f₂ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact arr_off _ (by decide) (by decide))
  -- `1 < y < p − 1`.
  refine wp_seqs_append (by simp [rangeTest, range, gt1, ltArr, cmpArr]) (by simp) (WP.mono (rangeTest_ok hc₂.good (Nat.le_refl _)
    (by omega_arith) (by omega_arith) (show aXm < 8 by decide) (by decide) hv₂.one) fun u₃ ⟨h9₃, hz₃, _, f₃, k₃⟩ => ?_)
  rw [hy₂, hv₂.n] at h9₃
  obtain hpk : (domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)).p =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k) := domainOf_p _ _ (by rcases hdl with h | h <;> omega_arith)
  obtain hrange : (1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) ∧
      2 * (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) / 2) + 1 <
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k)) ↔
      (1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) ∧ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) <
        (domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)).p - 1) := by
    rw [hpk, lt_pm1 hodd]
  obtain K₃ : Keep (.rdi :: mmRegs) t u₃ := keep_trans (keep_trans k₁ (k₂.mono (by decide))) (k₃.mono (by decide))
  obtain r₃ : ∀ r ∈ [(slot ((k + 7) / 8) aTmp, 8 * ((k + 7) / 8)), (8 * sF, 8)], 8 * 17 ≤ r.1 ∧
      r.1 + r.2 ≤ slot ((k + 7) / 8) 8 := by
    have := slot_le (w := (k + 7) / 8) (show aTmp < 8 by decide)
    have := hdr_lt_slot ((k + 7) / 8) aTmp (show 31 < 32 by decide)
    have := hdr_lt_slot ((k + 7) / 8) 8 (show sF < 32 by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> unfold sF sFn at * <;> omega_arith
  obtain hc₃ := hc₂.of_frm f₃ r₃ k₃.2.2 (k₃.gpr (by decide))
  obtain hv₃ := hv₂.of_frmA hc₂.good.scr.nowrap (by omega_arith) f₃ (fun r hr => by
    have := slot_le (w := (k + 7) / 8) (show aTmp < 8 by decide)
    have := hdr_lt_slot ((k + 7) / 8) aN (show sF < 32 by decide)
    have := hdr_lt_slot ((k + 7) / 8) aOne (show sF < 32 by decide)
    obtain s1 := slot_sep (w := (k + 7) / 8) (show aTmp ≠ aN by decide)
    obtain s2 := slot_sep (w := (k + 7) / 8) (show aTmp ≠ aOne by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith)
  obtain ⟨hb₂, hi₂⟩ := child_frm hc₁ (by unfold inner at hroom ⊢; omega_arith) f₂ (fun r hr => by
    rw [List.mem_singleton.mp hr]; have := slot_le (w := (k + 7) / 8) (show aXm < 8 by decide)
    unfold tabBytes; simp only; omega_arith)
  obtain ⟨hb₃, hi₃⟩ := child_frm hc₂ (by unfold inner at hroom ⊢; omega_arith) f₃ (fun r hr => by
    have := r₃ r hr; unfold tabBytes; omega_arith)
  obtain hw₃ : ∀ i < 32, word u₃.mem B (8 * i) = word u₁.mem B (8 * i) := fun i hi => by rw [hb₃ i hi, hb₂ i hi]
  obtain i₃ : InScr B Z t.mem u₃.mem := (i₁.trans hi₂).trans hi₃
  obtain saved₃ : ∀ i < 6, word u₃.mem B (8 * i) = word t.mem B (8 * i) := by
    intro i hi
    rw [hw₃ i (by omega_arith), hp₁ i (by omega_arith) (by unfold sW; omega_arith) (by unfold sWs sFn; omega_arith)
      (by unfold sArr; omega_arith)]
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
  obtain hP : 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) ∧
      2 * (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) / 2) + 1 <
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k) := by simpa only [Bool.not_eq_false', decide_eq_true_iff] using hp
  obtain hR := hrange.mp hP
  -- Back to the outer workspace, and whether there is q.
  refine WP.seq (WP.mono (leaveQ_ok hc₃ (dl := (s.gpr .rsi).toNat) (k := k)
    (by rw [hw₃ _ (by decide), hp₁ _ (by decide) (by decide) (by decide) (by decide), hL, ofNat_toNat64])
    (by rw [hw₃ _ (by decide)]; exact hK₁) (by rcases hdl with h | h <;> omega_arith)
    (by rcases hdl with h | h <;> omega_arith)) fun u₄ ⟨h0₄, h3₄, hz₄, hm₄, k₄⟩ => ?_)
  obtain K₄ : Keep (.rdi :: mmRegs) t u₄ := keep_trans K₃ (k₄.mono (by decide))
  rcases hdl with hdl | hdl
  · -- No q.
    obtain hq : (domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)).q = none := by
      rw [hdl]; exact domainOf_q2 _ _ (by omega_arith)
    refine WP.ite true (by simp [eval, hz₄, hdl]) (fun _ => ?_) (fun h => by simp at h)
    refine WP.mono (ret_ok u₄ (by decide)) fun t' ⟨h0', hmret, k'⟩ => ⟨?_, (k'.gpr (by decide)).trans h0₄, (by rw [hmret, hm₄]; exact i₃),
      (fun i hi => by rw [hmret, hm₄, saved₃ i hi]), keep_trans K₄ (k'.mono (by decide))⟩
    rw [h0', ite_eq_left (by rw [publicValid_iff, hq]; exact ⟨hR, fun _ h => by simp at h⟩)]; rfl
  · -- With q.
    obtain hq : (domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)).q =
        some (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi + BitVec.ofNat 64 (2 * k)) k)) := by
      rw [hdl]; exact domainOf_q3 _ _ _
    refine WP.ite false (by simp [eval, hz₄, hdl, show 3 * k ≠ 2 * k by omega_arith]) (fun h => by simp at h)
      (fun _ => ?_)
    obtain hc₄ := hc₃.toMem.congr hm₄ k₄.2.2
    obtain hv₄ : XVals u₄ B (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k)) :=
      ⟨by rw [hm₄]; exact hv₃.n, by rw [hm₄]; exact hv₃.inv, by rw [hm₄]; exact hv₃.one⟩
    obtain hw₄ : ∀ i < 32, word u₄.mem B (8 * i) = word u₁.mem B (8 * i) := fun i hi => by rw [hm₄, hw₃ i hi]
    obtain i₄ : InScr B Z t.mem u₄.mem := i₃.trans (by rw [hm₄]; exact InScr.refl _ _ _)
    rw [hdl] at hsrcD
    refine WP.mono (cpQ_ok M E R hc₄ hv₄ hval hk1 hk2 hZ h0₄ (by rw [hw₄ _ (by decide)]; exact hWs₁)
      (by rw [hw₄ _ (by decide)]; exact hK₁)
      (by rw [hw₄ _ (by decide), hp₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hQ)
      (by rw [hw₄ _ (by decide)]; exact hY₁) (hsrcD.congrK i₄ K₄) (hyS.congrK i₄ K₄))
      fun t' ⟨h0', hdi', hFrameQ, hSavedQ, k'⟩ => ⟨?_, hdi', i₄.trans hFrameQ, (fun i hi => by rw [hSavedQ i hi, hm₄, saved₃ i hi]), keep_trans K₄ (k'.mono (by decide))⟩
    obtain e : publicValid ⟨domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat),
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k)⟩ = true ↔
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) k) ^
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi + BitVec.ofNat 64 (2 * k)) k) %
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k) = 1 := by
      rw [publicValid_iff, hq, hpk]
      simp only [Option.some.injEq, forall_eq']
      exact ⟨fun h => h.2, fun h => ⟨hpk ▸ hR, h⟩⟩
    rw [h0']; unfold bit; exact if_congr e.symm rfl rfl


end VG.Proof.Ffdh.X86_64.CheckPublic

end

end


/-! # FFDH public-key validation on x86-64: correctness before the ABI epilogue -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh VG.Proof.MlKem.X86_64
open VG.Spec.Ffdh

theorem cp_body_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {s : State} (c : CpCtx s) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.body M.mm E.code (.seq (.block r2Head) R.code)) s fun t =>
      cpPost s t ∧ t.gpr .rdi = s.gpr .r9 ∧ InScr (s.gpr .r9) ((scrLen s).toNat * 8) s.mem t.mem ∧
      (∀ i < 6, word t.mem (s.gpr .r9) (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Keep (.rdi :: mmRegs) s t := by
  have hk1 := c.k1
  have hk2 := c.k2
  have hZ := c.hZ
  have hn := c.hs.nowrap
  obtain hw : ∀ i < 20, InRegions s.wr (off (s.gpr .r9) (8 * i)) 8 := fun i hi => c.hs.st (by omega_using [hZ, hi])
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPublic.body
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (cpEntry_ok rfl hw) fun s₁ ⟨hdi₁, saved₁, slots₁, ho₁, k₁⟩ => ?_
  obtain hD₁ := slots₁ (sDom, s.gpr .rdi) (by simp)
  obtain hL₁ := slots₁ (sDomLen, s.gpr .rsi) (by simp)
  obtain hK₁ := slots₁ (sK, s.gpr .rdx) (by simp)
  obtain hY₁ := slots₁ (sY, s.gpr .rcx) (by simp)
  obtain i₁ : InScr (s.gpr .r9) ((scrLen s).toNat * 8) s.mem s₁.mem := InScr.of_outside ho₁ (by omega_using [hZ])
  obtain hdom₁ := c.dom.congrK i₁ k₁
  obtain hpS : Src s₁ (s.gpr .r9) ((scrLen s).toNat * 8) (s.gpr .rdi)
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rdx).toNat) := by
    have := src_slice (off := 0) (len := (s.gpr .rdx).toNat) hdom₁
      (by rcases c.dl with h | h <;> rw [h] <;> omega_using [])
    simpa using this
  refine WP.mono (domHead_ok (c.hs.congr k₁.2.2) hdi₁ (by omega_using [hZ]) hk1 hk2 hD₁
    (by rw [hK₁, ofNat_toNat64]) hpS (bytesAt_length _ _ _))
    fun s₂ ⟨hz₂, _, hQ₂, f₂, hdi₂, k₂⟩ => ?_
  obtain hp₂ : ∀ i < 32, i ≠ sG → i ≠ sQ →
      word s₂.mem (s.gpr .r9) (8 * i) = word s₁.mem (s.gpr .r9) (8 * i) := fun i hi h1 h2 =>
    f₂.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> unfold sG sQ sFn at * <;> omega_arith) (by omega_using [hi])
  obtain i₂ : InScr (s.gpr .r9) ((scrLen s).toNat * 8) s.mem s₂.mem :=
    i₁.trans (InScr.of_frm f₂ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only [sG, sQ, sFn] <;> omega_using [hZ]))
  obtain K₂ : Keep (.rdi :: mmRegs) s s₂ := keep_trans (k₁.mono (by decide)) (k₂.mono (by decide))
  obtain saved₂ : ∀ i < 6, word s₂.mem (s.gpr .r9) (8 * i) = s.gpr (saved.getD i .rax) := fun i hi => by
    rw [hp₂ i (by omega_using [hi]) (by unfold sG sFn; omega_using [hi]) (by unfold sQ sFn; omega_using [hi])]
    exact saved₁ i hi
  obtain hpk : (domainOf (s.gpr .rdx).toNat (cpDom s)).p =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rdx).toNat) :=
    domainOf_p _ _ (by rcases c.dl with h | h <;> omega_using [h])
  refine WP.ite (!Spec.Rsa.modulusValid
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rdx).toNat)) (s.gpr .rdx).toNat)
    (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rdx).toNat)) (s.gpr .rdx).toNat = false :=
      by simpa only [Bool.not_eq_true'] using hb
    refine WP.mono (ret_ok s₂ (r := 0) (by decide)) fun t ⟨_, hm, k⟩ =>
      ⟨?_, (k.gpr (by decide)).trans hdi₂, by rw [hm]; exact i₂,
        (fun i hi => by rw [hm]; exact saved₂ i hi), keep_trans K₂ (k.mono (by decide))⟩
    intro hd
    have := domainValid_mod hd
    rw [hpk, hv] at this
    exact absurd this (by decide)
  · have hv : Spec.Rsa.modulusValid
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rdx).toNat)) (s.gpr .rdx).toNat = true :=
      by simpa only [Bool.not_eq_false'] using hb
    refine WP.mono (cpMain_ok M E R c hdi₂ (c.hs.congr (k₂.2.2.trans k₁.2.2))
      (by rw [hp₂ _ (by decide) (by decide) (by decide)]; exact hD₁)
      (by rw [hp₂ _ (by decide) (by decide) (by decide)]; exact hL₁)
      (by rw [hp₂ _ (by decide) (by decide) (by decide), hK₁, ofNat_toNat64])
      (by rw [hp₂ _ (by decide) (by decide) (by decide)]; exact hY₁)
      hQ₂ i₂ (k₂.2.1.trans k₁.2.1) (k₂.2.2.trans k₁.2.2) hv)
      fun t ⟨hax, hdi, hf, hsaved, k⟩ => ⟨?_, hdi, i₂.trans hf,
        (fun i hi => (hsaved i hi).trans (saved₂ i hi)), keep_trans K₂ k⟩
    intro _
    rw [hax]
    split <;> rfl

end VG.Proof.Ffdh.X86_64.CheckPublic
