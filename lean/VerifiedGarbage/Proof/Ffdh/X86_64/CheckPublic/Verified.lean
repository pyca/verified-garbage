module

public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Context
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
meta import VerifiedGarbage.Proof.Ffdh.X86_64.R2
meta import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Ffdh.X86_64.ScanCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ChecksCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
public import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Scan
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ScanCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ChecksCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Context
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Front
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Scan
meta import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Tactic.Push
meta import Mathlib.Data.Nat.Basic
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Ffdh.X86_64.CheckPublic.CT`, which only this module used -/

section

/-! ### `Ffdh.X86_64.CheckPublic.Body`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Ffdh.X86_64.CheckPublic.R2CT`, which only this module used -/

section

/-! ### `Ffdh.X86_64.CheckPublic.Stages`, which this module and modules that import it used -/

section

/-!
# `vg_ffdh_check_public` on X86_64: the stages of a run

Every input of `vg_ffdh_check_public` is public (`CpP`). Between the pieces
of `CheckPublic.code` whose timing the constant-time proof checks, a run from
a state with the public data `p` (`CR p`) satisfies a stage of `p`
(`E1`, `CE`, `C1` … `C8`), by the pieces' correctness. Each stage fixes what
the next piece's addresses, loop counts and branches depend on.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh
open VG.Proof.MlKem.X86_64
open VG.Spec.Ffdh

/-- The public data: the working space, the lengths, the pointers, the
domain, y and the stack pointer. -/
structure CpP where
  B : Addr
  Z : Nat
  k : Nat
  dl : Nat
  dp : Addr
  yp : Addr
  dom : List Byte
  yb : List Byte
  sp : Addr

namespace CpP

abbrev w (p : CpP) : Nat := (p.k + 7) / 8

/-- p. -/
abbrev P (p : CpP) : Nat := Spec.Rsa.os2ip (p.dom.take p.k)

/-- q's octets, for a domain with q. -/
abbrev qb (p : CpP) : List Byte := (p.dom.drop (2 * p.k)).take p.k

/-- y. -/
abbrev Y (p : CpP) : Nat := Spec.Rsa.os2ip p.yb

/-- Whether p is a valid modulus. -/
abbrev mv (p : CpP) : Bool := Spec.Rsa.modulusValid p.P p.k

/-- The front's public data. -/
abbrev d (p : CpP) : DPub := ⟨p.B, p.Z, p.k, p.dp⟩

/-- The inner workspace. -/
abbrev ws (p : CpP) : Ws := ⟨off p.B (inner p.w), slot p.w 8, p.w⟩

/-- The header slots the code reads after the entry. -/
abbrev hd (p : CpP) : List (Nat × BitVec 64) :=
  [(sDom, p.dp), (sDomLen, BitVec.ofNat 64 p.dl), (sK, BitVec.ofNat 64 p.k), (sY, p.yp)]

/-- And after `domHead`. -/
abbrev hdQ (p : CpP) : List (Nat × BitVec 64) := p.hd ++ [(sQ, p.dp + BitVec.ofNat 64 (2 * p.k))]

end CpP

/-- A state the contract allows, with the public data `p`. -/
def CR (p : CpP) (s : State) : Prop :=
  cpPre s ∧ s.gpr .rsp = p.sp ∧ s.gpr .r9 = p.B ∧ (scrLen s).toNat * 8 = p.Z ∧ (s.gpr .rdx).toNat = p.k ∧
    (s.gpr .rsi).toNat = p.dl ∧ s.gpr .rdi = p.dp ∧ s.gpr .rcx = p.yp ∧ cpDom s = p.dom ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat = p.yb

/-- What a run keeps of its start: the inputs, outside the working space,
and the permissions. -/
def Fx (p : CpP) (t : State) : Prop :=
  ∃ s, CR p s ∧ InScr p.B p.Z s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr

theorem Fx.step {p : CpP} {t u : State} (h : Fx p t) (hi : InScr p.B p.Z t.mem u.mem) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) : Fx p u :=
  let ⟨s, hs, i, r, w⟩ := h
  ⟨s, hs, i.trans hi, hrd.trans r, hwr.trans w⟩

theorem Fx.keep {p : CpP} {t u : State} (h : Fx p t) (hi : InScr p.B p.Z t.mem u.mem) {rs : List Reg}
    (k : Keep rs t u) : Fx p u := h.step hi k.2.1 k.2.2

/-- What `Fx` gives. -/
structure FxCtx (p : CpP) (t : State) : Prop where
  scr : Scr t p.B p.Z
  k1 : 64 ≤ p.k
  k2 : p.k ≤ 1024
  dl : p.dl = 2 * p.k ∨ p.dl = 3 * p.k
  hZ : 128 * p.k + 256 ≤ p.Z
  dom : Src t p.B p.Z p.dp p.dom
  doml : p.dom.length = p.dl
  y : Src t p.B p.Z p.yp p.yb
  yl : p.yb.length = p.k

theorem Fx.ctx {p : CpP} {t : State} (h : Fx p t) : FxCtx p t := by
  obtain ⟨B, Z, k, dl, dp, yp, dom, yb, sp⟩ := p
  obtain ⟨s, ⟨hpre, -, hB, hZ, hk, hdl, hdp, hyp, hdom, hyb⟩, hi, hrd, hwr⟩ := h
  have c := cpCtx_of hpre
  have hy := c.y
  rw [c.yl] at hy hyb
  subst hB hZ hk hdl hdp hyp hdom hyb
  exact ⟨c.hs.congr hwr, c.k1, c.k2, c.dl, c.hZ, c.dom.congr hi hrd hwr, bytesAt_length _ _ _, hy.congr hi hrd hwr,
    bytesAt_length _ _ _⟩

/-! ## The entry and the check of p -/

/-- After the entry. -/
def E1 (p : CpP) (t : State) : Prop := Fx p t ∧ t.gpr .rdi = p.B ∧ Slots t.mem p.B p.hd

/-- The entry's registers. -/
def entryRegs (p : CpP) (r : Reg) : BitVec 64 :=
  if r = .rdi then p.dp else if r = .rsi then BitVec.ofNat 64 p.dl else if r = .rdx then BitVec.ofNat 64 p.k else
    if r = .rcx then p.yp else p.B

theorem cr_regs (p : CpP) (s : State) (h : CR p s) : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r9], s.gpr r = entryRegs p r := by
  obtain ⟨-, -, hB, -, hk, hdl, hdp, hyp, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [entryRegs, reduceCtorEq, ↓reduceIte]
  · exact hdp
  · rw [← hdl, ofNat_toNat64]
  · rw [← hk, ofNat_toNat64]
  · exact hyp
  · exact hB

theorem cr_e1 (p : CpP) (s : State) (h : CR p s) : WP isa (.block CheckPublic.entry) s (E1 p) := by
  have c := cpCtx_of h.1
  have hn := c.hs.nowrap
  have hZ := c.hZ
  have hk1 := c.k1
  have h' := h
  obtain ⟨-, -, hB, hZ', hk, hdl, hdp, hyp, -⟩ := h'
  have hw : ∀ i < 20, InRegions s.wr (off (s.gpr .r9) (8 * i)) 8 := fun i hi => c.hs.st (by omega_arith)
  refine WP.mono (cpEntry_ok rfl hw) fun t ⟨h0, _, slots, ho, k⟩ => ?_
  have hD := slots (sDom, s.gpr .rdi) (by simp)
  have hL := slots (sDomLen, s.gpr .rsi) (by simp)
  have hK := slots (sK, s.gpr .rdx) (by simp)
  have hY := slots (sY, s.gpr .rcx) (by simp)
  rw [hB] at h0 hD hL hK hY ho
  rw [hZ'] at hn hZ
  refine ⟨⟨s, h, InScr.of_outside ho (by rw [← hZ']; omega_arith), k.2.1, k.2.2⟩, h0, ?_⟩
  intro q hq
  simp only [CpP.hd, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact hD.trans hdp
  · rw [hL, ← hdl, ofNat_toNat64]
  · rw [hK, ← hk, ofNat_toNat64]
  · exact hY.trans hyp

theorem e1_dhp (p : CpP) (t : State) (h : E1 p t) : DHP p.d t := by
  obtain ⟨hx, h0, hs⟩ := h
  have c := hx.ctx
  have := c.hZ
  exact ⟨c.scr, h0, show 256 ≤ p.Z by omega_arith, hs (sDom, p.dp) (by simp), hs (sK, BitVec.ofNat 64 p.k) (by simp)⟩

/-- After `domHead`. -/
def CE (p : CpP) (t : State) : Prop :=
  Fx p t ∧ t.gpr .rdi = p.B ∧ Slots t.mem p.B p.hdQ ∧ t.zf = some p.mv

theorem e1_ce (p : CpP) (t : State) (h : E1 p t) : WP isa (.block domHead) t (CE p) := by
  obtain ⟨hx, h0, hs⟩ := h
  have c := hx.ctx
  have hn := c.scr.nowrap
  have hZ := c.hZ
  have hl : (p.dom.take p.k).length = p.k := by rw [List.length_take, c.doml]; rcases c.dl with h | h <;> omega_arith
  refine WP.mono (domHead_ok c.scr h0 (by omega_arith) c.k1 c.k2 (hs (sDom, p.dp) (by simp)) (hs (sK, BitVec.ofNat 64 p.k) (by simp)) (c.dom.take p.k) hl)
    fun u ⟨h9, _, hQ, f, h0', k⟩ => ⟨hx.keep (InScr.of_frm f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sG, sQ, sFn] <;> omega_arith) k, h0', ?_, h9⟩
  have hs' : Slots u.mem p.B p.hd := hs.frm f (fun q hq r hr => by
      simp only [CpP.hd, List.mem_cons, List.not_mem_nil, or_false] at hq hr
      rcases hq with rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl <;>
        simp only [sG, sQ, sDom, sDomLen, sK, sY, sFn] <;> omega_arith)
    (fun q hq => by
      simp only [CpP.hd, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp only [sDom, sDomLen, sK, sY, sFn] <;> omega_arith)
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hs' q hq
  · rw [List.mem_singleton.mp hq]; exact hQ

theorem ce_eval {p : CpP} {t : State} (h : CE p t) :
    isa.eval .ne t = some (!p.mv) := by
  simp [eval, h.2.2.2]

theorem ce_valid {p : CpP} {t : State} (h : CE p t) (he : isa.eval .ne t = some false) : p.mv = true := by
  rw [ce_eval h] at he
  cases hv : p.mv
  · rw [hv] at he; simp at he
  · rfl

theorem ce_setupP (p : CpP) (t : State) (h : CE p t) (he : isa.eval .ne t = some false) :
    SetupP p.d t := by
  have hv := ce_valid h he
  obtain ⟨hx, h0, hs, -⟩ := h
  have c := hx.ctx
  have hl : (p.dom.take p.k).length = p.k := by rw [List.length_take, c.doml]; rcases c.dl with h | h <;> omega_arith
  obtain ⟨hodd, -⟩ := valid_facts hv c.k1
  exact ⟨p.dom.take p.k, c.scr, h0, c.k1, c.k2, c.hZ, hs (sDom, p.dp) (by simp), hs (sK, BitVec.ofNat 64 p.k) (by simp), c.dom.take p.k, hl, hodd⟩

/-! ## The workspaces, y and its range -/

/-- In the inner workspace for p. -/
def C1 (p : CpP) (t : State) : Prop :=
  ∃ mi, Fx p t ∧ SubCtx t p.B p.Z (inner p.w) p.w p.w mi ∧ XVals t p.B (inner p.w) p.w mi p.P ∧
    word t.mem p.B (8 * sWs) = off p.B (inner p.w) ∧ Slots t.mem p.B p.hdQ ∧ p.mv = true

theorem ce_c1 (p : CpP) (t : State) (h : CE p t) (he : isa.eval .ne t = some false) :
    WP isa (seqs (([.block head] : List (Prog isa)) ++ pSetup)) t (C1 p) := by
  have hv := ce_valid h he
  obtain ⟨hx, h0, hs, -⟩ := h
  have c := hx.ctx
  have hn := c.scr.nowrap
  have hZ := c.hZ
  have hroom := room_k c.k1 hZ
  have hl : (p.dom.take p.k).length = p.k := by rw [List.length_take, c.doml]; rcases c.dl with h | h <;> omega_arith
  obtain ⟨hodd, -⟩ := valid_facts hv c.k1
  refine WP.mono (setup_ok c.scr h0 c.k1 c.k2 hZ (hs (sDom, p.dp) (by simp)) (hs (sK, BitVec.ofNat 64 p.k) (by simp)) (c.dom.take p.k) hl hodd)
    fun u ⟨mi, hc, hX, hWs, f, k⟩ => ⟨mi, hx.keep (InScr.of_frm f fun r hr => by
      simp only [setupR, List.mem_cons, List.not_mem_nil, or_false] at hr
      unfold inner slot hdrBytes tabBytes at hroom
      rcases hr with rfl | rfl | rfl | rfl <;> simp only [sW, sArr, sWs, sFn, inner, slot, hdrBytes] <;> omega_arith) k,
      hc, hX, hWs, fun q hq => ?_, hv⟩
  rw [f.word_eq (fun r hr => by
      simp only [setupR, List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [CpP.hdQ, CpP.hd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;>
        rcases hr with rfl | rfl | rfl | rfl <;>
          simp only [sW, sArr, sWs, sDom, sDomLen, sK, sY, sQ, sFn, inner, slot, hdrBytes] <;> omega_arith)
    (by unfold inner slot hdrBytes tabBytes at hroom
        simp only [CpP.hdQ, CpP.hd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp only [sDom, sDomLen, sK, sY, sQ, sFn] <;> omega_arith)]
  exact hs q hq

theorem hdQ_lt (p : CpP) : ∀ q ∈ p.hdQ, q.1 < 32 := by
  intro q hq
  simp only [CpP.hdQ, CpP.hd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp [sDom, sDomLen, sK, sY, sQ, sFn]

/-- In the inner workspace for p, with what the outer one keeps. -/
def In (p : CpP) (mi : BitVec 64) (t : State) : Prop :=
  Fx p t ∧ SubCtx t p.B p.Z (inner p.w) p.w p.w mi ∧ XVals t p.B (inner p.w) p.w mi p.P ∧
    word t.mem p.B (8 * sWs) = off p.B (inner p.w) ∧ Slots t.mem p.B p.hdQ

theorem In.step {p : CpP} {mi : BitVec 64} {t u : State} (h : In p mi t) {rs : List (Nat × Nat)}
    (hf : Frm (off p.B (inner p.w)) rs t.mem u.mem) (hr : ∀ r ∈ rs, StepR p.w r) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) (h0 : u.gpr .rdi = t.gpr .rdi) : In p mi u := by
  obtain ⟨hx, hc, hv, hWs, hs⟩ := h
  have c := hx.ctx
  have hroom := room_k c.k1 c.hZ
  rw [show (p.k + 7) / 8 = p.w from rfl] at hroom
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have hGn := hc.good.scr.nowrap
  have hc' := hc.of_frm hf (fun r hr' => ⟨(hr r hr').1, (hr r hr').2.1⟩) hwr h0
  obtain ⟨hb, hi⟩ := child_frm hc (by unfold inner at hroom ⊢; omega_arith) hf (fun r hr' => by
    have := (hr r hr').2.1; omega_arith)
  exact ⟨hx.step hi hrd hwr, hc', hv.of_frmA hGn (by omega_arith) hf (fun r hr' => (hr r hr').2.2),
    by rw [hb _ (by decide)]; exact hWs, fun q hq => by rw [hb _ (hdQ_lt p q hq)]; exact hs q hq⟩

theorem In.keep {p : CpP} {mi : BitVec 64} {t u : State} (h : In p mi t) (hm : u.mem = t.mem) {rs : List Reg}
    (k : Keep rs t u) (h0 : .rdi ∉ rs) : In p mi u :=
  h.step (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (fun _ h => absurd h List.not_mem_nil) k.2.1 k.2.2
    (k.gpr h0)

theorem c1_in {p : CpP} {t : State} (h : C1 p t) : ∃ mi, In p mi t ∧ p.mv = true :=
  let ⟨mi, hx, hc, hv, hWs, hs, hm⟩ := h
  ⟨mi, ⟨hx, hc, hv, hWs, hs⟩, hm⟩

/-- y's load. -/
abbrev CpP.yl (p : CpP) : BPub := ⟨⟨p.B, p.Z, inner p.w, p.w, p.w⟩, p.yp, p.k⟩

theorem c1_lpre (p : CpP) (t : State) (h : C1 p t) : LPre aXm sY sK p.yl t := by
  obtain ⟨mi, ⟨hx, hc, -, -, hs⟩, -⟩ := c1_in h
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have := c.k2
  have := c.yl
  exact ⟨mi, p.yb, hc, show 2 ≤ p.w by omega_arith, Nat.le_refl _, show p.w < 2 ^ 30 by omega_arith, by decide, by decide,
    by decide, hs (sY, p.yp) (by simp), by rw [c.yl]; exact hs (sK, BitVec.ofNat 64 p.k) (by simp), c.yl, c.y,
    by omega_arith, by omega_arith, show (p.yb.length + 7) / 8 ≤ p.w by rw [c.yl]⟩

/-- With y in `aXm`. -/
def C2 (p : CpP) (t : State) : Prop :=
  ∃ mi, In p mi t ∧ p.mv = true ∧ wv t.mem (off p.B (inner p.w)) (slot p.w aXm) p.w = p.Y

theorem c1_c2 (p : CpP) (t : State) (h : C1 p t) : WP isa (seqs (Crt.loadArr aXm sY sK)) t (C2 p) := by
  obtain ⟨mi, hI, hm⟩ := c1_in h
  have hI' := hI
  obtain ⟨hx, hc, -, -, hs⟩ := hI'
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have := c.k2
  have := c.yl
  refine WP.mono (primeLoad_ok hc (show 2 ≤ p.w by omega_arith) (Nat.le_refl _) (show p.w < 2 ^ 30 by omega_arith)
    (show aXm < 8 by decide) (show sY < 32 by decide) (show sK < 32 by decide) (hs (sY, p.yp) (by simp))
    (by rw [c.yl]; exact hs (sK, BitVec.ofNat 64 p.k) (by simp)) c.y (by omega_arith) (by omega_arith)
    (show (p.yb.length + 7) / 8 ≤ p.w by rw [c.yl])) fun u ⟨_, hy, ho, k⟩ =>
    ⟨mi, hI.step (rs := [(slot p.w aXm, 8 * (p.w + 2))]) (Frm.of_outside ho (by simp)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact stepR_arr _ (by decide) (by decide) (by decide)) k.2.1 k.2.2
      (k.gpr (by decide)), hm, hy⟩

theorem c2_goodW1 (p : CpP) (t : State) (h : C2 p t) : GoodW1 p.ws t := by
  obtain ⟨mi, ⟨hx, hc, -⟩, -⟩ := h
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have := c.k2
  exact ⟨⟨mi, hc.good, Nat.le_refl _⟩, show 1 ≤ p.w by omega_arith, show p.w < 2 ^ 31 by omega_arith⟩

/-- Whether `1 < y < p − 1`, as the code compares. -/
abbrev CpP.rg (p : CpP) : Prop := 1 < p.Y ∧ 2 * (p.Y / 2) + 1 < p.P

/-- After the range check. -/
def C3 (p : CpP) (t : State) : Prop := ∃ mi, In p mi t ∧ p.mv = true ∧ t.zf = some (!decide p.rg)

theorem c2_c3 (p : CpP) (t : State) (h : C2 p t) : WP isa (seqs (rangeTest aXm)) t (C3 p) := by
  obtain ⟨mi, hI, hm, hy⟩ := h
  have hI' := hI
  obtain ⟨hx, hc, hv, -⟩ := hI'
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have := c.k2
  refine WP.mono (rangeTest_ok hc.good (Nat.le_refl _) (show 1 ≤ p.w by omega_arith) (show p.w < 2 ^ 31 by omega_arith)
    (show aXm < 8 by decide) (by decide) hv.one) fun u ⟨h9, hz, _, f, k⟩ => ⟨mi, hI.step f (fun r hr => ?_) k.2.1 k.2.2
      (k.gpr (by decide)), hm, by rw [hz, hy, hv.n]⟩
  have := slot_le (w := p.w) (show aTmp < 8 by decide)
  have := hdr_lt_slot p.w aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot p.w 8 (show sF < 32 by decide)
  have := hdr_lt_slot p.w aN (show sF < 32 by decide)
  have := hdr_lt_slot p.w aOne (show sF < 32 by decide)
  have s1 := slot_sep (w := p.w) (show aTmp ≠ aN by decide)
  have s2 := slot_sep (w := p.w) (show aTmp ≠ aOne by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [sF, sFn] at * <;> omega_arith

theorem c3_eval {p : CpP} {t : State} (h : C3 p t) : isa.eval .e t = some (!decide p.rg) := by
  obtain ⟨_, _, _, h9⟩ := h
  simp [eval, h9]

/-! ## Back to the outer workspace -/

/-- After `leave` and the test of the domain's length. -/
def C4 (p : CpP) (t : State) : Prop :=
  ∃ mi, Fx p t ∧ SubMem t p.B p.Z (inner p.w) p.w p.w mi ∧ XVals t p.B (inner p.w) p.w mi p.P ∧
    word t.mem p.B (8 * sWs) = off p.B (inner p.w) ∧ Slots t.mem p.B p.hdQ ∧ p.mv = true ∧ t.gpr .rdi = p.B ∧
    t.zf = some (decide (p.dl = 2 * p.k))

theorem c3_leave (p : CpP) (t : State) (h : C3 p t) : WP isa (.block [leave]) t fun u => u.gpr .rdi = p.B := by
  obtain ⟨mi, ⟨-, hc, -⟩, -⟩ := h
  exact WP.mono (leave_ok hc) fun u ⟨h0, _, _⟩ => h0

theorem c3_c4 (p : CpP) (t : State) (h : C3 p t) : WP isa (.block (leave :: qTest)) t (C4 p) := by
  obtain ⟨mi, ⟨hx, hc, hv, hWs, hs⟩, hm, -⟩ := h
  have c := hx.ctx
  refine WP.mono (leaveQ_ok hc (hs (sDomLen, BitVec.ofNat 64 p.dl) (by simp)) (hs (sK, BitVec.ofNat 64 p.k) (by simp))
    (by rcases c.dl with h | h <;> omega_arith)
    (by have := c.k2; rcases c.dl with h | h <;> omega_arith)) fun u ⟨h0, _, h3, hmu, k⟩ =>
    ⟨mi, hx.keep (by rw [hmu]; exact InScr.refl _ _ _) k, hc.toMem.congr hmu k.2.2,
      ⟨by rw [hmu]; exact hv.n, by rw [hmu]; exact hv.inv, by rw [hmu]; exact hv.one⟩, by rw [hmu]; exact hWs,
      by rw [hmu]; exact hs, hm, h0, h3⟩

theorem c4_eval {p : CpP} {t : State} (h : C4 p t) :
    isa.eval .e t = some (decide (p.dl = 2 * p.k)) := by
  obtain ⟨_, _, _, _, _, _, _, _, h3⟩ := h
  simp [eval, h3]

theorem c4_q {p : CpP} {t : State} (h : C4 p t) (he : isa.eval .e t = some false) : p.dl = 3 * p.k := by
  have c := h.choose_spec.1.ctx
  rw [c4_eval h] at he
  have := c.k2
  rcases c.dl with hd | hd
  · simp [hd] at he
  · exact hd

/-! ## q's first nonzero octet -/

/-- q's octets and their pointer. -/
abbrev CpP.qs (p : CpP) : ScanPub := ⟨p.B, p.Z, p.w, p.dp + BitVec.ofNat 64 (2 * p.k), p.qb⟩

theorem qb_length {p : CpP} {t : State} (c : FxCtx p t) (hq : p.dl = 3 * p.k) : p.qb.length = p.k := by
  simp only [CpP.qb, List.length_take, List.length_drop, c.doml, hq]; omega_arith

theorem c4_scan (p : CpP) (t : State) (h : C4 p t) (he : isa.eval .e t = some false) :
    ScanPre sQ p.qs t := by
  have hq := c4_q h he
  obtain ⟨mi, hx, hc, -, -, hs, -, h0, -⟩ := h
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have := c.k2
  have hroom := room_k c.k1 c.hZ
  rw [show (p.k + 7) / 8 = p.w from rfl] at hroom
  have hl := qb_length c hq
  show Outer t p.B p.Z p.w ∧ word t.mem p.B (8 * sQ) = p.dp + BitVec.ofNat 64 (2 * p.k) ∧
    word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.qb.length ∧ p.qb ≠ [] ∧ p.qb.length < 2 ^ 32 ∧
    Src t p.B p.Z (p.dp + BitVec.ofNat 64 (2 * p.k)) p.qb ∧ sQ < 32
  refine ⟨Outer.of_mem hc h0 hroom (by omega_arith) (by omega_arith), hs (sQ, p.dp + BitVec.ofNat 64 (2 * p.k)) (by simp),
    by rw [hl]; exact hs (sK, BitVec.ofNat 64 p.k) (by simp), fun he' => by rw [he'] at hl; simp at hl; omega_arith,
    by omega_arith, (c.dom.drop (2 * p.k)).take p.k, by decide⟩

/-- After the scan. -/
def C5 (p : CpP) (t : State) : Prop :=
  ∃ mi, Fx p t ∧ SubMem t p.B p.Z (inner p.w) p.w p.w mi ∧ XVals t p.B (inner p.w) p.w mi p.P ∧
    word t.mem p.B (8 * sWs) = off p.B (inner p.w) ∧ Slots t.mem p.B p.hdQ ∧ p.mv = true ∧ t.gpr .rdi = p.B ∧
    p.dl = 3 * p.k ∧ word t.mem p.B (8 * sEp) = off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead p.qb) ∧
    word t.mem p.B (8 * sEl) = BitVec.ofNat 64 (p.k - lead p.qb)

theorem c4_c5 (p : CpP) (t : State) (h : C4 p t) (he : isa.eval .e t = some false) :
    WP isa (seqs (scan sQ)) t (C5 p) := by
  have hq := c4_q h he
  have hS := c4_scan p t h he
  obtain ⟨mi, hx, hc, hv, hWs, hs, hm, h0, -⟩ := h
  have c := hx.ctx
  have hl := qb_length c hq
  have hS' : Outer t p.B p.Z p.w ∧ word t.mem p.B (8 * sQ) = p.dp + BitVec.ofNat 64 (2 * p.k) ∧
      word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.qb.length ∧ p.qb ≠ [] ∧ p.qb.length < 2 ^ 32 ∧
      Src t p.B p.Z (p.dp + BitVec.ofNat 64 (2 * p.k)) p.qb ∧ sQ < 32 := hS
  obtain ⟨hO, hp, hk, hne, hlt, hsrc, -⟩ := hS'
  refine WP.mono (scan_ok hO (show sQ < 32 by decide) hp hk hne hlt hsrc) fun u ⟨hEp, hEl, _, f, k⟩ => ?_
  have hr : ∀ r ∈ [(8 * sEp, 8), (8 * sEl, 8)], 8 * 16 ≤ r.1 ∧ r.1 + r.2 ≤ 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [sEp, sEl, sFn] <;> omega_arith
  have hroom := room_k c.k1 c.hZ
  have i : InScr p.B p.Z t.mem u.mem := InScr.of_frm f fun r hr' => by
    have := (hr r hr').2; unfold inner slot hdrBytes at hroom; omega_arith
  have hw : ∀ q ∈ p.hdQ ++ [(sWs, off p.B (inner p.w))], word u.mem p.B (8 * q.1) = word t.mem p.B (8 * q.1) := by
    intro q hq
    have hq32 : q.1 < 32 := by
      rcases List.mem_append.mp hq with hq | hq
      · exact hdQ_lt p q hq
      · rw [List.mem_singleton.mp hq]; show sWs < 32; decide
    refine f.word_eq (fun r hr' => ?_) (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    simp only [CpP.hdQ, CpP.hd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hr' with rfl | rfl <;>
      simp only [sDom, sDomLen, sK, sY, sQ, sWs, sEp, sEl, sFn] <;> omega_arith
  refine ⟨mi, hx.keep i k, hc.of_parent f hr k.2.2, hv.of_parent hc f (fun r hr' => (hr r hr').2),
    by rw [hw (sWs, off p.B (inner p.w)) (by simp)]; exact hWs, fun q hq => by rw [hw q (List.mem_append_left _ hq)]; exact hs q hq,
    hm, (k.gpr (by decide)).trans h0, hq, hEp, by rw [hEl, hl]⟩

/-! ## `R² mod p`, `y^q mod p` -/

/-- Back in the inner workspace. -/
def C6 (p : CpP) (t : State) : Prop :=
  ∃ mi, In p mi t ∧ p.mv = true ∧ p.dl = 3 * p.k ∧
    word t.mem p.B (8 * sEp) = off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead p.qb) ∧
    word t.mem p.B (8 * sEl) = BitVec.ofNat 64 (p.k - lead p.qb)

theorem c5_x0 {p : CpP} {t : State} (h : C5 p t) : t.gpr .rdi = p.B := h.choose_spec.2.2.2.2.2.2.1

theorem c5_c6 (p : CpP) (t : State) (h : C5 p t) : WP isa (.block [enter]) t (C6 p) := by
  obtain ⟨mi, hx, hc, hv, hWs, hs, hm, h0, hq, hEp, hEl⟩ := h
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have := c.k2
  have hroom := room_k c.k1 c.hZ
  rw [show (p.k + 7) / 8 = p.w from rfl] at hroom
  refine WP.mono (enter_ok (Outer.of_mem hc h0 hroom (by omega_arith) (by omega_arith)) hWs) fun u ⟨h0', hmu, k⟩ =>
    ⟨mi, ⟨hx.keep (by rw [hmu]; exact InScr.refl _ _ _) k, (hc.congr hmu k.2.2).ctx h0',
      ⟨by rw [hmu]; exact hv.n, by rw [hmu]; exact hv.inv, by rw [hmu]; exact hv.one⟩, by rw [hmu]; exact hWs,
      by rw [hmu]; exact hs⟩, hm, hq, by rw [hmu]; exact hEp, by rw [hmu]; exact hEl⟩

/-- `r2_ok`'s hypotheses, for the run's `-p⁻¹`. -/
theorem c6_r2 {p : CpP} {t : State} {mi : BitVec 64} (hI : In p mi t) (hm : p.mv = true)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 p.w) (h10 : t.gpr .r10 = off (off p.B (inner p.w)) (slot p.w aN)) :
    R2Pre ⟨⟨off p.B (inner p.w), slot p.w 8, p.w, mi⟩, p.P⟩ t := by
  obtain ⟨hx, hc, hv, -⟩ := hI
  have c := hx.ctx
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have := c.k2
  obtain ⟨hodd, -, hlo⟩ := valid_facts hm c.k1
  exact ⟨⟨hc.good, Nat.le_refl _⟩, show 2 ≤ p.w by omega_arith, show p.w < 2 ^ 30 by omega_arith, hv.n, hv.inv, h12, h10, hodd, hlo⟩

/-- After `R² mod p`. -/
def C7 (p : CpP) (t : State) : Prop :=
  ∃ mi, Fx p t ∧ ModCtx t p.B p.Z (inner p.w) p.w mi p.P ∧ Slots t.mem p.B p.hdQ ∧ p.dl = 3 * p.k ∧
    word t.mem p.B (8 * sEp) = off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead p.qb) ∧
    word t.mem p.B (8 * sEl) = BitVec.ofNat 64 (p.k - lead p.qb)

theorem c6_c7 (M : Mont) (R : R2Impl M) (p : CpP) (t : State) (h : C6 p t) : WP isa (.seq (.block r2Head) R.code) t (C7 p) := by
  obtain ⟨mi, ⟨hx, hc, hv, -, hs⟩, hm, hq, hEp, hEl⟩ := h
  have c := hx.ctx
  have hroom := room_k c.k1 c.hZ
  refine WP.mono (r2_ctx M R hc hv hm c.k1 c.k2 c.hZ) fun u ⟨hM, f, k⟩ => ?_
  obtain ⟨hb, hi⟩ := child_frm hc (by unfold inner at hroom ⊢; omega_arith) f (fun r hr => by
    have := r2Ranges_le p.w r hr; unfold tabBytes; omega_arith)
  exact ⟨mi, hx.keep hi k, hM, fun q hq => by rw [hb _ (hdQ_lt p q hq)]; exact hs q hq, hq,
    by rw [hb _ (by decide)]; exact hEp, by rw [hb _ (by decide)]; exact hEl⟩

/-- `pow`'s public data. -/
abbrev CpP.pw (p : CpP) : PowPub :=
  ⟨⟨p.B, p.Z, inner p.w, p.w, p.w⟩, p.yp, p.yb.length, off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead p.qb),
    (p.qb.drop (lead p.qb)).length⟩

theorem c7_ps0 (p : CpP) (t : State) (h : C7 p t) : PS0 sY sK sEp sEl p.pw t := by
  obtain ⟨mi, hx, hM, hs, hq, hEp, hEl⟩ := h
  have c := hx.ctx
  have hl := qb_length c hq
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have := c.k2
  have hne : p.qb ≠ [] := fun he => by rw [he] at hl; simp at hl; omega_arith
  have hlead := lead_lt hne
  have := c.yl
  have hsq : Src t p.B p.Z (off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead p.qb)) (p.qb.drop (lead p.qb)) :=
    ((c.dom.drop (2 * p.k)).take p.k).drop (lead p.qb)
  exact ps0_of hM (by decide) (by decide) (by decide) (by decide) (hs (sY, p.yp) (by simp))
    (by rw [c.yl]; exact hs (sK, BitVec.ofNat 64 p.k) (by simp)) c.y (by omega_arith) (by rw [c.yl]) hEp
    (by rw [hEl, List.length_drop, hl]) hsq (by rw [List.length_drop]; omega_arith) (by rw [List.length_drop]; omega_arith)

/-- After `pow`: the inner workspace. -/
def C8 (p : CpP) (t : State) : Prop := GoodW1 p.ws t

theorem c7_c8 (M : Mont) (E : CrtExpL M) (p : CpP) (t : State) (h : C7 p t) :
    WP isa (seqs (pow M.mm E.code sY sK sEp sEl)) t (C8 p) := by
  have h0 := c7_ps0 p t h
  obtain ⟨mi, hx, hM, hs, hq, hEp, hEl⟩ := h
  have c := hx.ctx
  have hl := qb_length c hq
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_arith
  have := c.k1
  have := c.k2
  have hne : p.qb ≠ [] := fun he => by rw [he] at hl; simp at hl; omega_arith
  have hlead := lead_lt hne
  have := c.yl
  have hsq : Src t p.B p.Z (off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead p.qb)) (p.qb.drop (lead p.qb)) :=
    ((c.dom.drop (2 * p.k)).take p.k).drop (lead p.qb)
  exact WP.mono (pow_ok M E hM (by decide) (by decide) (by decide) (by decide) (hs (sY, p.yp) (by simp))
    (by rw [c.yl]; exact hs (sK, BitVec.ofNat 64 p.k) (by simp)) c.y (by omega_arith) (by rw [c.yl]) hEp
    (by rw [hEl, List.length_drop, hl]) hsq (by rw [List.length_drop]; omega_arith) (by rw [List.length_drop]; omega_arith))
    fun u ⟨hM', _⟩ => ⟨⟨mi, hM'.sub.good, Nat.le_refl _⟩, show 1 ≤ p.w by omega_arith, show p.w < 2 ^ 31 by omega_arith⟩

end VG.Proof.Ffdh.X86_64.CheckPublic

end

end

/-! # FFDH public-key validation on x86-64: precomputation in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh VG.Proof.MlKem.X86_64

private def C6H (p : CpP) (s : State) : Prop :=
  C6 p s ∧ s.gpr .r12 = BitVec.ofNat 64 p.w ∧ s.gpr .r10 = off (off p.B (inner p.w)) (slot p.w aN)

private theorem c6_head (p : CpP) (s : State) (h : C6 p s) : WP isa (.block r2Head) s (C6H p) := by
  obtain ⟨mi, hI, hm, hq, hEp, hEl⟩ := h
  refine WP.mono (r2Head_ok hI.2.1.good (Nat.le_refl _)) fun t ⟨h12, h10, hmem, k⟩ => ?_
  exact ⟨⟨mi, hI.keep hmem k (by decide), hm, hq, by rw [hmem]; exact hEp, by rw [hmem]; exact hEl⟩, h12, h10⟩

/-- The two runs have the same modulus and hence the same negative inverse. -/
private theorem c6h_two_r2 {s₁ s₂ : State} (h : Two C6H s₁ s₂) : Two R2Pre s₁ s₂ := by
  refine two_bind (fun p t₁ t₂ h₁ h₂ => ?_) h
  obtain ⟨⟨mi₁, hI₁, hm, _⟩, h12₁, h10₁⟩ := h₁
  obtain ⟨⟨mi₂, hI₂, _, _⟩, h12₂, h10₂⟩ := h₂
  have c := hI₁.1.ctx
  obtain ⟨hodd, _⟩ := valid_facts hm c.k1
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CpP.w; omega_using []
  have hk := c.k1
  obtain rfl := xvals_minv (show 1 ≤ p.w by omega_using [ew, hk]) hodd hI₁.2.2.1 hI₂.2.2.1
  exact ⟨_, c6_r2 hI₁ hm h12₁ h10₁, c6_r2 hI₂ hm h12₂ h10₂⟩

theorem c6_r2_ct (M : Mont) (R : R2Impl M) :
    RelCT isa (Two C6) (.seq (.block r2Head) R.code) fun _ _ => True := by
  refine RelCT.seq (R := Two C6H)
    (two_piece [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
      fun p s ⟨_, hI, _⟩ => hI.2.1.rdi) (by taint_decide) c6_head)
    (R.ct.mono (fun _ _ h => c6h_two_r2 h) fun _ _ h => h)

end VG.Proof.Ffdh.X86_64.CheckPublic

end

end

/-! # FFDH public-key validation on x86-64: constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh VG.Proof.MlKem.X86_64

private theorem pins_nil {α : Type} (Φ : α → State → Prop) : Pins Φ [] :=
  fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

private theorem rangeXm_ct : RelCT isa (Two GoodW1) (seqs (rangeTest aXm)) fun _ _ => True := by
  unfold rangeTest
  refine RelCT.seqs_append (by simp [range, gt1, ltArr, cmpArr]) (by simp)
    (RelCT.seq (R := Two fun (_ : Unit) (_ : State) => True)
      ((range_ct (a := aXm) (by decide) (by decide) (by taint_decide) (by taint_decide)
        (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => ⟨(), trivial, trivial⟩)) ?_)
  exact two_taint [] (pins_nil _) (by taint_decide)

private theorem main_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckPublic.main M.mm E.code (.seq (.block r2Head) R.code) =
      seqs ((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++
        (Crt.loadArr aXm sY sK ++ (rangeTest aXm ++
          ([.ite .e (retInner 0) (.seq (.block (leave :: qTest))
            (.ite .e (VG.Impl.Ffdh.X86_64.Domain.ret 1)
              (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup M.mm E.code (.seq (.block r2Head) R.code)))))] : List (Prog isa))))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckPublic.main, List.append_assoc]

private theorem subgroup_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup M.mm E.code (.seq (.block r2Head) R.code) =
      scan sQ ++ (.block [enter] :: (.seq (.block r2Head) R.code ::
        (pow M.mm E.code sY sK sEp sEl ++ (isOne aY ++ ([.block [leave]] : List (Prog isa)))))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup, List.append_assoc, List.cons_append, List.nil_append]

theorem subgroup_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    RelCT isa (Two fun p s => C4 p s ∧ isa.eval .e s = some false)
      (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.subgroup M.mm E.code (.seq (.block r2Head) R.code)))
      fun _ _ => True := by
  rw [subgroup_eq]
  refine RelCT.seqs_append (by simp [scan]) (by simp) (RelCT.seq (R := Two C5)
    (two_post (two_map CpP.qs (fun p s h => c4_scan p s h.1 h.2)
      (scan_ct (by taint_decide) (by taint_decide))) (fun p s h => c4_c5 p s h.1 h.2)) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two C6)
    (two_piece [.rdi] (pins_rdiB CpP.B fun _ _ h => c5_x0 h) (by taint_decide) c5_c6) ?_)
  refine seqs_cons_ct (by simp [pow]) (RelCT.seq (R := Two C7)
    (two_post (c6_r2_ct M R) (c6_c7 M R)) ?_)
  refine RelCT.seqs_append (by simp [pow]) (by simp [isOne, eqArr]) (RelCT.seq (R := Two C8)
    (two_post (two_map CpP.pw c7_ps0
      (pow_ct M E (loadArr_ct (by decide) (by taint_decide) (by taint_decide)) hE
        (by taint_decide) (by taint_decide) (by taint_decide))) (c7_c8 M E)) ?_)
  refine RelCT.seqs_append (by simp [isOne, eqArr]) (by simp) (RelCT.seq (R := Two C8)
    (two_post (two_map CpP.ws (fun _ _ h => h.1) (eqArr_ct (by decide) (by decide) (by taint_decide)))
      fun p s h => ?_) ?_)
  · obtain ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ := h
    exact WP.mono (eqArr_ok hg hZ hw hw' (show aY < 8 by decide) (show aOne < 8 by decide))
      fun t ⟨_, hm, k⟩ => GoodW1.keep ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ hm (k.gpr (by decide)) k.2.2
  exact two_map CpP.ws (fun _ _ h => h) (two_taint [.rdi] pins_goodW1 (by taint_decide))

theorem main_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    RelCT isa (Two fun p s => CE p s ∧ isa.eval .ne s = some false)
      (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.main M.mm E.code (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp [pSetup]) (by simp [Crt.loadArr]) (RelCT.seq (R := Two C1)
    (two_post (two_map CpP.d (fun p s h => ce_setupP p s h.1 h.2) setup_ct)
      fun p s h => ce_c1 p s h.1 h.2) ?_)
  refine RelCT.seqs_append (by simp [Crt.loadArr]) (by simp) (RelCT.seq (R := Two C2)
    (two_post (two_map CpP.yl c1_lpre (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) c1_c2) ?_)
  refine RelCT.seqs_append (by simp [rangeTest, range, gt1, ltArr, cmpArr]) (by simp) (RelCT.seq (R := Two C3)
    (two_post (two_map CpP.ws c2_goodW1 rangeXm_ct) c2_c3) ?_)
  simp only [seqs]
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [c3_eval h₁, c3_eval h₂])
    (two_taint [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
      fun _ _ ⟨⟨_, ⟨_, hc, _⟩, _⟩, _⟩ => hc.rdi) (by taint_decide)) ?_
  refine RelCT.seq (R := Two C4) (RelCT.block_append (RelCT.seq
    (two_piece (Ψ := fun (p : CpP) t => t.gpr .rdi = p.B ∧ WP isa (.block qTest) t (C4 p)) [.rdi]
      (pins_rdiB (fun p => off p.B (inner p.w)) fun _ _ ⟨⟨_, ⟨_, hc, _⟩, _⟩, _⟩ => hc.rdi)
      (by taint_decide) fun p s h => WP.and (c3_leave p s h.1) (WP.block_append_iff.mp (c3_c4 p s h.1)))
    (two_piece [.rdi] (pins_rdiB CpP.B fun _ _ h => h.1) (by taint_decide) fun _ _ h => h.2))) ?_
  exact two_ite (fun p s₁ s₂ h₁ h₂ => by rw [c4_eval h₁, c4_eval h₂])
    (two_taint [] (pins_nil _) (by taint_decide)) (subgroup_ct M E R hE)

theorem cp_body_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    RelCT isa (Two CR) (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.body M.mm E.code (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPublic.body
  refine RelCT.seq (R := Two CE) (RelCT.block_append (RelCT.seq
    (two_piece (Ψ := E1) [.rdi, .rsi, .rdx, .rcx, .r9] (pins_of entryRegs cr_regs) (by taint_decide) cr_e1)
    (two_post (two_map CpP.d e1_dhp domHead_ct) e1_ce))) ?_
  exact two_ite (fun p s₁ s₂ h₁ h₂ => by rw [ce_eval h₁, ce_eval h₂])
    (two_taint [] (pins_nil _) (by taint_decide)) (main_ct M E R hE)

theorem cp_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    RelCT isa (Two CR) (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code M.mm E.code (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code
  refine RelCT.seq (R := Two fun (p : CpP) s => s.gpr .rdi = p.B)
    (two_post (cp_body_ct M E R hE) fun p s h =>
      WP.mono (cp_body_ok M E R (cpCtx_of h.1)) fun _ ⟨_, hdi, _⟩ => hdi.trans h.2.2.1)
    (two_taint [.rdi] (pins_rdiB CpP.B fun _ _ h => h) (by taint_decide))

def cpOf (s : State) : CpP :=
  ⟨s.gpr .r9, (scrLen s).toNat * 8, (s.gpr .rdx).toNat, (s.gpr .rsi).toNat, s.gpr .rdi, s.gpr .rcx, cpDom s,
    Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat, s.gpr .rsp⟩

theorem cp_constantTime (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    ConstantTime isa cpContract.pre cpContract.pub
      (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code M.mm E.code (.seq (.block r2Head) R.code)) := by
  refine RelCT.constantTime ((cp_ct M E R hE).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨cpOf s₁, ?_, ?_⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6⟩ := hp
    unfold cpLeak at hl
    obtain ⟨hd, hy⟩ := List.append_inj hl (by simp [cpDom, Spec.Rsa.bytesAt, r1])
    refine ⟨h₂, hsp.symm, r5.symm, by rw [← r6]; rfl, by rw [← r2]; rfl, by rw [← r1]; rfl,
      r0.symm, r3.symm, ?_, ?_⟩
    · exact ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hd).symm
    · exact ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hy).symm

end VG.Proof.Ffdh.X86_64.CheckPublic

end

end

/-! # FFDH public-key validation on x86-64: verified -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/CheckPublic/Correct.lean`, which only this module imported.
section

/-! # FFDH public-key validation on x86-64: full correctness and ABI -/

section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem cp_correct (M : Mont) (E : CrtExpL M) (R : R2Impl M)
    (hmx : ctlOk (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code M.mm E.code (.seq (.block r2Head) R.code)) = true) (s : State) (h : cpContract.pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code M.mm E.code (.seq (.block r2Head) R.code)) s tr t ∧
      abiPreserved s t ∧ cpContract.post s t := by
  have c := cpCtx_of h
  obtain ⟨_, _, _, _, _, _, _, _, hRetScr, _⟩ := h
  suffices hw : WP isa (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code M.mm E.code (.seq (.block r2Head) R.code)) s
      fun t => gprPreserved s t ∧ cpContract.post s t by
    obtain ⟨tr, t, he, hg, hp⟩ := hw
    exact ⟨tr, t, he, abiPreserved_of_ctl hmx he hg, hp⟩
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code
  refine WP.seq (WP.mono (cp_body_ok M E R c) fun u ⟨hp, hdi, hf, hsaved, k₁⟩ => ?_)
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (exit_ok (c.hs.congr k₁.2.2) hdi (by omega) hsaved)
    fun t ⟨hRestore, hm, k₂⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact (k₂.gpr (by decide)).trans (k₁.gpr (by decide))
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
  · rw [hm]
    apply Mem.readW_congr
    intro i hi
    exact hf _ (out_scr hRetScr (contains_byte (s.gpr .rsp) hi (by decide)))
  · change cpPost s t
    unfold cpPost
    rw [k₂.gpr (show .rax ∉ saved by decide)]
    exact hp

end VG.Proof.Ffdh.X86_64.CheckPublic
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Domain

theorem cp_verified (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl)
    (hmx : ctlOk (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code M.mm E.code (.seq (.block r2Head) R.code)) = true) :
    Verified target (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.code M.mm E.code (.seq (.block r2Head) R.code))
      (Spec.Ffdh.checkPublicContract abi) := by
  exact Verified.of_correct (cp_correct M E R hmx) (cp_constantTime M E R hE) cp_implies

end VG.Proof.Ffdh.X86_64.CheckPublic
