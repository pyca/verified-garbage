module

public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPublic.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Front
import VerifiedGarbage.Proof.Ffdh.AArch64.Scan
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math

/-!
# `vg_ffdh_check_public` on AArch64: correctness

From `cpContract`'s precondition, `CheckPublic.code` returns whether y is a
valid public value, for a valid domain (`cp_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckPublic

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Spec.Ffdh

/-- What the code uses of the precondition. -/
structure CpCtx (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .x2).toNat
  k2 : (s.gpr .x2).toNat ≤ 1024
  dl : (s.gpr .x1).toNat = 2 * (s.gpr .x2).toNat ∨ (s.gpr .x1).toNat = 3 * (s.gpr .x2).toNat
  yl : (s.gpr .x4).toNat = (s.gpr .x2).toNat
  hZ : 128 * (s.gpr .x2).toNat + 256 ≤ (s.gpr .x6).toNat * 8
  hs : Scr s (s.gpr .x5) ((s.gpr .x6).toNat * 8)
  dom : Src s (s.gpr .x5) ((s.gpr .x6).toNat * 8) (s.gpr .x0) (cpDom s)
  y : Src s (s.gpr .x5) ((s.gpr .x6).toNat * 8) (s.gpr .x3)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)

theorem cpCtx_of {s : State} (h : cpPre s) : CpCtx s := by
  obtain ⟨hrd, hwr, dds, dys, wD, wY, wS, ⟨hk1, hk2⟩, hdl, hyl, hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  exact ⟨hk1, hk2, hdl, hyl, by omega_arith, Scr.of_mem (by rw [hwr]; simp) wS,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dds, src_of_region (by rw [hrd]; simp) (by omega_arith) dys⟩

/-- The entry: the arguments into the header at `scratch`. -/
theorem cpEntry_ok {s : State} {B : Addr} (hB : s.gpr .x5 = B) (hw : ∀ i < 22, InRegions s.wr (off B (8 * i)) 8) :
    WP isa (.block CheckPublic.entry) s fun t => t.gpr .x0 = B ∧
      word t.mem B (8 * sDom) = s.gpr .x0 ∧ word t.mem B (8 * sDomLen) = s.gpr .x1 ∧
      word t.mem B (8 * sK) = s.gpr .x2 ∧ word t.mem B (8 * sY) = s.gpr .x3 ∧
      Outside B (8 * 16) (8 * 4) s.mem t.mem ∧ Keep [.x0] s t := by
  have eD : sDom = 16 := rfl
  have eL : sDomLen = 17 := rfl
  have eK : sK = 18 := rfl
  have eY : sY = 19 := rfl
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧
      t.mem = (((s.mem.writeW (off B (8 * sDom)) (s.gpr .x0)).writeW (off B (8 * sDomLen)) (s.gpr .x1)).writeW
        (off B (8 * sK)) (s.gpr .x2)).writeW (off B (8 * sY)) (s.gpr .x3)) (by
    unfold CheckPublic.entry
    brun [Crt.stw, hB, hdr_enc (show sDom < 32 by decide), hdr_enc (show sDomLen < 32 by decide),
      hdr_enc (show sK < 32 by decide), hdr_enc (show sY < 32 by decide), hw sDom (by decide), hw sDomLen (by decide),
      hw sK (by decide), hw sY (by decide)]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h0, hm⟩, k⟩ => ?_
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_, k⟩ <;> rw [hm]
  · rw [(writeW_outside _ B _ (by omega_arith)).word (by omega_arith) (by omega_arith),
      (writeW_outside _ B _ (by omega_arith)).word (by omega_arith) (by omega_arith),
      (writeW_outside _ B _ (by omega_arith)).word (by omega_arith) (by omega_arith), word_writeW_self]
  · rw [(writeW_outside _ B _ (by omega_arith)).word (by omega_arith) (by omega_arith),
      (writeW_outside _ B _ (by omega_arith)).word (by omega_arith) (by omega_arith), word_writeW_self]
  · rw [(writeW_outside _ B _ (by omega_arith)).word (by omega_arith) (by omega_arith), word_writeW_self]
  · rw [word_writeW_self]
  · intro x hx
    rw [writeW_outside _ B _ (by omega_arith) x (by omega_arith), writeW_outside _ B _ (by omega_arith) x (by omega_arith),
      writeW_outside _ B _ (by omega_arith) x (by omega_arith), writeW_outside _ B _ (by omega_arith) x (by omega_arith)]

/-- With q: its first nonzero octet, `R² mod p`, `y^q mod p` and whether it is 1. -/
theorem cpQ_ok (W : Window) (M : Mont) (S : Selector) {u : State} {B : Addr} {Z k : Nat} {mi : BitVec 64}
    {m₀ : Mem} {dp yp : Addr}
    (hc : SubMem u B Z (inner ((k + 7) / 8)) ((k + 7) / 8) ((k + 7) / 8) mi)
    (hv : XVals u B (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ dp k)))
    (hval : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ dp k)) k = true) (hk1 : 64 ≤ k)
    (hk2 : k ≤ 1024) (hZ : 128 * k + 256 ≤ Z) (h0 : u.gpr .x0 = B)
    (hWs : word u.mem B (8 * sWs) = off B (inner ((k + 7) / 8))) (hK : word u.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hQ : word u.mem B (8 * sQ) = dp + BitVec.ofNat 64 (2 * k)) (hY : word u.mem B (8 * sY) = yp)
    (hdom : Src u B Z dp (Spec.Rsa.bytesAt m₀ dp (3 * k)))
    (hy : Src u B Z yp (Spec.Rsa.bytesAt m₀ yp k)) :
    WP isa (seqs (VG.Impl.Ffdh.AArch64.Domain.CheckPublic.subgroup W.code S.code M.mm)) u fun t =>
      t.gpr .x0 = bit (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ yp k) ^
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k) %
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ dp k) = 1) ∧ Keep (.x0 :: mmRegs) u t := by
  have hroom := room_k hk1 hZ
  have hO : Outer u B Z ((k + 7) / 8) := Outer.of_mem hc h0 hroom (by omega_arith) (by omega_arith)
  have hq := src_slice (off := 2 * k) (len := k) hdom (by omega_arith)
  have hql : (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k).length = k := bytesAt_length _ _ _
  have hne : Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k ≠ [] := by
    intro h; rw [h] at hql; simp at hql; omega_arith
  unfold VG.Impl.Ffdh.AArch64.Domain.CheckPublic.subgroup
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- The first nonzero octet of q.
  refine wp_seqs_append (by simp [scan]) (by simp) (WP.mono (scan_ok hO (show sQ < 32 by decide) hQ
    (by rw [hql]; exact hK) hne (by omega_arith) hq) fun u₁ ⟨hEp, hEl, _, f₁, k₁⟩ => ?_)
  have hr₁ := scanR_le
  have hc₁ := hc.of_parent f₁ hr₁ k₁.wr
  have hv₁ := hv.of_parent hc f₁ (fun r hr => (hr₁ r hr).2)
  have hO₁ : Outer u₁ B Z ((k + 7) / 8) := Outer.of_mem hc₁ ((k₁.gpr .x0 (by decide)).trans h0) hroom (by omega_arith)
    (by omega_arith)
  have hs₁ : ∀ i < 32, i ≠ sEp → i ≠ sEl → word u₁.mem B (8 * i) = word u.mem B (8 * i) := fun i hi h1 h2 =>
    f₁.word_eq (scanR_word h1 h2) (by omega_using [hi])
  have i₁ : InScr B Z u.mem u₁.mem := InScr.of_frm f₁ fun r hr => by
    have h1 := (hr₁ r hr).2; omega_using [h1, hZ]
  -- Into the inner workspace, and `R² mod p`.
  have hWs₁ : word u₁.mem B (8 * sWs) = off B (inner ((k + 7) / 8)) := by
    rw [hs₁ _ (by decide) (by decide) (by decide)]; exact hWs
  refine wp_seqs_cons (by simp [r2Steps]) (WP.mono (enter_ok hO₁ hWs₁) fun u₂ ⟨⟨h0₂, hm₂⟩, k₂⟩ => ?_)
  have hc₂ : SubCtx u₂ B Z (inner ((k + 7) / 8)) ((k + 7) / 8) ((k + 7) / 8) mi :=
    ⟨hc₁.scr.congr k₂.wr, h0₂, by rw [hm₂]; exact hc₁.hdr, by rw [hm₂]; exact hc₁.link, by rw [hm₂]; exact hc₁.nw,
      by rw [hm₂]; exact hc₁.narr, hc₁.lo, hc₁.hi⟩
  have hv₂ : XVals u₂ B (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ dp k)) :=
    ⟨by rw [hm₂]; exact hv₁.n, by rw [hm₂]; exact hv₁.inv, by rw [hm₂]; exact hv₁.one⟩
  refine wp_seqs_append (by simp [r2Steps]) (by simp [pow, Crt.loadArr]) (WP.mono (r2_ctx M hc₂ hv₂ hval hk1 hk2 hZ)
    fun u₃ ⟨hm₃, f₃, k₃⟩ => ?_)
  -- The power and its comparison with 1.
  have hlead := lead_lt hne
  rw [hql] at hlead
  obtain ⟨hb₃, hi₃⟩ := child_frm hc₂ (by have := hroom; unfold inner at this ⊢; omega_arith) f₃ (fun r hr => by
    have := r2Ranges_le ((k + 7) / 8) r hr; unfold CrtWindowFive.tabBytes32; omega_arith)
  have hw₃ : ∀ i < 32, i ≠ sEp → i ≠ sEl → word u₃.mem B (8 * i) = word u.mem B (8 * i) := fun i hi h1 h2 => by
    rw [hb₃ i hi, hm₂, hs₁ i hi h1 h2]
  have hs₃ : InScr B Z u.mem u₃.mem := (i₁.trans (by rw [hm₂]; exact InScr.refl _ _ _)).trans hi₃
  have K₃ : Keep (.x0 :: mmRegs) u u₃ :=
    keep_trans (keep_trans (k₁.mono (by decide)) (k₂.mono (by decide))) (k₃.mono (by decide))
  have heS := src_slice (off := lead (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k))
    (len := k - lead (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k)) hq (by omega_arith)
  rw [← List.append_assoc]
  refine wp_seqs_append (by simp [pow, Crt.loadArr]) (by simp) (WP.mono (powOne_ok W M S hm₃ (bp := sY) (bl := sK)
    (ep := sEp) (el := sEl) (by decide) (by decide) (by decide) (by decide)
    (by rw [hw₃ _ (by decide) (by decide) (by decide)]; exact hY)
    (by rw [hw₃ _ (by decide) (by decide) (by decide), bytesAt_length]; exact hK)
    (hy.congrK hs₃ K₃) (by rw [bytesAt_length]; omega_arith) (by rw [bytesAt_length])
    (by rw [hb₃ _ (by decide), hm₂]; exact hEp)
    (by rw [hb₃ _ (by decide), hm₂, bytesAt_length, hEl, hql])
    (heS.congrK hs₃ K₃) (by rw [bytesAt_length]; omega_arith) (by rw [bytesAt_length]; omega_arith))
    fun u₄ ⟨_, h9₄, _, k₄⟩ => ?_)
  refine WP.mono (WP.keep [.x0] (c := .block [mov .x0 .x9]) (Q := fun t => t.gpr .x0 = u₄.gpr .x9) (by brun)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨h0', k₅⟩ => ⟨?_, ?_⟩
  · rw [h0', h9₄]
    have e : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k) +
        BitVec.ofNat 64 (lead (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k)))
        (k - lead (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k))) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k) := by
      rw [← VG.Proof.Dsa.bytesAt_slice m₀ _ (show lead _ + (k - lead _) ≤ k by omega_arith)]
      generalize Spec.Rsa.bytesAt m₀ (dp + BitVec.ofNat 64 (2 * k)) k = L at hql ⊢
      rw [List.take_of_length_le (by simp; omega_arith), os2ip_drop_lead]
    rw [e]
  · exact keep_trans (keep_trans K₃ (k₄.mono (by decide))) (k₅.mono (by decide))

/-- `publicValid`, on the integers. -/
theorem publicValid_iff (a : Parameters) (y : Nat) :
    publicValid ⟨a, y⟩ = true ↔ (1 < y ∧ y < a.p - 1) ∧ ∀ q, a.q = some q → y ^ q % a.p = 1 := by
  unfold publicValid
  cases hq : a.q with
  | none => simp
  | some q => simp [powMod_eq]

/-- After `domHead`, for a valid modulus p: `main`. -/
theorem cpMain_ok (W : Window) (M : Mont) (S : Selector) {s t : State} (c : CpCtx s)
    (h0 : t.gpr .x0 = s.gpr .x5) (hs : Scr t (s.gpr .x5) ((s.gpr .x6).toNat * 8))
    (hD : word t.mem (s.gpr .x5) (8 * sDom) = s.gpr .x0)
    (hL : word t.mem (s.gpr .x5) (8 * sDomLen) = s.gpr .x1)
    (hK : word t.mem (s.gpr .x5) (8 * sK) = BitVec.ofNat 64 (s.gpr .x2).toNat)
    (hY : word t.mem (s.gpr .x5) (8 * sY) = s.gpr .x3)
    (hQ : word t.mem (s.gpr .x5) (8 * sQ) = s.gpr .x0 + BitVec.ofNat 64 (2 * (s.gpr .x2).toNat))
    (i₀ : InScr (s.gpr .x5) ((s.gpr .x6).toNat * 8) s.mem t.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hval : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x2).toNat))
      (s.gpr .x2).toNat = true) :
    WP isa (VG.Impl.Ffdh.AArch64.Domain.CheckPublic.main W.code S.code M.mm) t fun t' =>
      (t'.gpr .x0 = if publicValid ⟨domainOf (s.gpr .x2).toNat (cpDom s),
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)⟩ then 1 else 0) ∧
      Keep (.x0 :: mmRegs) t t' := by
  obtain ⟨hk1, hk2, hdl, hyl, hZ, -, hdom, hy⟩ := c
  have hn := hs.nowrap
  simp only [cpDom] at *
  generalize s.gpr .x5 = B at *
  generalize (s.gpr .x6).toNat * 8 = Z at *
  generalize hkk : (s.gpr .x2).toNat = k at *
  rw [hyl] at hy ⊢
  have hroom := room_k hk1 hZ
  obtain ⟨hodd, hp1, hlo⟩ := valid_facts hval hk1
  have hsrcD := hdom.congr i₀ hrd hwr
  have hpS : Src t B Z (s.gpr .x0) (Spec.Rsa.bytesAt s.mem (s.gpr .x0) k) := by
    have := src_slice (off := 0) (len := k) hsrcD (by rcases hdl with h | h <;> rw [h] <;> omega_arith)
    simpa using this
  have hyS : Src t B Z (s.gpr .x3) (Spec.Rsa.bytesAt s.mem (s.gpr .x3) k) := hy.congr i₀ hrd hwr
  unfold VG.Impl.Ffdh.AArch64.Domain.CheckPublic.main
  rw [show [.block head] ++ pSetup ++ Crt.loadArr aXm sY sK ++ range aXm ++
      [Code.ite (.zero .x .x9) (VG.Impl.Ffdh.AArch64.Domain.ret 0)
        (.seq (.block (leave :: qTest)) (.ite (.zero .x .x3) (VG.Impl.Ffdh.AArch64.Domain.ret 1)
          (seqs (VG.Impl.Ffdh.AArch64.Domain.CheckPublic.subgroup W.code S.code M.mm))))] =
    ([.block head] ++ pSetup) ++ (Crt.loadArr aXm sY sK ++ (range aXm ++
      [Code.ite (.zero .x .x9) (VG.Impl.Ffdh.AArch64.Domain.ret 0)
        (.seq (.block (leave :: qTest)) (.ite (.zero .x .x3) (VG.Impl.Ffdh.AArch64.Domain.ret 1)
          (seqs (VG.Impl.Ffdh.AArch64.Domain.CheckPublic.subgroup W.code S.code M.mm))))])) by
    simp only [List.append_assoc]]
  -- The workspaces.
  refine wp_seqs_append (by simp) (by simp [Crt.loadArr]) (WP.mono (setup_ok hs h0 hk1 hk2 hZ hD hK hpS
    (bytesAt_length _ _ _) hodd) fun u₁ ⟨mi, hc₁, hv₁, hWs₁, f₁, k₁⟩ => ?_)
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hi8 : 8 * 32 ≤ inner ((k + 7) / 8) := by simp only [inner, slot, hdrBytes]; omega_arith
  have hiZ : inner ((k + 7) / 8) + slot ((k + 7) / 8) 8 ≤ Z := by unfold CrtWindowFive.tabBytes32 at hroom; omega_arith
  have hp₁ : ∀ i < 32, i ≠ sW → i ≠ sWs → (i < sArr 0 ∨ sArr 0 + 8 ≤ i) →
      word u₁.mem B (8 * i) = word t.mem B (8 * i) := fun i hi h1 h2 h3 =>
    f₁.word_eq (setupR_word _ hi h1 h2 h3) (by omega_using [hi])
  have i₁ : InScr B Z t.mem u₁.mem := InScr.of_frm f₁ (setupR_le _ hiZ)
  have hY₁ : word u₁.mem B (8 * sY) = s.gpr .x3 := by
    rw [hp₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hY
  have hK₁ : word u₁.mem B (8 * sK) = BitVec.ofNat 64 k := by
    rw [hp₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hK
  -- y into `aXm`.
  refine wp_seqs_append (by simp [Crt.loadArr]) (by simp [range, gt1, ltArr, cmpArr])
    (WP.mono (primeLoad_ok hc₁ (by omega_arith) (Nat.le_refl _) (by omega_arith) (show aXm < 8 by decide) (show sY < 32 by decide)
      (show sK < 32 by decide) hY₁ (by rw [bytesAt_length]; exact hK₁) (hyS.congrK i₁ k₁) (by rw [bytesAt_length]; omega_arith)
      (by rw [bytesAt_length]; omega_arith) (by rw [bytesAt_length])) fun u₂ ⟨hc₂, hy₂, ho₂, k₂⟩ => ?_)
  have f₂ : Frm (off B (inner ((k + 7) / 8))) [(slot ((k + 7) / 8) aXm, 8 * ((k + 7) / 8 + 2))] u₁.mem u₂.mem :=
    Frm.of_outside ho₂ (by simp)
  have hv₂ := hv₁.of_frmA hc₁.good.scr.nowrap (by omega_arith) f₂ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact arr_off _ (by decide) (by decide))
  -- `1 < y < p − 1`.
  refine wp_seqs_append (by simp [range, gt1, ltArr, cmpArr]) (by simp) (WP.mono (range_ok hc₂.good (Nat.le_refl _)
    (by omega_arith) (by omega_arith) (show aXm < 8 by decide) (by decide) hv₂.one) fun u₃ ⟨h9₃, _, f₃, k₃⟩ => ?_)
  rw [hy₂, hv₂.n] at h9₃
  have hpk : (domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)).p =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0) k) := domainOf_p _ _ (by rcases hdl with h | h <;> omega_arith)
  have hrange : (1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x3) k) ∧
      2 * (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x3) k) / 2) + 1 <
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0) k)) ↔
      (1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x3) k) ∧ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x3) k) <
        (domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)).p - 1) := by
    rw [hpk, lt_pm1 hodd]
  have K₃ : Keep (.x0 :: mmRegs) t u₃ := keep_trans (keep_trans k₁ (k₂.mono (by decide))) (k₃.mono (by decide))
  simp only [seqs]
  refine wp_ite_bit h9₃ (fun hP => ?_) (fun hP => ?_)
  · refine WP.mono (ret_ok u₃ (by decide)) fun t' ⟨⟨h0', _⟩, k'⟩ => ⟨?_, keep_trans K₃ (k'.mono (by decide))⟩
    rw [h0', ite_eq_right (by rw [publicValid_iff]; exact fun h => hP (hrange.mpr h.1))]; rfl
  have hR := hrange.mp hP
  -- Back to the outer workspace, and whether there is q.
  have r₃ : ∀ r ∈ [(slot ((k + 7) / 8) aTmp, 8 * ((k + 7) / 8)), (8 * sF, 8)], 8 * 17 ≤ r.1 ∧
      r.1 + r.2 ≤ slot ((k + 7) / 8) 8 := fun r hr => ⟨(range_frame _ r hr).1, (range_frame _ r hr).2.1⟩
  have hc₃ := hc₂.of_frm f₃ r₃ k₃.wr (k₃.gpr .x0 (by decide))
  have hv₃ := hv₂.of_frmA hc₂.good.scr.nowrap (by omega_arith) f₃ (fun r hr => (range_frame _ r hr).2.2)
  obtain ⟨hb₂, hi₂⟩ := child_frm hc₁ (by unfold inner at hroom ⊢; omega_arith) f₂ (fun r hr => by
    rw [List.mem_singleton.mp hr]; have := slot_le (w := (k + 7) / 8) (show aXm < 8 by decide)
    unfold CrtWindowFive.tabBytes32; simp only; omega_arith)
  obtain ⟨hb₃, hi₃⟩ := child_frm hc₂ (by unfold inner at hroom ⊢; omega_arith) f₃ (fun r hr => by
    have := r₃ r hr; unfold CrtWindowFive.tabBytes32; omega_arith)
  have hw₃ : ∀ i < 32, word u₃.mem B (8 * i) = word u₁.mem B (8 * i) := fun i hi => by rw [hb₃ i hi, hb₂ i hi]
  have i₃ : InScr B Z t.mem u₃.mem := (i₁.trans hi₂).trans hi₃
  refine WP.seq (WP.mono (leaveQ_ok hc₃ (dl := (s.gpr .x1).toNat) (k := k)
    (by rw [hw₃ _ (by decide), hp₁ _ (by decide) (by decide) (by decide) (by decide), hL, ofNat_toNat64])
    (by rw [hw₃ _ (by decide)]; exact hK₁) (by rcases hdl with h | h <;> omega_arith)) fun u₄ ⟨⟨h0₄, h3₄, hm₄⟩, k₄⟩ => ?_)
  have K₄ : Keep (.x0 :: mmRegs) t u₄ := keep_trans K₃ (k₄.mono (by decide))
  rcases hdl with hdl | hdl
  · -- No q.
    have hq : (domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)).q = none := by
      rw [hdl]; exact domainOf_q2 _ _ (by omega_arith)
    refine WP.ite true (by rw [VG.Proof.MlKem.AArch64.eval_zero, h3₄, hdl]; simp) (fun _ => ?_) (fun h => by simp at h)
    refine WP.mono (ret_ok u₄ (by decide)) fun t' ⟨⟨h0', _⟩, k'⟩ => ⟨?_, keep_trans K₄ (k'.mono (by decide))⟩
    rw [h0', ite_eq_left (by rw [publicValid_iff, hq]; exact ⟨hR, fun _ h => by simp at h⟩)]; rfl
  · -- With q.
    have hq : (domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)).q =
        some (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0 + BitVec.ofNat 64 (2 * k)) k)) := by
      rw [hdl]; exact domainOf_q3 _ _ _
    refine WP.ite false (by
      rw [VG.Proof.MlKem.AArch64.eval_zero, h3₄, hdl]
      rw [show 3 * k - 2 * k = k by omega_arith]
      refine congrArg some (beq_eq_false_iff_ne.mpr fun h => ?_)
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_arith)] at this; have h00 : k = 0 := this; omega_arith) (fun h => by simp at h)
      (fun _ => ?_)
    have hc₄ := hc₃.toMem.congr hm₄ k₄.wr
    have hv₄ : XVals u₄ B (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0) k)) :=
      ⟨by rw [hm₄]; exact hv₃.n, by rw [hm₄]; exact hv₃.inv, by rw [hm₄]; exact hv₃.one⟩
    have hw₄ : ∀ i < 32, word u₄.mem B (8 * i) = word u₁.mem B (8 * i) := fun i hi => by rw [hm₄, hw₃ i hi]
    have i₄ : InScr B Z t.mem u₄.mem := i₃.trans (by rw [hm₄]; exact InScr.refl _ _ _)
    rw [hdl] at hsrcD
    refine WP.mono (cpQ_ok W M S hc₄ hv₄ hval hk1 hk2 hZ h0₄ (by rw [hw₄ _ (by decide)]; exact hWs₁)
      (by rw [hw₄ _ (by decide)]; exact hK₁)
      (by rw [hw₄ _ (by decide), hp₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hQ)
      (by rw [hw₄ _ (by decide)]; exact hY₁) (hsrcD.congrK i₄ K₄) (hyS.congrK i₄ K₄))
      fun t' ⟨h0', k'⟩ => ⟨?_, keep_trans K₄ (k'.mono (by decide))⟩
    have e : publicValid ⟨domainOf k (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat),
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x3) k)⟩ = true ↔
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x3) k) ^
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0 + BitVec.ofNat 64 (2 * k)) k) %
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0) k) = 1 := by
      rw [publicValid_iff, hq, hpk]
      simp only [Option.some.injEq, forall_eq']
      exact ⟨fun h => h.2, fun h => ⟨hpk ▸ hR, h⟩⟩
    rw [h0']; unfold bit; exact if_congr e.symm rfl rfl

/-- `vg_ffdh_check_public`. -/
theorem cp_correct (W : Window) (M : Mont) (S : Selector) (s : State) (h : cpContract.pre s) :
    ∃ t s', Exec isa (VG.Impl.Ffdh.AArch64.Domain.CheckPublic.code W.code S.code M.mm) s t s' ∧
      abiPreserved s s' ∧ cpContract.post s s' := by
  have c := cpCtx_of h
  have hk1 := c.k1
  have hk2 := c.k2
  have hZ := c.hZ
  have hn := c.hs.nowrap
  suffices hwp : WP isa (VG.Impl.Ffdh.AArch64.Domain.CheckPublic.code W.code S.code M.mm) s
      fun s' => abiPreserved s s' ∧ cpContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  unfold VG.Impl.Ffdh.AArch64.Domain.CheckPublic.code
  have hw : ∀ i < 22, InRegions s.wr (off (s.gpr .x5) (8 * i)) 8 := fun i hi => c.hs.st (by omega_arith)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (cpEntry_ok rfl hw) fun t₁ ⟨h0₁, hD₁, hL₁, hK₁, hY₁, ho₁, k₁⟩ => ?_
  have i₁ : InScr (s.gpr .x5) ((s.gpr .x6).toNat * 8) s.mem t₁.mem := InScr.of_outside ho₁ (by omega_arith)
  have hdom₁ := c.dom.congrK i₁ k₁
  have hpS : Src t₁ (s.gpr .x5) ((s.gpr .x6).toNat * 8) (s.gpr .x0)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x2).toNat) := by
    have := src_slice (off := 0) (len := (s.gpr .x2).toNat) hdom₁ (by rcases c.dl with h | h <;> rw [h] <;> omega_arith)
    simpa using this
  refine WP.mono (domHead_ok (c.hs.congr k₁.wr) h0₁ (by omega_arith) hk1 hk2 hD₁ (by rw [hK₁, ofNat_toNat64]) hpS
    (bytesAt_length _ _ _)) fun t₂ ⟨h9₂, hG₂, hQ₂, f₂, h0₂, k₂⟩ => ?_
  have hp₂ : ∀ i < 32, i ≠ sG → i ≠ sQ → word t₂.mem (s.gpr .x5) (8 * i) = word t₁.mem (s.gpr .x5) (8 * i) :=
    fun i hi h1 h2 => f₂.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> unfold sG sQ sFn at * <;> omega_arith) (by omega_arith)
  have i₂ : InScr (s.gpr .x5) ((s.gpr .x6).toNat * 8) s.mem t₂.mem := i₁.trans (InScr.of_frm f₂ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sG, sQ, sFn] <;> omega_arith)
  have K₂ : Keep (.x0 :: mmRegs) s t₂ := keep_trans (k₁.mono (by decide)) (k₂.mono (by decide))
  have hpk : (domainOf (s.gpr .x2).toNat (cpDom s)).p = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0)
      (s.gpr .x2).toNat) := domainOf_p _ _ (by rcases c.dl with h | h <;> omega_arith)
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x2).toNat))
    (s.gpr .x2).toNat) (by rw [eval_zero, h9₂]; cases Spec.Rsa.modulusValid _ _ <;> rfl) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x2).toNat))
        (s.gpr .x2).toNat = false := by simpa using hb
    refine WP.mono (ret_ok t₂ (by decide)) fun t' ⟨_, k'⟩ =>
      ⟨abiPreserved_of_keep (keep_trans K₂ (k'.mono (by decide))), fun hd => ?_⟩
    have := domainValid_mod hd
    rw [hpk, hv] at this
    exact absurd this (by decide)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x2).toNat))
        (s.gpr .x2).toNat = true := by simpa using hb
    refine WP.mono (cpMain_ok W M S c h0₂ (c.hs.congr (k₂.wr.trans k₁.wr))
      (by rw [hp₂ _ (by decide) (by decide) (by decide)]; exact hD₁)
      (by rw [hp₂ _ (by decide) (by decide) (by decide)]; exact hL₁)
      (by rw [hp₂ _ (by decide) (by decide) (by decide), hK₁, ofNat_toNat64])
      (by rw [hp₂ _ (by decide) (by decide) (by decide)]; exact hY₁)
      hQ₂ i₂ (k₂.rd.trans k₁.rd) (k₂.wr.trans k₁.wr) hv)
      fun t' ⟨h0', k'⟩ => ⟨abiPreserved_of_keep (keep_trans K₂ k'), fun _ => ?_⟩
    rw [h0']
    split <;> rfl

end VG.Proof.Ffdh.AArch64.CheckPublic
