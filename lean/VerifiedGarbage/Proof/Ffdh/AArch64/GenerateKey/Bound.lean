module

public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Ffdh.AArch64.Stage
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain

/-!
# `vg_ffdh_generate_key` on AArch64: the bound's scan

`Pa.bound`: in the outer workspace, `GenerateKey.bound` scans the bound's
octets (`KeyScalar.bnd`: q's, or p's) for the first nonzero one: its
pointer and the number of octets from it go to `sEp` and `sEl`, the octet
to `x3`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Ffdh.KeyScalar (bnd bnd_length)
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- The pointer to the bound's octets. -/
abbrev FD.bp (D : FD) : Addr := if D.dl = 3 * D.k then D.dp + BitVec.ofNat 64 (2 * D.k) else D.dp

/-- The bound's octets. -/
abbrev FD.bb (D : FD) : List Byte := bnd D.k D.dom

/-- Their first nonzero octet's index. -/
abbrev FD.bl (D : FD) : Nat := lead D.bb

/-- That octet. -/
abbrev FD.bc (D : FD) : Byte := D.bb.getD D.bl 0

theorem Base.bb_length {D : FD} {t : State} (hb : Base D t) : D.bb.length = D.k := by
  have := hb.doml
  exact bnd_length (by rw [this]; exact hb.dl)

theorem Base.bl_lt {D : FD} {t : State} (hb : Base D t) : D.bl < D.k := by
  have hl := hb.bb_length
  have hne : D.bb ≠ [] := by intro he; rw [he] at hl; have := hb.k1; simp at hl; omega
  have := lead_lt hne
  rw [hl] at this; exact this

theorem Pa.keep {D : FD} {mi : BitVec 64} {t u : State} (h : Pa D mi t) (hm : u.mem = t.mem) {rs : List Reg}
    (k : Keep rs t u) (h0 : .x0 ∉ rs) : Pa D mi u :=
  h.outside (o := 256) (n := 0) (by decide) (by simp only [inner, slot, hdrBytes]; omega) (fun x _ => by rw [hm])
    k.rd k.wr ((k.gpr .x0 h0).trans h.2.2.2.2.2.2)

/-- The slot of the bound's pointer. -/
abbrev FD.bs (D : FD) : Nat := if D.dl = 3 * D.k then sQ else sDom

/-- The scan's public data. -/
abbrev FD.bsp (D : FD) : ScanPub := ⟨D.B, D.Z, D.w, D.bp, D.bb⟩

/-- The scan's hypotheses. -/
theorem Pa.scanPreB {D : FD} {mi : BitVec 64} {t : State} (h : Pa D mi t) : ScanPre D.bs D.bsp t := by
  have hb := h.1
  have hk1 := hb.k1
  have hk2 := hb.k2
  have hdl := hb.doml
  have hs := h.2.2.2.2.1
  have hl := hb.bb_length
  have hne : D.bb ≠ [] := by intro he; rw [he] at hl; simp at hl; omega
  show Outer t D.B D.Z D.w ∧ word t.mem D.B (8 * D.bs) = D.bp ∧ word t.mem D.B (8 * sK) = BitVec.ofNat 64 D.bb.length ∧
    D.bb ≠ [] ∧ D.bb.length < 2 ^ 32 ∧ Src t D.B D.Z D.bp D.bb ∧ D.bs < 32
  refine ⟨h.outer, ?_, by rw [hl]; exact hs.get (i := sK) (by simp), hne, by omega, ?_, by
    simp only [FD.bs]; split <;> decide⟩
  · by_cases hq : D.dl = 3 * D.k
    · simp only [FD.bs, FD.bp, ite_eq_left hq]; exact hs.get (by simp)
    · simp only [FD.bs, FD.bp, ite_eq_right hq]; exact hs.get (by simp)
  · by_cases hq : D.dl = 3 * D.k
    · have e : D.bb = D.qb := by simp only [FD.bb, bnd, hdl]; rw [ite_eq_left hq]
      simp only [FD.bp, ite_eq_left hq]; rw [e]; exact hb.qsrc
    · have e : D.bb = D.dom.take D.k := by simp only [FD.bb, bnd, hdl]; rw [ite_eq_right hq]
      simp only [FD.bp, ite_eq_right hq]; rw [e]; exact hb.dom.take D.k

/-- The scan of the bound's octets, its pointer's slot chosen. -/
theorem Pa.scanB {D : FD} {mi : BitVec 64} {t : State} (h : Pa D mi t) :
    WP isa (seqs (VG.Impl.Ffdh.AArch64.Domain.scan D.bs)) t fun u => (Pa D mi u ∧
      word u.mem D.B (8 * sEp) = off D.bp D.bl ∧ word u.mem D.B (8 * sEl) = BitVec.ofNat 64 (D.k - D.bl) ∧
      u.gpr .x3 = BitVec.ofNat 64 D.bc.toNat ∧ Frm D.B [(8 * sEp, 8), (8 * sEl, 8)] t.mem u.mem) ∧ KX t u := by
  obtain ⟨hO, hp, hk, hne, hlt, hsrc, hsp⟩ := (h.scanPreB : Outer t D.B D.Z D.w ∧
    word t.mem D.B (8 * D.bs) = D.bp ∧ word t.mem D.B (8 * sK) = BitVec.ofNat 64 D.bb.length ∧
    D.bb ≠ [] ∧ D.bb.length < 2 ^ 32 ∧ Src t D.B D.Z D.bp D.bb ∧ D.bs < 32)
  have hl := h.1.bb_length
  refine WP.mono (scan_ok hO hsp hp hk hne hlt hsrc) fun u ⟨hEp, hEl, h3', f, k⟩ =>
    ⟨⟨h.hdr f k ((k.gpr .x0 (by decide)).trans h.2.2.2.2.2.2), hEp, by rw [hEl, hl], ?_, f⟩, k.mono (by decide)⟩
  rw [h3']
  simp only [FD.bc, FD.bl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (lead_lt hne), Option.getD_some]

theorem bs_eval {D : FD} {t : State} (h3 : t.gpr .x3 = BitVec.ofNat 64 (D.dl - 2 * D.k)) :
    isa.eval (.zero .x .x3) t = some (BitVec.ofNat 64 (D.dl - 2 * D.k) == 0) := by rw [eval_zero, h3]

/-- The branch of `bound` taken is the scan of the bound. -/
theorem bs_n {D : FD} {t : State} (hb : Base D t) (he : (BitVec.ofNat 64 (D.dl - 2 * D.k) == 0) = true) :
    D.bs = sDom := by
  have := hb.noq he
  have := hb.k1
  simp only [FD.bs]; rw [ite_eq_right (by omega)]

theorem bs_q {D : FD} {t : State} (hb : Base D t) (he : (BitVec.ofNat 64 (D.dl - 2 * D.k) == 0) = false) :
    D.bs = sQ := by
  simp only [FD.bs]; rw [ite_eq_left (hb.q he)]

/-- The scan of the bound's octets. -/
theorem Pa.bound {D : FD} {mi : BitVec 64} {t : State} (h : Pa D mi t) :
    WP isa (seqs GenerateKey.bound) t fun u => (Pa D mi u ∧ word u.mem D.B (8 * sEp) = off D.bp D.bl ∧
      word u.mem D.B (8 * sEl) = BitVec.ofNat 64 (D.k - D.bl) ∧ u.gpr .x3 = BitVec.ofNat 64 D.bc.toNat ∧
      Frm D.B [(8 * sEp, 8), (8 * sEl, 8)] t.mem u.mem) ∧ KX t u := by
  have hb := h.1
  unfold GenerateKey.bound
  refine wp_seqs_cons (by simp) (WP.mono h.qtest fun t₁ ⟨⟨h3, hm₁⟩, k₁⟩ => ?_)
  have hP₁ : Pa D mi t₁ := h.keep hm₁ k₁ (by decide)
  rw [seqs_one]
  have post : WP isa (seqs (VG.Impl.Ffdh.AArch64.Domain.scan D.bs)) t₁ fun u => (Pa D mi u ∧
      word u.mem D.B (8 * sEp) = off D.bp D.bl ∧ word u.mem D.B (8 * sEl) = BitVec.ofNat 64 (D.k - D.bl) ∧
      u.gpr .x3 = BitVec.ofNat 64 D.bc.toNat ∧ Frm D.B [(8 * sEp, 8), (8 * sEl, 8)] t.mem u.mem) ∧ KX t u :=
    WP.mono hP₁.scanB fun u ⟨⟨a, b, c, d, f⟩, k⟩ => ⟨⟨a, b, c, d, fun x hx => by rw [f x hx, hm₁]⟩,
      keep_trans (k₁.mono (by decide)) k⟩
  refine WP.ite (BitVec.ofNat 64 (D.dl - 2 * D.k) == 0) (bs_eval h3) (fun he => ?_) (fun he => ?_)
  · rw [← bs_n hb he]; exact post
  · rw [← bs_q hb he]; exact post

end VG.Proof.Ffdh.AArch64
