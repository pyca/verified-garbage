module
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Context
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Flags
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckPrivate

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Entry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH private-key validation on x86-64: entry and modulus validation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def kpOf (s : State) : KpP :=
  ⟨stackArg s 1, (stackArg s 2).toNat * 8, (s.gpr .rdx).toNat, (s.gpr .rsi).toNat, s.gpr .rdi,
    kpDom s, s.gpr .r9, (stackArg s 0).toNat, s.gpr .rcx, kpY s, s.gpr .rsp,
    Spec.Ffdh.privateValid (Spec.Ffdh.domainOf (s.gpr .rdx).toNat (kpDom s)) (Spec.Rsa.os2ip (kpX s))⟩

theorem entry_base {s : State} (c : KpCtx s) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.entry) s fun t =>
      Base (kpOf s) (kpX s) t ∧ t.gpr .rdi = (kpOf s).B ∧
      InScr (kpOf s).B (kpOf s).Z s.mem t.mem ∧
      (∀ i < 6, word t.mem (kpOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Keep (.rdi :: mmRegs) s t := by
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (kpEntry_ok rfl (fun i hi => c.hs.st (by omega)) c.ha)
    fun t ⟨hd, hs, hh, hf, k⟩ => ?_
  have hi : InScr (kpOf s).B (kpOf s).Z s.mem t.mem := InScr.of_outside hf (by dsimp only [kpOf]; omega)
  refine ⟨⟨c.k1, c.k2, c.dl, bytesAt_length _ _ _, ?_, bytesAt_length _ _ _,
    c.xl1, c.xl2, c.hZ, c.hs.congr k.2.2, c.dom.congrK hi k, c.x.congrK hi k, c.y.congrK hi k,
    ?_, rfl⟩, hd, hi, hs, k.mono (by decide)⟩
  · change (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat).length = (s.gpr .rdx).toNat
    rw [bytesAt_length, c.yl]
  · change Slots t.mem (stackArg s 1) (kpOf s).headers
    simp only [KpP.headers, kpOf, ofNat_toNat64]
    intro e he
    exact hh e he

theorem dom_base {p : KpP} {xb : List Byte} {s : State} (h : Base p xb s) (hdi : s.gpr .rdi = p.B) :
    WP isa (.block domHead) s fun t => Base p xb t ∧ t.zf = some p.mv ∧ t.gpr .rdi = p.B ∧
      word t.mem p.B (8 * sG) = off p.dp p.k ∧ word t.mem p.B (8 * sQ) = off p.dp (2 * p.k) ∧
      InScr p.B p.Z s.mem t.mem ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ Keep (.rdi :: mmRegs) s t := by
  have hZ := h.hZ
  have hk := h.k1
  refine WP.mono (domHead_ok h.scr hdi (by omega) h.k1 h.k2
    (h.hdr (sDom, p.dp) (by simp [KpP.headers]))
    (h.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers])) (h.dom.take p.k) h.plen)
    fun t ⟨hz, hG, hQ, hf, hd, k⟩ => ?_
  have hi : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> unfold sG sQ sFn at * <;> omega)
  have hh : ∀ i < 32, i ≠ sG → i ≠ sQ → word t.mem p.B (8 * i) = word s.mem p.B (8 * i) :=
    fun i hi hg hq => hf.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only <;> unfold sG sQ sFn at * <;> omega) (by omega)
  refine ⟨h.keep hi k ?_, hz, hd, hG, hQ, hi, ?_, k.mono (by decide)⟩
  · intro e he
    simp only [KpP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hh _ (by dsimp only; decide) (by dsimp only; decide) (by dsimp only; decide)
  · intro i hi
    exact hh i (by omega) (by unfold sG sFn; omega) (by unfold sQ sFn; omega)

/-- Setup and load the private scalar, preserving the domain's pointers. -/
theorem setup_work {p : KpP} {xb : List Byte} {s : State} (h : Base p xb s) (hd : s.gpr .rdi = p.B)
    (hG : word s.mem p.B (8 * sG) = off p.dp p.k) (hQ : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k))
    (hm : p.mv = true) :
    WP isa (seqs ((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++
      VG.Impl.Rsa.X86_64.Crt.loadArr aXm sX sXl)) s
      (StepPost p s fun t => ∃ mi, Work p xb mi t ∧ t.gpr .rdi = off p.B (inner p.w)) := by
  have hk := h.k1
  have hk' := h.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold KpP.w; omega
  obtain ⟨hodd, _⟩ := valid_facts hm hk
  refine wp_seqs_append (by simp [pSetup]) (by simp [VG.Impl.Rsa.X86_64.Crt.loadArr])
    (WP.mono (setup_ok (B := p.B) (Z := p.Z) (k := p.k) (dp := p.dp) (pb := p.pb) h.scr hd hk hk' h.hZ
      (h.hdr (sDom, p.dp) (by simp [KpP.headers])) (h.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers]))
      (h.dom.take p.k) h.plen hodd) fun u ⟨mi, hc, hv, hWs, hf, k⟩ => ?_)
  obtain ⟨hi, hh, hs, hhead⟩ := setup_frame hk h.hZ hf
  have hb := h.keep hi k hh
  have hGu : word u.mem p.B (8 * sG) = off p.dp p.k := by
    rw [hhead _ (by decide) (by decide) (by decide) (by decide)]; exact hG
  have hQu : word u.mem p.B (8 * sQ) = off p.dp (2 * p.k) := by
    rw [hhead _ (by decide) (by decide) (by decide) (by decide)]; exact hQ
  have hxl := hb.xl2
  refine WP.mono (primeLoad_ok hc (by omega) (Nat.le_refl _) (by omega) (show aXm < 8 by decide)
    (show sX < 32 by decide) (show sXl < 32 by decide)
    (hb.hdr (sX, p.xp) (by simp [KpP.headers]))
    (by rw [hb.xlen]; exact hb.hdr (sXl, BitVec.ofNat 64 p.xl) (by simp [KpP.headers])) hb.x
    (by rw [hb.xlen]; exact hb.xl1) (by rw [hb.xlen]; omega)
    (by rw [hb.xlen]; omega)) fun t ⟨hc', hx, ho, kk⟩ => ?_
  have ff : Frm (off p.B (inner p.w)) [(slot p.w aXm, 8 * (p.w + 2))] u.mem t.mem := Frm.of_outside ho (by simp)
  have hXmle := slot_le (w := p.w) (show aXm < 8 by decide)
  have hr : ∀ r ∈ [(slot p.w aXm, 8 * (p.w + 2))], r.1 + r.2 ≤ slot p.w 8 + tabBytes p.w 32 := by
    simp only [List.mem_singleton]; rintro r rfl; omega
  obtain ⟨hb', hi', hs'⟩ := hb.child hc ff hr kk
  have hroom := room_k hk h.hZ
  change inner p.w + slot p.w 8 + tabBytes p.w 32 ≤ p.Z at hroom
  obtain ⟨hh', _⟩ := child_frm hc hroom ff hr
  have hn := hc.good.scr.nowrap
  have hv' := hv.of_frmA hn (show 1 ≤ p.w by omega) ff (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact arr_off p.w (by decide) (by decide))
  exact ⟨⟨mi, ⟨hb', hc'.toMem, hv', (hh' _ (by decide)).trans hWs,
    (hh' _ (by decide)).trans hGu, (hh' _ (by decide)).trans hQu, hx⟩, hc'.rdi⟩,
    hi.trans hi', fun i hi => (hs' i hi).trans (hs i hi), keep_trans k (kk.mono (by decide))⟩

end VG.Proof.Ffdh.X86_64.CheckPrivate
