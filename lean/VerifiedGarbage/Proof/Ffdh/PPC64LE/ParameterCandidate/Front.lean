module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Contract
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Base
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Entry
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.ZeroOut
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.End
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# An FFDH parameter candidate on PPC64LE: the front

`front_ok`: the entry and `out` zeroed give `St` for the arguments
(`ppOf`), with `used` at `out_len`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE

/-- The candidate's arguments, on entry. -/
def ppOf (s : State) : PP where
  B := s.gpr .r10
  n := (stackArg s 0).toNat
  op := s.gpr .r3
  up := s.gpr .r5
  bits := (s.gpr .r6).toNat
  g := ((s.gpr .r7).setWidth 32).toNat
  rp := s.gpr .r8
  r := pcRand s
  sp := s.sp
  sv i := if i < 18 then s.gpr (Impl.Ffdh.PPC64LE.ParameterCandidate.saved i) else s.lr
  toc := s.gpr .r2

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

theorem zext_eq (x : BitVec 64) : (x.setWidth 32).setWidth 64 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq; simp

/-- Memory kept outside a region. -/
theorem out_word {O B : Addr} {L Z : Nat} {m m' : Mem} (hd : (⟨O, L⟩ : Region).Disjoint ⟨B, Z⟩)
    (hm : Outside O 0 L m m') (hnw : B.toNat + Z ≤ 2 ^ 64) {d : Nat} (hdz : d + 8 ≤ Z) :
    m'.readW (B + BitVec.ofNat 64 d) 64 = m.readW (B + BitVec.ofNat 64 d) 64 := by
  refine Mem.readW_congr fun i hi => hm _ (Or.inr ?_)
  by_contra hc
  exact hd (B + BitVec.ofNat 64 d + BitVec.ofNat 64 i) (by simp only [Region.Contains]; simp only [ofs] at hc; omega)
    (by simp only [Region.Contains]; rw [VG.Offset.add_add, Mem.sub_ofNat_toNat B (by omega)]; omega)

theorem saved_notin : ∀ i < 18, Impl.Ffdh.PPC64LE.ParameterCandidate.saved i ∉ ([.r0, .r11, .r12] : List Reg) := by
  decide

theorem front_ok (s : State) (h : pcPre s) :
    WP isa (.seq (.block entry) zeroOut) s fun t =>
      St (ppOf s) t ∧ word t.mem (ppOf s).B 152 = BitVec.ofNat 64 (ppOf s).L ∧ t.lr = s.lr := by
  obtain ⟨hsp, hspT, hrd, hwr, dOU, dOR, dOS, dOA, dUR, dUS, dUA, dRS, dSA, qO, qU, qR, qS, qA, nwO, nwU, nwR,
    nwS, hb1, hb2, hL, hg, hsw⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsw
  have hn : stackArg s 0 = BitVec.ofNat 64 (stackArg s 0).toNat := (ofNat_toNat _).symm
  have h8n : 160 ≤ 8 * (stackArg s 0).toNat := by omega
  have hscr : Scr s (s.gpr .r10) (8 * (stackArg s 0).toNat) :=
    Scr.of_mem (by rw [hwr, Nat.mul_comm]; simp) (by omega)
  have hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8 :=
    ⟨⟨stackArgAddr s 0, 8⟩, by rw [hrd]; simp, by simp [Region.Contains]⟩
  refine WP.seq ?_
  simp only [entry]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (entryA_ok rfl hn hargs h8n (hscr.st (by omega))) fun tA ⟨⟨a11, a12, am⟩, ka⟩ => ?_
  refine WP.mono (saves_ok (s₀ := tA) a11 h8n (by omega) fun i hi => by
    rw [ka.wr]; exact hscr.st (by omega)) fun tS hS => ?_
  have hS10 : tS.gpr .r10 = s.gpr .r10 := by rw [hS.gpr, ka.gpr _ (by decide)]
  refine WP.mono (header_ok (s := tS) hS10 fun d hd => by
    rw [hS.wr, ka.wr]; exact hscr.st (d := d) (by omega)) fun t₁ ⟨⟨c31, c7, cm⟩, kc⟩ => ?_
  have gS : ∀ r, r ∉ ([.r0, .r11, .r12] : List Reg) → tS.gpr r = s.gpr r := fun r hr => by
    rw [hS.gpr]; exact ka.gpr r hr
  have hS12 : tS.gpr .r12 = BitVec.ofNat 64 (stackArg s 0).toNat := by rw [hS.gpr]; exact a12
  obtain ⟨w0, w16, w24, w152, w32, w40, w128, w136, w144⟩ := hdrW_words tS.mem (s.gpr .r10) (tS.gpr .r12)
    (tS.gpr .r3) (tS.gpr .r4) (tS.gpr .r5) (tS.gpr .r6) (((tS.gpr .r7).setWidth 32).setWidth 64) (tS.gpr .r8)
    (tS.gpr .r9)
  rw [← cm] at w0 w16 w24 w152 w32 w40 w128 w136 w144
  have hwr₁ : t₁.wr = s.wr := by rw [kc.wr, hS.wr, ka.wr]
  have hscr₁ : Scr t₁ (s.gpr .r10) (8 * (stackArg s 0).toNat) := hscr.congr hwr₁
  have hout₁ : Scr t₁ (s.gpr .r3) (s.gpr .r4).toNat := (Scr.of_mem (by rw [hwr]; simp) nwO).congr hwr₁
  refine WP.mono (zeroOut_ok (s := t₁) hscr₁ hout₁ c31 (by rw [gS _ (by decide)] at w16; exact w16)
    (by rw [gS _ (by decide), ← ofNat_toNat (s.gpr .r4)] at w24; exact w24) (by omega) (by omega) (by omega))
    fun t ⟨⟨zb, zo⟩, kz⟩ => ?_
  have hnw := hscr.nowrap
  have dOS' : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint ⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩ := by
    rw [Nat.mul_comm]; exact dOS
  have wsW : ∀ d, d + 8 ≤ 8 * (stackArg s 0).toNat →
      t.mem.readW (s.gpr .r10 + BitVec.ofNat 64 d) 64 = t₁.mem.readW (s.gpr .r10 + BitVec.ofNat 64 d) 64 :=
    fun d hd => out_word dOS' zo hnw hd
  -- The memory, changed only in the working space and `out`.
  have fr : Frame [⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩, ⟨s.gpr .r3, (s.gpr .r4).toNat⟩] s.mem t.mem := by
    have ws_of : ∀ x, (∀ r ∈ ([⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩, ⟨s.gpr .r3, (s.gpr .r4).toNat⟩] : List Region),
        ¬ r.Contains x 1) → 8 * (stackArg s 0).toNat ≤ ofs (s.gpr .r10) x ∧ (s.gpr .r4).toNat ≤ ofs (s.gpr .r3) x :=
      fun x hx => by
        have h1 := hx _ (List.mem_cons_self ..)
        have h2 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        simp only [Region.Contains, ofs] at h1 h2 ⊢; omega
    intro x hx
    obtain ⟨hx1, hx2⟩ := ws_of x hx
    rw [zo x (Or.inr (by omega)), cm, hdrW_frm _ _ _ _ _ _ _ _ _ _ x (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (by omega)), hS.out x (Or.inr (by omega)), am]
    exact writeW_outside s.mem (s.gpr .r10) (d := 8 * (stackArg s 0).toNat - 160 + 144) s.lr (by omega) x
      (Or.inr (by omega))
  have hlen : (pcRand s).length = (s.gpr .r9).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  have hLe : (s.gpr .r4).toNat = (ppOf s).L := hL
  have kall : ∀ r, r ∉ ([.r0, .r4, .r5, .r7, .r11, .r12, .r31] : List Reg) → t.gpr r = s.gpr r := fun r hr => by
    rw [kz.gpr r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl <;> simp)),
      kc.gpr r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> simp)),
      gS r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl <;> simp))]
  have hd : ∀ {d}, d + 8 ≤ 256 → word t.mem (s.gpr .r10) d = word t₁.mem (s.gpr .r10) d := fun hd' =>
    wsW _ (by omega)
  have sav : ∀ i < 19, word t.mem (s.gpr .r10) (8 * (stackArg s 0).toNat - saveBytes + 8 * i) = (ppOf s).sv i := by
    intro i hi
    simp only [saveBytes]
    rw [show word t.mem (s.gpr .r10) (8 * (stackArg s 0).toNat - 160 + 8 * i) =
        word t₁.mem (s.gpr .r10) (8 * (stackArg s 0).toNat - 160 + 8 * i) from wsW _ (by omega), cm,
      (hdrW_frm _ _ _ _ _ _ _ _ _ _).word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by omega))
        (by omega)]
    by_cases h18 : i < 18
    · rw [hS.saved i h18, ka.gpr _ (saved_notin i h18)]; simp [ppOf, h18]
    · obtain rfl : i = 18 := by omega
      rw [hS.lrW]; simp only [word, off] at am ⊢
      rw [am, show 8 * (stackArg s 0).toNat - 160 + 8 * 18 = 8 * (stackArg s 0).toNat - 160 + 144 by omega,
        VG.Proof.MillerRabin.PPC64LE.Search.rw_self]
      simp [ppOf]
  have dRS' : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩ := by
    rw [Nat.mul_comm]; exact dRS
  have dUS' : (⟨s.gpr .r5, 8⟩ : Region).Disjoint ⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩ := by
    rw [Nat.mul_comm]; exact dUS
  have hwrt : t.wr = s.wr := by rw [kz.wr, hwr₁]
  refine ⟨⟨hscr₁.congr kz.wr, (kz.gpr .r31 (by decide)).trans c31,
    ⟨(hd (d := 0) (by decide)).trans (w0.trans hS12),
     (hd (d := 16) (by decide)).trans (w16.trans (gS .r3 (by decide))),
     (hd (d := 24) (by decide)).trans (w24.trans ((gS .r4 (by decide)).trans (by rw [← hLe, ofNat_toNat]))),
     (hd (d := 32) (by decide)).trans (w32.trans (gS .r5 (by decide))),
     (hd (d := 40) (by decide)).trans (w40.trans ((gS .r6 (by decide)).trans (ofNat_toNat _).symm)),
     (hd (d := 128) (by decide)).trans (w128.trans (by rw [gS .r7 (by decide), zext_eq]; rfl)),
     (hd (d := 136) (by decide)).trans (w136.trans (gS .r8 (by decide))),
     (hd (d := 144) (by decide)).trans (w144.trans ((gS .r9 (by decide)).trans (by
       rw [show (ppOf s).r.length = (s.gpr .r9).toNat from hlen, ofNat_toNat])))⟩,
    ⟨fun i hi => ?_, fun i hi x hx he => ?_, ?_, ?_, ?_, fun x hx => ?_, ?_, fun x hx => ?_, by show (below s.sp 176).Disjoint ⟨s.gpr .r8, (pcRand s).length⟩; rw [hlen]; exact qR,
      by show (below s.sp 176).Disjoint ⟨s.gpr .r3, (ppOf s).L⟩; rw [← hLe]; exact qO, qU, by
      show (⟨s.gpr .r3, (ppOf s).L⟩ : Region).Disjoint _; rw [← hLe]; exact dOU⟩,
    ⟨hb1, hb2, hg, by simp only [ppOf, PP.L] at hLe ⊢; omega, by simp only [ppOf]; omega,
      by show (pcRand s).length < 2 ^ 64; rw [hlen]; exact (s.gpr .r9).isLt⟩,
    by rw [hwrt, hwr]; simp [ppOf, PP.Z, Nat.mul_comm], by rw [kz.sp, kc.sp, hS.sp, ka.sp]; rfl, hsp,
    by show (below s.sp 176).Disjoint ⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩; rw [Nat.mul_comm]; exact qS,
    sav, kall .r2 (by decide)⟩,
    (hd (d := 152) (by decide)).trans (w152.trans ((gS .r4 (by decide)).trans (by rw [← hLe, ofNat_toNat]))),
    by rw [kz.lr, kc.lr, hS.lr, ka.lr]⟩
  · rw [kz.rd, kc.rd, hS.rd, ka.rd, hrd]
    rw [show (ppOf s).r.length = (s.gpr .r9).toNat from hlen] at hi
    exact ⟨⟨s.gpr .r8, (s.gpr .r9).toNat⟩, by simp, VG.Proof.Bignum.contains_byte _ hi (by omega)⟩
  · rw [show (ppOf s).r.length = (s.gpr .r9).toNat from hlen] at hi
    subst he
    exact dRS' _ (VG.Proof.Bignum.contains_byte _ hi (by omega)) (VG.Proof.Bignum.contains_scr hx)
  · show Spec.Rsa.bytesAt t.mem (s.gpr .r8) (pcRand s).length = pcRand s
    rw [hlen]
    refine VG.Proof.Rsa.rsa_bytes_frame fr (s.gpr .r9).isLt fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRS'
    · exact dOR.symm
  · show Spec.Rsa.bytesAt t.mem (s.gpr .r3) (ppOf s).L = List.replicate (ppOf s).L 0
    rw [← hLe]; exact Pub.zero_bytes zb
  · show Scr t (s.gpr .r3) (ppOf s).L
    rw [← hLe]; exact hout₁.congr kz.wr
  · have hx' : ofs (s.gpr .r3) x < (s.gpr .r4).toNat := by rw [hLe]; exact hx
    exact VG.Proof.Bignum.out_scr dOS' (by simp only [Region.Contains]; simp only [ofs] at hx'; omega)
  · exact (Scr.of_mem (by rw [hwr]; simp) nwU).congr hwrt
  · have hx' : ofs (s.gpr .r5) x < 8 := hx
    exact VG.Proof.Bignum.out_scr dUS' (by simp only [Region.Contains]; simp only [ofs] at hx'; omega)

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
