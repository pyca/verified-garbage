module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Pow
public import VerifiedGarbage.Proof.Ffdh.AArch64.Checks
public import VerifiedGarbage.Proof.Ffdh.AArch64.Ws
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# FFDH on AArch64: the front of the domain operations

From the outer header with the domain's pointer and p's length: the check of
p (`domHead_ok`); the outer workspace and the inner one for p, with p, `-p⁻¹`
and the number 1 (`setup_ok`); `R² mod p` (`r2_ctx`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (wsEnd wsNew loadArr leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.CrtWindowFive VG.Proof.Bignum.AArch64.WindowFive
open VG.Proof.MlKem.AArch64 (Keep)

/-- Header slots of the outer workspace with given values. -/
def Slots (m : Mem) (B : Addr) (L : List (Nat × BitVec 64)) : Prop := ∀ p ∈ L, word m B (8 * p.1) = p.2

theorem Slots.frm {m m' : Mem} {B : Addr} {L : List (Nat × BitVec 64)} {rs : List (Nat × Nat)} (h : Slots m B L)
    (hf : Frm B rs m m') (hr : ∀ p ∈ L, ∀ r ∈ rs, 8 * p.1 + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * p.1)
    (hL : ∀ p ∈ L, p.1 < 32) : Slots m' B L := fun p hp => by
  rw [hf.word_eq (hr p hp) (by have := hL p hp; omega_arith)]; exact h p hp

/-! ## The check of p -/

/-- `domHead`'s loads and stores before the check of p. -/
theorem domHead1_ok {s : State} {B : Addr} {Z k : Nat} {dp : Addr} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hZ : 256 ≤ Z) (hD : word s.mem B (8 * sDom) = dp)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) :
    WP isa (.block [ldh .x2 sDom, ldh .x3 sK, .add .x .x4 .x2 .x3, sth .x4 sG, .add .x .x4 .x4 .x3, sth .x4 sQ]) s
      fun t => (t.gpr .x2 = dp ∧ t.gpr .x3 = BitVec.ofNat 64 k ∧
        t.mem = (s.mem.writeW (off B (8 * sG)) (dp + BitVec.ofNat 64 k)).writeW (off B (8 * sQ))
          (dp + BitVec.ofNat 64 k + BitVec.ofNat 64 k)) ∧ Keep [.x2, .x3, .x4] s t := by
  have hn := hs.nowrap
  have eG : sG = 27 := rfl
  have eQ : sQ = 28 := rfl
  have eD : sDom = 16 := rfl
  have eK : sK = 18 := rfl
  refine WP.keep [.x2, .x3, .x4] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h0, hdr_enc (show sDom < 32 by decide), hdr_enc (show sK < 32 by decide), hdr_enc (show sG < 32 by decide),
    hdr_enc (show sQ < 32 by decide), hs.ld (d := 8 * sDom) (by omega_arith), hs.ld (d := 8 * sK) (by omega_arith),
    hs.st (d := 8 * sG) (by omega_arith), hs.st (d := 8 * sQ) (by omega_arith), hD, hK]

/-- `domHead`: g's and q's pointers into their slots, and `x9 :=` whether p (the
first `p_len` octets of the domain) is a valid modulus. -/
theorem domHead_ok {s : State} {B : Addr} {Z k : Nat} {dp : Addr} {pb : List Byte} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hZ : 256 ≤ Z) (hk1 : 64 ≤ k) (hk2 : k ≤ 1024)
    (hD : word s.mem B (8 * sDom) = dp) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hsrc : Src s B Z dp pb) (hl : pb.length = k) :
    WP isa (.block domHead) s fun t =>
      t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid (Spec.Rsa.os2ip pb) k).toNat ∧
      word t.mem B (8 * sG) = dp + BitVec.ofNat 64 k ∧ word t.mem B (8 * sQ) = dp + BitVec.ofNat 64 (2 * k) ∧
      Frm B [(8 * sG, 8), (8 * sQ, 8)] s.mem t.mem ∧ t.gpr .x0 = B ∧
      Keep [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] s t := by
  have hn := hs.nowrap
  have eG : sG = 27 := rfl
  have eQ : sQ = 28 := rfl
  have eD : sDom = 16 := rfl
  have eK : sK = 18 := rfl
  unfold domHead
  rw [show ([ldh .x2 sDom, ldh .x3 sK, .add .x .x4 .x2 .x3, sth .x4 sG, .add .x .x4 .x4 .x3, sth .x4 sQ] ++ invalid) =
    [ldh .x2 sDom, ldh .x3 sK, .add .x .x4 .x2 .x3, sth .x4 sG, .add .x .x4 .x4 .x3, sth .x4 sQ] ++ invalid from rfl,
    WP.block_append_iff]
  refine WP.mono (domHead1_ok hs h0 hZ hD hK) fun t₁ ⟨⟨h2, h3, hm₁⟩, k₁⟩ => ?_
  have o₁ := writeW_outside s.mem B (d := 8 * sG) (dp + BitVec.ofNat 64 k) (by omega_arith)
  have o₂ := writeW_outside (s.mem.writeW (off B (8 * sG)) (dp + BitVec.ofNat 64 k)) B (d := 8 * sQ)
    (dp + BitVec.ofNat 64 k + BitVec.ofNat 64 k) (by omega_arith)
  have hsrc₁ : Src t₁ B Z dp pb := hsrc.congr (fun x hx => by
      rw [hm₁, o₂ x (Or.inr (by omega_arith)), o₁ x (Or.inr (by omega_arith))]) k₁.rd k₁.wr
  refine WP.mono (invalid_ok h2 h3 hk1 hk2 hl (fun i hi => hsrc₁.rd i (by omega_arith)) (fun i hi => hsrc₁.val i _))
    fun t ⟨h9, hm, k₂⟩ => ⟨h9, ?_, ?_, ?_, (k₂.gpr .x0 (by decide)).trans ((k₁.gpr .x0 (by decide)).trans h0),
      (k₁.trans k₂).mono (by decide)⟩
  · rw [hm, hm₁, o₂.word (by omega_arith) (by omega_arith)]; exact word_writeW_self _ _ _ _
  · rw [hm, hm₁, word_writeW_self, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith
  · intro x hx
    rw [hm, hm₁, o₂ x (hx (8 * sQ, 8) (by simp)), o₁ x (hx (8 * sG, 8) (by simp))]

/-! ## The workspaces -/

/-- What `head` and `pSetup` change in the outer workspace. -/
def setupR (w : Nat) : List (Nat × Nat) := [(8 * sW, 8), (8 * sArr 0, 64), (8 * sWs, 8), (inner w, slot w 8)]

/-- A header slot that `head` and `pSetup` don't write is outside `setupR`. -/
theorem setupR_word (w : Nat) {i : Nat} (hi : i < 32) (h1 : i ≠ sW) (h2 : i ≠ sWs) (h3 : i < sArr 0 ∨ sArr 0 + 8 ≤ i) :
    ∀ r ∈ setupR w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
  have h8 := hdr_lt_slot w 8 hi
  simp only [setupR, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  unfold sW sWs sArr sFn at *
  exact ⟨by omega, by omega, by omega, Or.inl h8⟩

/-- `setupR` within a working space with room for the inner workspace. -/
theorem setupR_le (w : Nat) {Z : Nat} (h : inner w + slot w 8 ≤ Z) : ∀ r ∈ setupR w, r.1 + r.2 ≤ Z := by
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  simp only [setupR, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  unfold sW sWs sArr sFn at *
  exact ⟨by omega, by omega, by omega, h⟩

theorem wsWords_k {k : Nat} (hk : 16 ≤ k) : wsWords k = (k + 7) / 8 := by unfold wsWords; omega_arith

/-- The workspaces' room in the working space of `16 k + 32` words. -/
theorem room_k {k Z : Nat} (hk : 64 ≤ k) (hZ : 128 * k + 256 ≤ Z) :
    inner ((k + 7) / 8) + slot ((k + 7) / 8) 8 + tabBytes32 ((k + 7) / 8) ≤ Z := by
  simp only [inner, slot, hdrBytes, tabBytes32]
  generalize hw : (k + 7) / 8 = w
  have h8 : 8 * w ≤ k + 7 := by omega_arith
  have e : 256 + 8 * (8 * (w + 2)) + (256 + 8 * (8 * (w + 2))) + 32 * (8 * (w + 2)) = 384 * w + 1280 := by omega_arith
  rw [e]
  omega_arith

/-- The outer workspace, once back from the inner one. -/
theorem Outer.of_sub {t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} (hc : SubCtx t B Z o w wx mi)
    (h0 : t.gpr .x0 = B) (hroom : inner w + slot w 8 + tabBytes32 w ≤ Z) (hw2 : 2 ≤ w) (hw : w < 2 ^ 28) :
    Outer t B Z w :=
  ⟨hc.scr, h0, hc.nw, hc.narr, hroom, hw2, hw⟩

/-- `head`, then the inner workspace for p, entered, with p, `-p⁻¹` and the
number 1. -/
theorem setup_ok {s : State} {B : Addr} {Z k : Nat} {dp : Addr} {pb : List Byte} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hk1 : 64 ≤ k) (hk2 : k ≤ 1024) (hZ : 128 * k + 256 ≤ Z)
    (hD : word s.mem B (8 * sDom) = dp) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hsrc : Src s B Z dp pb) (hl : pb.length = k) (hodd : Spec.Rsa.os2ip pb % 2 = 1) :
    WP isa (seqs (([.block head] : List (Prog isa)) ++ pSetup)) s fun t => ∃ mi,
      SubCtx t B Z (inner ((k + 7) / 8)) ((k + 7) / 8) ((k + 7) / 8) mi ∧
      XVals t B (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip pb) ∧
      word t.mem B (8 * sWs) = off B (inner ((k + 7) / 8)) ∧
      Frm B (setupR ((k + 7) / 8)) s.mem t.mem ∧ Keep (.x0 :: mmRegs) s t := by
  have hn := hs.nowrap
  have hroom := room_k hk1 hZ
  have eW : wsWords k = (k + 7) / 8 := wsWords_k (by omega_arith)
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have eW6 : sW = 6 := rfl
  have eA8 : sArr 0 = 8 := rfl
  have eWs : sWs = 29 := rfl
  have hi8 : 8 * 32 ≤ inner ((k + 7) / 8) := by simp only [inner, slot, hdrBytes]; omega_arith
  have hiZ : inner ((k + 7) / 8) + slot ((k + 7) / 8) 8 ≤ Z := by unfold tabBytes32 at hroom; omega_arith
  refine wp_seqs_cons (by simp [pSetup]) (WP.mono (head_ok hs h0 (by unfold inner at hroom; omega_arith) (by omega_arith) hK)
    fun s₁ ⟨h12, hW, hA, f₁, k₁⟩ => ?_)
  have hO : Outer s₁ B Z ((k + 7) / 8) :=
    ⟨hs.congr k₁.wr, (k₁.gpr .x0 (by decide)).trans h0, hW, hA, hroom, by omega_arith, by omega_arith⟩
  have hr₁ : ∀ i < 32, i ≠ sW → (i < sArr 0 ∨ sArr 0 + 8 ≤ i) → word s₁.mem B (8 * i) = word s.mem B (8 * i) :=
    fun i hi h1 h2 => f₁.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)
  have hK₁ : word s₁.mem B (8 * sK) = BitVec.ofNat 64 k := by rw [hr₁ _ (by decide) (by decide) (by decide)]; exact hK
  have hD₁ : word s₁.mem B (8 * sDom) = dp := by rw [hr₁ _ (by decide) (by decide) (by decide)]; exact hD
  have hsrc₁ : Src s₁ B Z dp pb := hsrc.congrK (InScr.of_frm f₁ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) k₁
  unfold pSetup
  refine wp_seqs_cons (by simp [modSetup, loadArr]) (WP.mono (wsSetup_ok (len := k) hO (by decide) (by decide)
    (by rw [hK₁]) (by omega_arith) (by omega_arith)) fun s₂ ⟨hc₂, hWs₂, f₂, k₂⟩ => ?_)
  rw [eW] at hc₂
  have hb₂ : ∀ i < 32, i ≠ sWs → word s₂.mem B (8 * i) = word s₁.mem B (8 * i) := fun i hi hne =>
    f₂.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)
  have i₂ : InScr B Z s₁.mem s₂.mem := InScr.of_frm f₂ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith
  refine WP.mono (modSetup_ok hc₂ (by omega_arith) (Nat.le_refl _) (by omega_arith) (show sDom < 32 by decide)
    (show sK < 32 by decide) (by rw [hb₂ _ (by decide) (by decide)]; exact hD₁)
    (by rw [hb₂ _ (by decide) (by decide), hl]; exact hK₁) (hsrc₁.congrK i₂ k₂) (by omega_arith) (by rw [hl]) hodd)
    fun t ⟨mi, hc, hv, f₃, k₃⟩ => ⟨mi, hc, hv, ?_, ?_, ?_⟩
  · have hr₃ : ∀ r ∈ [(slot ((k + 7) / 8) aN, 8 * ((k + 7) / 8 + 2)), (slot ((k + 7) / 8) aOne, 8 * ((k + 7) / 8 + 2)),
        (8 * sMinv, 8)], r.1 + r.2 ≤ slot ((k + 7) / 8) 8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact slot_le (by decide)
      · exact slot_le (by decide)
      · have := hdr_lt_slot ((k + 7) / 8) 8 (show sMinv < 32 by decide); simp only; omega_arith
    rw [f₃.word_below hr₃ (by omega_arith) (by omega_arith) (by omega_arith)]; exact hWs₂
  · intro x hx
    have hr₃ : ∀ r ∈ [(slot ((k + 7) / 8) aN, 8 * ((k + 7) / 8 + 2)), (slot ((k + 7) / 8) aOne, 8 * ((k + 7) / 8 + 2)),
        (8 * sMinv, 8)], inner ((k + 7) / 8) + r.1 + r.2 ≤ 2 ^ 64 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · have := slot_le (w := (k + 7) / 8) (show aN < 8 by decide); simp only; omega_arith
      · have := slot_le (w := (k + 7) / 8) (show aOne < 8 by decide); simp only; omega_arith
      · have := hdr_lt_slot ((k + 7) / 8) 8 (show sMinv < 32 by decide); simp only; omega_arith
    have g₃ := f₃.rebase (by omega_arith) hr₃
    rw [g₃ x (fun r hr => by
      simp only [shiftRanges, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
      have hx' := hx (inner ((k + 7) / 8), slot ((k + 7) / 8) 8) (by simp [setupR])
      have s1 := slot_le (w := (k + 7) / 8) (show aN < 8 by decide)
      have s2 := slot_le (w := (k + 7) / 8) (show aOne < 8 by decide)
      have s3 := hdr_lt_slot ((k + 7) / 8) 8 (show sMinv < 32 by decide)
      rcases hr with rfl | rfl | rfl <;> simp only at hx' ⊢ <;> omega_arith),
      f₂ x (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hx (8 * sWs, 8) (by simp [setupR])
        · have hx' := hx (inner ((k + 7) / 8), slot ((k + 7) / 8) 8) (by simp [setupR])
          simp only at hx' ⊢; omega_arith),
      f₁ x (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hx (8 * sW, 8) (by simp [setupR])
        · exact hx (8 * sArr 0, 64) (by simp [setupR]))]
  · exact keep_trans ((k₁.trans k₂).mono (by decide)) (k₃.mono (by decide))

/-- `R² mod p` in the inner workspace for a valid modulus p. -/
theorem r2_ctx (M : Mont) {t : State} {B : Addr} {Z k : Nat} {mi : BitVec 64} {pb : List Byte}
    (hc : SubCtx t B Z (inner ((k + 7) / 8)) ((k + 7) / 8) ((k + 7) / 8) mi)
    (hv : XVals t B (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip pb))
    (hval : Spec.Rsa.modulusValid (Spec.Rsa.os2ip pb) k = true) (hk1 : 64 ≤ k) (hk2 : k ≤ 1024)
    (hZ : 128 * k + 256 ≤ Z) :
    WP isa (seqs (r2Steps M.mm)) t fun t' =>
      ModCtx t' B Z (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip pb) ∧
      Frm (off B (inner ((k + 7) / 8))) (r2Ranges ((k + 7) / 8)) t.mem t'.mem ∧ Keep mmRegs t t' := by
  obtain ⟨hodd, h1, hlo⟩ := valid_facts hval hk1
  have hroom := room_k hk1 hZ
  have hGn := hc.good.scr.nowrap
  refine WP.mono (r2_ok M hc.good (Nat.le_refl _) (by omega_arith) (by omega_arith) hv.n hv.inv hodd hlo)
    fun t' ⟨hg', hlt, hr, f, kk⟩ => ?_
  have hr' : ∀ r ∈ r2Ranges ((k + 7) / 8), 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot ((k + 7) / 8) 8 := fun r hr' => by
    refine ⟨?_, r2Ranges_le ((k + 7) / 8) r hr'⟩
    simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl <;> simp only [slot, hdrBytes, aAcc, aTmp, aR2, sCnt, sFn] <;> omega_arith
  refine ⟨⟨hc.of_frm f hr' kk.wr (kk.gpr .x0 (by decide)), hv.of_frmA hGn (by omega_arith) f (fun r hr'' => ⟨?_, ?_⟩),
    hlt, hr, hodd, h1, by unfold inner at hroom ⊢; omega_arith, by omega_arith, by omega_arith⟩, f, kk⟩
  · exact r2Ranges_arr _ (j := aN) (by decide) (by decide) (by decide) r hr'' |>.symm
  · exact r2Ranges_arr _ (j := aOne) (by decide) (by decide) (by decide) r hr'' |>.symm

/-! ## Octets outside the working space -/

theorem src_slice {s : State} {B : Addr} {Z : Nat} {p : Addr} {m : Mem} {n : Nat} (h : Src s B Z p (Spec.Rsa.bytesAt m p n))
    {off len : Nat} (hle : off + len ≤ n) :
    Src s B Z (p + BitVec.ofNat 64 off) (Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 off) len) := by
  have e : ∀ i, p + BitVec.ofNat 64 off + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (off + i) := fun i => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · simp only [VG.Proof.Bignum.bytesAt_length] at hi
    rw [e]; exact h.rd (off + i) (by simp only [VG.Proof.Bignum.bytesAt_length]; omega_arith)
  · simp only [VG.Proof.Bignum.bytesAt_length] at hi
    have := h.val (off + i) (by simp only [VG.Proof.Bignum.bytesAt_length]; omega_arith)
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range] at this ⊢
    rw [e, this]
  · simp only [VG.Proof.Bignum.bytesAt_length] at hi
    rw [e]; exact h.out (off + i) (by simp only [VG.Proof.Bignum.bytesAt_length]; omega_arith)

/-! ## Moving between the workspaces -/

/-- `SubCtx` but for `x0`: the memory and permissions of the inner workspace,
whichever workspace the code is in. -/
structure SubMem (t : State) (B : Addr) (Z o w wx : Nat) (minv : BitVec 64) : Prop where
  scr : Scr t B Z
  hdr : Hdr t.mem (off B o) wx minv
  link : word t.mem (off B o) (8 * Crt.sLink) = B
  nw : word t.mem B (8 * sW) = BitVec.ofNat 64 w
  narr : ∀ j < 8, word t.mem B (8 * sArr j) = off B (slot w j)
  lo : slot w 8 ≤ o
  hi : o + slot wx 8 + tabBytes wx ≤ Z

theorem _root_.VG.Proof.Bignum.AArch64.SubCtx.toMem {t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64}
    (h : SubCtx t B Z o w wx mi) : SubMem t B Z o w wx mi :=
  ⟨h.scr, h.hdr, h.link, h.nw, h.narr, h.lo, h.hi⟩

theorem SubMem.ctx {t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} (h : SubMem t B Z o w wx mi)
    (h0 : t.gpr .x0 = off B o) : SubCtx t B Z o w wx mi :=
  ⟨h.scr, h0, h.hdr, h.link, h.nw, h.narr, h.lo, h.hi⟩

theorem SubMem.congr {s t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} (h : SubMem s B Z o w wx mi)
    (hm : t.mem = s.mem) (hwr : t.wr = s.wr) : SubMem t B Z o w wx mi :=
  ⟨h.scr.congr hwr, by rw [hm]; exact h.hdr, by rw [hm]; exact h.link, by rw [hm]; exact h.nw,
    by rw [hm]; exact h.narr, h.lo, h.hi⟩

/-- `SubMem` after a change of the outer header's own slots. -/
theorem SubMem.of_parent {s t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} {rs : List (Nat × Nat)}
    (hc : SubMem s B Z o w wx mi) (hf : Frm B rs s.mem t.mem) (hr : ∀ r ∈ rs, 8 * 16 ≤ r.1 ∧ r.1 + r.2 ≤ 256)
    (hwr : t.wr = s.wr) : SubMem t B Z o w wx mi := by
  have hn := hc.scr.nowrap
  have hlo := hc.lo
  have hi := hc.hi
  have h256 : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_arith
  have hc' : ∀ d, o ≤ d → d + 8 ≤ Z → word t.mem B d = word s.mem B d := fun d h1 h2 =>
    hf.word_eq (fun r hr' => Or.inr (by have := hr r hr'; omega_arith)) (by omega_arith)
  have hp : ∀ i < 16, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    hf.word_eq (fun r hr' => Or.inl (by have := hr r hr'; omega_arith)) (by omega_arith)
  have hh : ∀ i < 32, word t.mem (off B o) (8 * i) = word s.mem (off B o) (8 * i) := fun i hi' => by
    rw [word_off, word_off]; exact hc' _ (by omega_arith) (by have := hdr_lt_slot wx 8 hi'; omega_arith)
  exact ⟨hc.scr.congr hwr,
    ⟨(hh _ (by decide)).trans hc.hdr.hw, (hh _ (by decide)).trans hc.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega_arith)).trans (hc.hdr.harr j hj)⟩,
    (hh _ (by decide)).trans hc.link, (hp _ (by decide)).trans hc.nw,
    fun j hj => (hp _ (by unfold sArr; omega_arith)).trans (hc.narr j hj), hc.lo, hc.hi⟩

/-- `SubCtx` after a change of the outer header's own slots. -/
theorem _root_.VG.Proof.Bignum.AArch64.SubCtx.of_parent {s t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64}
    {rs : List (Nat × Nat)} (hc : SubCtx s B Z o w wx mi) (hf : Frm B rs s.mem t.mem)
    (hr : ∀ r ∈ rs, 8 * 16 ≤ r.1 ∧ r.1 + r.2 ≤ 256) (hwr : t.wr = s.wr) (h0 : t.gpr .x0 = s.gpr .x0) :
    SubCtx t B Z o w wx mi :=
  (hc.toMem.of_parent hf hr hwr).ctx (h0.trans hc.x0)

/-- The outer workspace, from the inner one's memory. -/
theorem Outer.of_mem {t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} (hc : SubMem t B Z o w wx mi)
    (h0 : t.gpr .x0 = B) (hroom : inner w + slot w 8 + tabBytes32 w ≤ Z) (hw2 : 2 ≤ w) (hw : w < 2 ^ 28) :
    Outer t B Z w :=
  ⟨hc.scr, h0, hc.nw, hc.narr, hroom, hw2, hw⟩

/-- From the inner workspace, back to the outer one, and `x3 := domain_len − 2 p_len`. -/
theorem leaveQ_ok {t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} {dl k : Nat}
    (hc : SubCtx t B Z o w wx mi) (hdl : word t.mem B (8 * sDomLen) = BitVec.ofNat 64 dl)
    (hk : word t.mem B (8 * sK) = BitVec.ofNat 64 k) (hdk : 2 * k ≤ dl) :
    WP isa (.block (leave :: qTest)) t fun t' => (t'.gpr .x0 = B ∧ t'.gpr .x3 = BitVec.ofNat 64 (dl - 2 * k) ∧
      t'.mem = t.mem) ∧ Keep [.x0, .x3, .x4] t t' := by
  refine WP.keep [.x0, .x3, .x4] ?_ (by decide) (by decide) (by decide +kernel)
  unfold leave qTest
  brun [hc.x0, hdr_enc (show Crt.sLink < 32 by decide), hdr_enc (show sDomLen < 32 by decide),
    hdr_enc (show sK < 32 by decide), hc.ld' (show Crt.sLink < 32 by decide), off_off, hc.link',
    hc.ldn (show sDomLen < 32 by decide), hc.ldn (show sK < 32 by decide), hdl, hk]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- From the inner workspace, back to the outer one. -/
theorem leave_ok {t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} (hc : SubCtx t B Z o w wx mi) :
    WP isa (.block [leave]) t fun t' => (t'.gpr .x0 = B ∧ t'.mem = t.mem) ∧ Keep [.x0] t t' := by
  refine WP.keep [.x0] ?_ (by decide) (by decide) (by decide +kernel)
  unfold leave
  brun [hc.x0, hdr_enc (show Crt.sLink < 32 by decide), hc.ld' (show Crt.sLink < 32 by decide), off_off, hc.link']

/-- `-m⁻¹` of the same odd modulus is the same. -/
theorem xvals_minv {s t : State} {B : Addr} {o w : Nat} {mi₁ mi₂ : BitVec 64} {X : Nat} (hw : 1 ≤ w)
    (hodd : X % 2 = 1) (h₁ : XVals s B o w mi₁ X) (h₂ : XVals t B o w mi₂ X) : mi₁ = mi₂ := by
  have e : ∀ {u : State} {mi : BitVec 64}, XVals u B o w mi X → ((X % 2 ^ 64) * mi.toNat + 1) % 2 ^ 64 = 0 :=
    fun h => by have hi := h.inv; rwa [← wv_mod64 _ _ _ hw, h.n] at hi
  exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact hodd) (e h₁) (e h₂)

/-- Into the inner workspace. -/
theorem enter_ok {t : State} {B : Addr} {Z w : Nat} (h : Outer t B Z w)
    (hWs : word t.mem B (8 * sWs) = off B (inner w)) :
    WP isa (.block [enter]) t fun t' => (t'.gpr .x0 = off B (inner w) ∧ t'.mem = t.mem) ∧ Keep [.x0] t t' := by
  refine WP.keep [.x0] ?_ (by decide) (by decide) (by decide +kernel)
  unfold enter
  brun [h.x0, hdr_enc (show sWs < 32 by decide), h.ld (show sWs < 32 by decide), hWs]

/-- Return `r`. -/
theorem ret_ok (t : State) {r : Nat} (hr : r < 65536) :
    WP isa (VG.Impl.Ffdh.AArch64.Domain.ret r) t fun t' => (t'.gpr .x0 = BitVec.ofNat 64 r ∧ t'.mem = t.mem) ∧
      Keep [.x0] t t' := by
  refine WP.keep [.x0] ?_ (by unfold VG.Impl.Ffdh.AArch64.Domain.ret; cases r <;> rfl) rfl
    (by unfold VG.Impl.Ffdh.AArch64.Domain.ret; rfl)
  unfold VG.Impl.Ffdh.AArch64.Domain.ret movi
  brun
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

theorem setWidth32_bit (p : Prop) [Decidable p] :
    ((if p then (1 : BitVec 64) else 0).setWidth 32).toNat = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

theorem setWidth32_ofNat {r : Nat} (hr : r < 2 ^ 32) : ((BitVec.ofNat 64 r).setWidth 32).toNat = r := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_arith

/-- A branch on a register holding 0 or 1. -/
theorem wp_ite_bit {th el : Prog isa} {s : State} {Q : State → Prop} {r : Reg} {P : Prop} [Decidable P]
    (h : s.gpr r = if P then 1 else 0) (ht : ¬ P → WP isa th s Q) (he : P → WP isa el s Q) :
    WP isa (.ite (.zero .x r) th el) s Q := by
  refine WP.ite (!decide P) (by rw [VG.Proof.MlKem.AArch64.eval_zero, h]; by_cases hp : P <;> simp [hp]) (fun hb => ?_)
    (fun hb => ?_)
  · exact ht (by simpa using hb)
  · exact he (by simpa using hb)

/-- A branch on a register holding a Boolean's 0 or 1. -/
theorem wp_ite_bool {th el : Prog isa} {s : State} {Q : State → Prop} {r : Reg} {b : Bool}
    (h : s.gpr r = BitVec.ofNat 64 b.toNat) (ht : b = false → WP isa th s Q) (he : b = true → WP isa el s Q) :
    WP isa (.ite (.zero .x r) th el) s Q := by
  refine WP.ite (!b) (by rw [VG.Proof.MlKem.AArch64.eval_zero, h]; cases b <;> rfl) (fun hb => ?_) (fun hb => ?_)
  · exact ht (by simpa using hb)
  · exact he (by simpa using hb)

/-- `XVals` after a change of the outer header's own slots. -/
theorem _root_.VG.Proof.Bignum.AArch64.XVals.of_parent {s t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} {X : Nat}
    {rs : List (Nat × Nat)} (hc : SubMem s B Z o w wx mi) (h : XVals s B o wx mi X) (hf : Frm B rs s.mem t.mem)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ 256) : XVals t B o wx mi X := by
  have hn := hc.scr.nowrap
  have hlo := hc.lo
  have hi := hc.hi
  have h256 : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_arith
  have sN := slot_le (w := wx) (show aN < 8 by decide)
  have sO := slot_le (w := wx) (show aOne < 8 by decide)
  have e : ∀ d k, d + 8 * k ≤ slot wx 8 → wv t.mem (off B o) d k = wv s.mem (off B o) d k := fun d k hd =>
    wv_congr fun i hi' => by
      rw [word_off, word_off]
      exact hf.word_eq (fun r hr' => Or.inr (by have := hr r hr'; omega_arith)) (by omega_arith)
  refine ⟨by rw [e _ _ (by omega_arith)]; exact h.n, ?_, by rw [e _ _ (by omega_arith)]; exact h.one⟩
  rw [word_off, hf.word_eq (fun r hr' => Or.inr (by have := hr r hr'; omega_arith)) (by omega_arith), ← word_off]
  exact h.inv

/-! ## A power compared with 1 -/

/-- `pow` then `isOne aY`: `x9 := b^e mod X = 1`. -/
theorem powOne_ok (W : Window) (M : Mont) (S : Selector) {s : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64}
    {X : Nat} (hc : ModCtx s B Z o w mi X)
    {bp bl ep el : Nat} (hbp : bp < 32) (hbl : bl < 32) (hep : ep < 32) (hel : el < 32)
    {pb pe : Addr} {bb eb : List Byte}
    (hpb : word s.mem B (8 * bp) = pb) (hlb : word s.mem B (8 * bl) = BitVec.ofNat 64 bb.length)
    (hsb : Src s B Z pb bb) (hb1 : 1 ≤ bb.length) (hb2 : (bb.length + 7) / 8 ≤ w)
    (hpe : word s.mem B (8 * ep) = pe) (hle : word s.mem B (8 * el) = BitVec.ofNat 64 eb.length)
    (hse : Src s B Z pe eb) (he1 : 1 ≤ eb.length) (he2 : eb.length ≤ 1024) :
    WP isa (seqs (pow W.code S.code M.mm bp bl ep el ++ isOne aY)) s fun t => ModCtx t B Z o w mi X ∧
      t.gpr .x9 = bit (Spec.Rsa.os2ip bb ^ Spec.Rsa.os2ip eb % X = 1) ∧
      Frm (off B o) (powRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine wp_seqs_append (by simp [pow, loadArr]) (by simp [isOne, eqArr]) (WP.mono (pow_ok W M S hc hbp hbl hep hel
    hpb hlb hsb hb1 hb2 hpe hle hse he1 he2) fun t₁ ⟨hc₁, hY, f₁, k₁⟩ => ?_)
  have hw2 := hc₁.w2
  have hw28 := hc₁.w28
  refine WP.mono (eqArr_ok hc₁.sub.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (show aY < 8 by decide)
    (show aOne < 8 by decide)) fun t ⟨h9, hm, k⟩ => ?_
  have hc' : ModCtx t B Z o w mi X := by
    obtain ⟨hs, hv, r2l, r2, hodd, hx1, hwide, -, -⟩ := hc₁
    have hn := hs.good.scr.nowrap
    have e : ∀ d n, wv t.mem (off B o) d n = wv t₁.mem (off B o) d n := fun d n => by rw [hm]
    exact ⟨⟨hs.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hs.x0, by rw [hm]; exact hs.hdr,
      by rw [hm]; exact hs.link, by rw [hm]; exact hs.nw, by rw [hm]; exact hs.narr, hs.lo, hs.hi⟩,
      ⟨by rw [e]; exact hv.n, by rw [hm]; exact hv.inv, by rw [e]; exact hv.one⟩,
      by rw [e]; exact r2l, by rw [e]; exact r2, hodd, hx1, hwide, hw2, hw28⟩
  refine ⟨hc', by rw [h9, hY, hc₁.xv.one], by rw [hm]; exact f₁, keep_trans k₁ k⟩

/-! ## Slices of sources -/

theorem _root_.VG.Proof.Bignum.AArch64.Src.take {t : State} {B : Addr} {Z : Nat} {ptr : Addr} {bs : List Byte}
    (h : Src t B Z ptr bs) (n : Nat) : Src t B Z ptr (bs.take n) :=
  ⟨fun i hi => h.rd i (by simp at hi; omega_arith), fun i hi => by rw [List.getElem_take]; exact h.val i _,
    fun i hi => h.out i (by simp at hi; omega_arith)⟩

theorem _root_.VG.Proof.Bignum.AArch64.Src.drop {t : State} {B : Addr} {Z : Nat} {ptr : Addr} {bs : List Byte}
    (h : Src t B Z ptr bs) (n : Nat) : Src t B Z (ptr + BitVec.ofNat 64 n) (bs.drop n) := by
  have e : ∀ i, ptr + BitVec.ofNat 64 n + BitVec.ofNat 64 i = ptr + BitVec.ofNat 64 (n + i) := fun i => by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [e]; exact h.rd _ (by simp at hi; omega_arith)
  · rw [e, List.getElem_drop]; exact h.val _ _
  · rw [e]; exact h.out _ (by simp at hi; omega_arith)

end VG.Proof.Ffdh.AArch64
