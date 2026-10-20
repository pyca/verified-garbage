module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Pow
public import VerifiedGarbage.Proof.Ffdh.X86_64.Checks
public import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# FFDH on X86_64: the front of the domain operations

From the outer header with the domain's pointer and p's length: the check of
p (`domHead_ok`); the outer workspace and the inner one for p, with p, `-p⁻¹`
and the number 1 (`setup_ok`); `R² mod p` (`r2_ctx`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt (wsEnd wsNew loadArr leave)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- Header slots of the outer workspace with given values. -/
def Slots (m : Mem) (B : Addr) (L : List (Nat × BitVec 64)) : Prop := ∀ p ∈ L, word m B (8 * p.1) = p.2

theorem Slots.frm {m m' : Mem} {B : Addr} {L : List (Nat × BitVec 64)} {rs : List (Nat × Nat)} (h : Slots m B L)
    (hf : Frm B rs m m') (hr : ∀ p ∈ L, ∀ r ∈ rs, 8 * p.1 + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * p.1)
    (hL : ∀ p ∈ L, p.1 < 32) : Slots m' B L := fun p hp => by
  rw [hf.word_eq (hr p hp) (by have := hL p hp; omega_arith)]; exact h p hp

def setupR (w : Nat) : List (Nat × Nat) := [(8 * sW, 8), (8 * sArr 0, 64), (8 * sWs, 8), (inner w, slot w 8)]

theorem wsWords_k {k : Nat} (hk : 16 ≤ k) : wsWords k = (k + 7) / 8 := by unfold wsWords; omega_arith

/-- The workspaces' room in the working space of `16 k + 32` words. -/
theorem room_k {k Z : Nat} (hk : 64 ≤ k) (hZ : 128 * k + 256 ≤ Z) :
    inner ((k + 7) / 8) + slot ((k + 7) / 8) 8 + tabBytes ((k + 7) / 8) 32 ≤ Z := by
  simp only [inner, slot, hdrBytes, tabBytes]
  generalize hw : (k + 7) / 8 = w
  have h8 : 8 * w ≤ k + 7 := by omega_arith
  have e : 256 + 8 * (8 * (w + 2)) + (256 + 8 * (8 * (w + 2))) + 32 * (8 * (w + 2)) = 384 * w + 1280 := by omega_arith
  rw [e]
  omega_arith

/-- The outer workspace, once back from the inner one. -/
theorem Outer.of_sub {t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} (hc : SubCtx t B Z o w wx mi)
    (h0 : t.gpr .rdi = B) (hroom : inner w + slot w 8 + tabBytes w 32 ≤ Z) (hw2 : 2 ≤ w) (hw : w < 2 ^ 28) :
    Outer t B Z w :=
  ⟨hc.scr, h0, hc.nw, hc.narr, hroom, hw2, hw⟩

/-- Initialize the outer workspace using RSA's existing header routine. -/
theorem head_ok {s : State} {B : Addr} {Z k : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk : k < 2 ^ 32)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) :
    WP isa (.block VG.Impl.Rsa.X86_64.head) s fun t => t.gpr .r12 = BitVec.ofNat 64 ((k + 7) / 8) ∧
      word t.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) ∧
      (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)) ∧
      Frm B [(8 * sW, 8), (8 * sArr 0, 64)] s.mem t.mem ∧ Keep mmRegs s t :=
by
  have h := VG.Proof.Bignum.X86_64.setupHead_ok hs hdi hZ hk hK rfl
  change WP isa (.block VG.Impl.Rsa.X86_64.head) s _ at h
  exact WP.mono h fun _ ⟨h12, _, _, _, hW, hA, f, k⟩ =>
    ⟨h12, hW, hA, f, k.mono (by decide)⟩

/-- `head`, then the inner workspace for p, entered, with p, `-p⁻¹` and the
number 1. -/
theorem setup_ok {s : State} {B : Addr} {Z k : Nat} {dp : Addr} {pb : List Byte} (hs : Scr s B Z)
    (h0 : s.gpr .rdi = B) (hk1 : 64 ≤ k) (hk2 : k ≤ 1024) (hZ : 128 * k + 256 ≤ Z)
    (hD : word s.mem B (8 * sDom) = dp) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hsrc : Src s B Z dp pb) (hl : pb.length = k) (hodd : Spec.Rsa.os2ip pb % 2 = 1) :
    WP isa (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)) s fun t => ∃ mi,
      SubCtx t B Z (inner ((k + 7) / 8)) ((k + 7) / 8) ((k + 7) / 8) mi ∧
      XVals t B (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip pb) ∧
      word t.mem B (8 * sWs) = off B (inner ((k + 7) / 8)) ∧
      Frm B (setupR ((k + 7) / 8)) s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  have hn := hs.nowrap
  have hroom := room_k hk1 hZ
  have eW : wsWords k = (k + 7) / 8 := wsWords_k (by omega_arith)
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have eW6 : sW = 6 := rfl
  have eA8 : sArr 0 = 8 := rfl
  have eWs : sWs = 29 := rfl
  have hi8 : 8 * 32 ≤ inner ((k + 7) / 8) := by simp only [inner, slot, hdrBytes]; omega_arith
  have hiZ : inner ((k + 7) / 8) + slot ((k + 7) / 8) 8 ≤ Z := by unfold tabBytes at hroom; omega_arith
  refine wp_seqs_cons (by simp [pSetup]) (WP.mono (head_ok hs h0 (by unfold inner at hroom; omega_arith) (by omega_arith) hK)
    fun s₁ ⟨h12, hW, hA, f₁, k₁⟩ => ?_)
  have hO : Outer s₁ B Z ((k + 7) / 8) :=
    ⟨hs.congr k₁.2.2, (k₁.gpr (by decide)).trans h0, hW, hA, hroom, by omega_arith, by omega_arith⟩
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
  refine wp_seqs_append (a := wsSetup sK ++ [.block [enter]]) (b := modSetup sDom sK) (by simp [wsSetup]) (by simp [modSetup, loadArr]) (WP.mono (wsSetup_ok (sl := sK) (len := k) hO (by decide) (by decide)
    (by rw [hK₁]) (by omega_arith) (by omega_arith)) fun s₂ ⟨hc₂, _, hWs₂, f₂, k₂⟩ => ?_)
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

theorem _root_.VG.Proof.Bignum.X86_64.SubCtx.toMem {t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64}
    (h : SubCtx t B Z o w wx mi) : SubMem t B Z o w wx mi :=
  ⟨h.scr, h.hdr, h.link, h.nw, h.narr, h.lo, h.hi⟩

theorem SubMem.ctx {t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} (h : SubMem t B Z o w wx mi)
    (h0 : t.gpr .rdi = off B o) : SubCtx t B Z o w wx mi :=
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
theorem _root_.VG.Proof.Bignum.X86_64.SubCtx.of_parent {s t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64}
    {rs : List (Nat × Nat)} (hc : SubCtx s B Z o w wx mi) (hf : Frm B rs s.mem t.mem)
    (hr : ∀ r ∈ rs, 8 * 16 ≤ r.1 ∧ r.1 + r.2 ≤ 256) (hwr : t.wr = s.wr) (h0 : t.gpr .rdi = s.gpr .rdi) :
    SubCtx t B Z o w wx mi :=
  (hc.toMem.of_parent hf hr hwr).ctx (h0.trans hc.rdi)

/-- The outer workspace, from the inner one's memory. -/
theorem Outer.of_mem {t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} (hc : SubMem t B Z o w wx mi)
    (h0 : t.gpr .rdi = B) (hroom : inner w + slot w 8 + tabBytes w 32 ≤ Z) (hw2 : 2 ≤ w) (hw : w < 2 ^ 28) :
    Outer t B Z w :=
  ⟨hc.scr, h0, hc.nw, hc.narr, hroom, hw2, hw⟩

/-- Changes inside the child workspace preserve its memory layout even while
the caller uses the outer workspace's base register. -/
theorem SubMem.of_child {s t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64}
    {rs : List (Nat × Nat)} (h : SubMem s B Z o w wx mi) (hf : Frm (off B o) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8) (hwr : t.wr = s.wr) :
    SubMem t B Z o w wx mi := by
  have hn := h.scr.nowrap
  have hi := h.hi
  have hL : o + slot wx 8 ≤ 2 ^ 64 := by omega
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have hh : ∀ i < 17, word t.mem (off B o) (8 * i) = word s.mem (off B o) (8 * i) := fun i hi' =>
    hf.word_eq (fun r hr' => Or.inl (by have := hr r hr'; omega)) (by omega)
  have hb : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    hf.word_below (fun r hr' => (hr r hr').2) hL (by omega)
      (by have := hdr_lt_slot w 8 hi'; have := h.lo; omega)
  exact ⟨h.scr.congr hwr,
    ⟨(hh _ (by decide)).trans h.hdr.hw, (hh _ (by decide)).trans h.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega)).trans (h.hdr.harr j hj)⟩,
    (hh _ (by decide)).trans h.link, (hb _ (by decide)).trans h.nw,
    fun j hj => (hb _ (by unfold sArr; omega)).trans (h.narr j hj), h.lo, h.hi⟩

/-- `-m⁻¹` of the same odd modulus is the same. -/
theorem xvals_minv {s t : State} {B : Addr} {o w : Nat} {mi₁ mi₂ : BitVec 64} {X : Nat} (hw : 1 ≤ w)
    (hodd : X % 2 = 1) (h₁ : XVals s B o w mi₁ X) (h₂ : XVals t B o w mi₂ X) : mi₁ = mi₂ := by
  have e : ∀ {u : State} {mi : BitVec 64}, XVals u B o w mi X → ((X % 2 ^ 64) * mi.toNat + 1) % 2 ^ 64 = 0 :=
    fun h => by have hi := h.inv; rwa [← wv_mod64 _ _ _ hw, h.n] at hi
  exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact hodd) (e h₁) (e h₂)

/-- `XVals` after a change of the outer header's own slots. -/
theorem _root_.VG.Proof.Bignum.X86_64.XVals.of_parent {s t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} {X : Nat}
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
theorem powOne_ok (M : Mont) (E : CrtExpL M) {s : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64}
    {X : Nat} (hc : ModCtx s B Z o w mi X)
    {bp bl ep el : Nat} (hbp : bp < 32) (hbl : bl < 32) (hep : ep < 32) (hel : el < 32)
    {pb pe : Addr} {bb eb : List Byte}
    (hpb : word s.mem B (8 * bp) = pb) (hlb : word s.mem B (8 * bl) = BitVec.ofNat 64 bb.length)
    (hsb : Src s B Z pb bb) (hb1 : 1 ≤ bb.length) (hb2 : (bb.length + 7) / 8 ≤ w)
    (hpe : word s.mem B (8 * ep) = pe) (hle : word s.mem B (8 * el) = BitVec.ofNat 64 eb.length)
    (hse : Src s B Z pe eb) (he1 : 1 ≤ eb.length) (he2 : eb.length ≤ 1024) :
    WP isa (seqs (pow M.mm E.code bp bl ep el ++ isOne aY)) s fun t => ModCtx t B Z o w mi X ∧
      t.gpr .rax = bit (Spec.Rsa.os2ip bb ^ Spec.Rsa.os2ip eb % X = 1) ∧
      Frm (off B o) (powRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine wp_seqs_append (by simp [pow, loadArr]) (by simp [isOne, eqArr]) (WP.mono (pow_ok M E hc hbp hbl hep hel
    hpb hlb hsb hb1 hb2 hpe hle hse he1 he2) fun t₁ ⟨hc₁, hY, f₁, k₁⟩ => ?_)
  have hw2 := hc₁.w2
  have hw28 := hc₁.w28
  refine WP.mono (eqArr_ok hc₁.sub.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (show aY < 8 by decide)
    (show aOne < 8 by decide)) fun t ⟨h9, hm, k⟩ => ?_
  have hc' : ModCtx t B Z o w mi X := by
    obtain ⟨hs, hv, r2l, r2, hodd, hx1, hwide, -, -⟩ := hc₁
    have hn := hs.good.scr.nowrap
    have e : ∀ d n, wv t.mem (off B o) d n = wv t₁.mem (off B o) d n := fun d n => by rw [hm]
    exact ⟨⟨hs.scr.congr k.2.2, (k.gpr (by decide)).trans hs.rdi, by rw [hm]; exact hs.hdr,
      by rw [hm]; exact hs.link, by rw [hm]; exact hs.nw, by rw [hm]; exact hs.narr, hs.lo, hs.hi⟩,
      ⟨by rw [e]; exact hv.n, by rw [hm]; exact hv.inv, by rw [e]; exact hv.one⟩,
      by rw [e]; exact r2l, by rw [e]; exact r2, hodd, hx1, hwide, hw2, hw28⟩
  refine ⟨hc', by rw [h9, hY, hc₁.xv.one], by rw [hm]; exact f₁, keep_trans k₁ k⟩

/-! ## Slices of sources -/

theorem _root_.VG.Proof.Bignum.X86_64.Src.take {t : State} {B : Addr} {Z : Nat} {ptr : Addr} {bs : List Byte}
    (h : Src t B Z ptr bs) (n : Nat) : Src t B Z ptr (bs.take n) :=
  ⟨fun i hi => h.rd i (by simp at hi; omega_arith), fun i hi => by rw [List.getElem_take]; exact h.val i _,
    fun i hi => h.out i (by simp at hi; omega_arith)⟩

theorem _root_.VG.Proof.Bignum.X86_64.Src.drop {t : State} {B : Addr} {Z : Nat} {ptr : Addr} {bs : List Byte}
    (h : Src t B Z ptr bs) (n : Nat) : Src t B Z (ptr + BitVec.ofNat 64 n) (bs.drop n) := by
  have e : ∀ i, ptr + BitVec.ofNat 64 n + BitVec.ofNat 64 i = ptr + BitVec.ofNat 64 (n + i) := fun i => by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [e]; exact h.rd _ (by simp at hi; omega_arith)
  · rw [e, List.getElem_drop]; exact h.val _ _
  · rw [e]; exact h.out _ (by simp at hi; omega_arith)

end VG.Proof.Ffdh.X86_64
