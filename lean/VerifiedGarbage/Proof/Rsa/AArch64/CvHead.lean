import VerifiedGarbage.Proof.Rsa.AArch64.Inv

/-!
# `vg_rsa_crt_values` on AArch64: the arguments and the head

`CvArgs`: the arguments `entry` leaves in the header, kept by the pieces
(`CvArgs.congr`). `cvHead_ok`: `head` sets up the working space (`Ws`) for
`w = ⌈k / 8⌉` and the mask all ones.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.Keys.CrtValues
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The arguments in the header: the outputs' pointers, `n`'s pointer and
length, and `p`'s, `q`'s and `d`'s pointers and lengths. -/
structure CvArgs (m : Mem) (B : Addr) (k pl ql dl : Nat) (pDp pDq pQi pN pP pQ pD : Addr) : Prop where
  dp : word m B (8 * sDp) = pDp
  dq : word m B (8 * sDq) = pDq
  qi : word m B (8 * sQi) = pQi
  n : word m B (8 * Public.sN) = pN
  k : word m B (8 * Public.sK) = BitVec.ofNat 64 k
  p : word m B (8 * sP) = pP
  pl : word m B (8 * sPl) = BitVec.ofNat 64 pl
  q : word m B (8 * sQ) = pQ
  ql : word m B (8 * sQl) = BitVec.ofNat 64 ql
  d : word m B (8 * sD) = pD
  dl : word m B (8 * sDl) = BitVec.ofNat 64 dl

/-- The header slots of `CvArgs`. -/
def argSlot (i : Nat) : Prop := (16 ≤ i ∧ i < 22) ∨ (23 ≤ i ∧ i < 28)

theorem CvArgs.congr {m m' : Mem} {B : Addr} {k pl ql dl : Nat} {pDp pDq pQi pN pP pQ pD : Addr}
    (h : CvArgs m B k pl ql dl pDp pDq pQi pN pP pQ pD)
    (hm : ∀ i, argSlot i → word m' B (8 * i) = word m B (8 * i)) :
    CvArgs m' B k pl ql dl pDp pDq pQi pN pP pQ pD :=
  ⟨(hm _ (by simp [argSlot, sDp, sFn])).trans h.dp, (hm _ (by simp [argSlot, sDq, sFn])).trans h.dq,
    (hm _ (by simp [argSlot, sQi, sFn])).trans h.qi,
    (hm _ (by simp [argSlot, Public.sN, sFn])).trans h.n,
    (hm _ (by simp [argSlot, Public.sK, sFn])).trans h.k,
    (hm _ (by simp [argSlot, sP, sFn])).trans h.p, (hm _ (by simp [argSlot, sPl, sFn])).trans h.pl,
    (hm _ (by simp [argSlot, sQ, sFn])).trans h.q, (hm _ (by simp [argSlot, sQl, sFn])).trans h.ql,
    (hm _ (by simp [argSlot, sD, sFn])).trans h.d, (hm _ (by simp [argSlot, sDl, sFn])).trans h.dl⟩

/-- The argument slots, after code that changes only ranges that `Mut`
allows. -/
theorem argSlot_frm {m m' : Mem} {B : Addr} {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (hr : ∀ r ∈ rs, Mut r) :
    ∀ i, argSlot i → word m' B (8 * i) = word m B (8 * i) := fun i hi => by
  unfold argSlot at hi
  exact hf.word_eq (fun r hr' => by
    rcases hr r hr' with h | rfl
    · omega
    · simp only [Public.sMask, sFn]; omega) (by omega)

/-- The words of `w = ⌈k / 8⌉` for `64 ≤ k ≤ 1024`. -/
abbrev wk (k : Nat) : Nat := (k + 7) / 8

/-- `head`: `w`, the arrays' bases, the stride, and the mask all ones. -/
theorem cvHead_ok {s : State} {B : Addr} {Z k : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hk1 : 64 ≤ k)
    (hk2 : k ≤ 1024) (hZ : 128 * k ≤ Z) (hK : word s.mem B (8 * Public.sK) = BitVec.ofNat 64 k) :
    WP isa (.block VG.Impl.Rsa.AArch64.Keys.head) s fun t =>
      Ws t B Z (wk k) ∧ word t.mem B (8 * Public.sMask) = mask true ∧
      Frm B [(8 * sW, 8), (8 * sArr 0, 64), (8 * sStride, 8), (8 * Public.sMask, 8)] s.mem t.mem ∧
      Keep [.x3, .x4, .x7, .x12] s t := by
  have hn := hs.nowrap
  have hZ16 : slot (wk k) 16 ≤ Z := by simp only [slot, hdrBytes, wk]; omega
  have h8 := hdr_lt_slot (wk k) 8 (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have eM : Public.sMask = 22 := rfl
  have hl8 : slot (wk k) 8 ≤ slot (wk k) 16 := by unfold slot; omega
  unfold VG.Impl.Rsa.AArch64.Keys.head
  rw [WP.block_append_iff]
  refine WP.mono (head_ok hs h0 (by simp only [slot, hdrBytes]; omega) (by omega) hK) fun t₁ ⟨h12, hW₁, hb₁, hf₁, k₁⟩ => ?_
  have hs₁ := hs.congr k₁.wr
  have h0₁ : t₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h0
  refine WP.mono (WP.keep [.x3, .x4, .x7] (Q := fun t => t.gpr .x7 = 0 ∧ t.mem = (t₁.mem.writeW (off B (8 * sStride))
      (BitVec.ofNat 64 (8 * (wk k + 2)))).writeW (off B (8 * Public.sMask)) (mask true)) (by
    brun [h0₁, h12, hdr_enc (show sStride < 32 by decide), hdr_enc (show Public.sMask < 32 by decide),
      hs₁.st (d := 8 * sStride) (by omega), hs₁.st (d := 8 * Public.sMask) (by omega),
      ofNat_add_ofNat, shl_ofNat (show ((k + 7) / 8 + 2) * 2 ^ 3 < 2 ^ 64 by omega)]
    rw [show ((k + 7) / 8 + 2) * 2 ^ 3 = 8 * (wk k + 2) by simp only [wk]; omega]
    rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨_, hm⟩, k₂⟩ => ?_
  have o1 := writeW_outside t₁.mem B (BitVec.ofNat 64 (8 * (wk k + 2))) (d := 8 * sStride) (by omega)
  have o2 := writeW_outside (t₁.mem.writeW (off B (8 * sStride)) (BitVec.ofNat 64 (8 * (wk k + 2)))) B (mask true)
    (d := 8 * Public.sMask) (by omega)
  have hw : ∀ i < 32, i ≠ sStride → i ≠ Public.sMask → word t.mem B (8 * i) = word t₁.mem B (8 * i) :=
    fun i hi h1 h2 => by rw [hm, o2.word (by omega) (by omega), o1.word (by omega) (by omega)]
  refine ⟨⟨hs₁.congr k₂.wr, (k₂.gpr .x0 (by decide)).trans h0₁, ?_, ?_, fun j hj => ?_, hZ16, show 2 ≤ (k + 7) / 8 by omega,
    show (k + 7) / 8 < 2 ^ 24 by omega⟩, by rw [hm, word_writeW_self], ?_, (k₁.trans k₂).mono (by simp)⟩
  · rw [hw sW (by decide) (by decide) (by decide)]; exact hW₁
  · rw [hm, o2.word (by omega) (by omega), word_writeW_self]
  · rw [hw (sArr j) (by unfold sArr; omega) (by unfold sArr sStride sFn; omega)
      (by unfold sArr Public.sMask sFn; omega)]
    exact hb₁ j hj
  · intro x hx
    have a := hx (8 * sW, 8) (by simp)
    have b := hx (8 * sArr 0, 64) (by simp)
    have c := hx (8 * sStride, 8) (by simp)
    have d := hx (8 * Public.sMask, 8) (by simp)
    dsimp only at a b c d
    rw [hm, o2 x d, o1 x c, hf₁ x (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> with_reducible assumption)]

end VG.Proof.Rsa.AArch64
