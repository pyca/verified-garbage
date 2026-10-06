import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup

/-!
# `vg_rsa_crt_values` on x86-64: the arguments and the head

`CvArgs`: the arguments `entry` leaves in the header, kept by the pieces
(`CvArgs.congr`). `cvHead_ok`: `head` sets up the working space (`Ws`) for
`w = ⌈k / 8⌉` and the mask all ones.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The arguments in the header: the outputs' pointers, `n`'s pointer and
length, `p`'s, `q`'s and `d`'s pointers and lengths, and the saved
registers `sv`. -/
structure CvArgs (m : Mem) (B : Addr) (k pl ql dl : Nat) (pDp pDq pQi pN pP pQ pD : Addr)
    (sv : Nat → BitVec 64) : Prop where
  dp : word m B (8 * sDp) = pDp
  dq : word m B (8 * sDq) = pDq
  qi : word m B (8 * sQi) = pQi
  n : word m B (8 * Impl.Bignum.X86_64.Public.sN) = pN
  k : word m B (8 * Impl.Bignum.X86_64.Public.sK) = BitVec.ofNat 64 k
  p : word m B (8 * sP) = pP
  pl : word m B (8 * sPl) = BitVec.ofNat 64 pl
  q : word m B (8 * sQ) = pQ
  ql : word m B (8 * sQl) = BitVec.ofNat 64 ql
  d : word m B (8 * sD) = pD
  dl : word m B (8 * sDl) = BitVec.ofNat 64 dl
  saved : ∀ i < 6, word m B (8 * i) = sv i

/-- The header slots of `CvArgs`. -/
def argSlot (i : Nat) : Prop := i < 6 ∨ (16 ≤ i ∧ i < 22) ∨ (23 ≤ i ∧ i < 28)

theorem CvArgs.congr {m m' : Mem} {B : Addr} {k pl ql dl : Nat} {pDp pDq pQi pN pP pQ pD : Addr}
    {sv : Nat → BitVec 64} (h : CvArgs m B k pl ql dl pDp pDq pQi pN pP pQ pD sv)
    (hm : ∀ i, argSlot i → word m' B (8 * i) = word m B (8 * i)) :
    CvArgs m' B k pl ql dl pDp pDq pQi pN pP pQ pD sv :=
  ⟨(hm _ (by simp [argSlot, sDp, sFn])).trans h.dp, (hm _ (by simp [argSlot, sDq, sFn])).trans h.dq,
    (hm _ (by simp [argSlot, sQi, sFn])).trans h.qi,
    (hm _ (by simp [argSlot, Impl.Bignum.X86_64.Public.sN, sFn])).trans h.n,
    (hm _ (by simp [argSlot, Impl.Bignum.X86_64.Public.sK, sFn])).trans h.k,
    (hm _ (by simp [argSlot, sP, sFn])).trans h.p, (hm _ (by simp [argSlot, sPl, sFn])).trans h.pl,
    (hm _ (by simp [argSlot, sQ, sFn])).trans h.q, (hm _ (by simp [argSlot, sQl, sFn])).trans h.ql,
    (hm _ (by simp [argSlot, sD, sFn])).trans h.d, (hm _ (by simp [argSlot, sDl, sFn])).trans h.dl,
    fun i hi => (hm i (Or.inl hi)).trans (h.saved i hi)⟩

/-- The argument slots, after code that changes only ranges that `Mut`
allows. -/
theorem argSlot_frm {m m' : Mem} {B : Addr} {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (hr : ∀ r ∈ rs, Mut r) :
    ∀ i, argSlot i → word m' B (8 * i) = word m B (8 * i) := fun i hi => by
  unfold argSlot at hi
  exact hf.word_eq (fun r hr' => by
    rcases hr r hr' with h | rfl | rfl
    · omega
    · simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega
    · simp only [sMo, sFn]; omega) (by omega)

/-- The words of `w = ⌈k / 8⌉` for `64 ≤ k ≤ 1024`. -/
abbrev wk (k : Nat) : Nat := (k + 7) / 8

/-- `head`: `w`, the arrays' bases, the stride, and the mask all ones. -/
theorem cvHead_ok {s : State} {B : Addr} {Z k : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hk1 : 64 ≤ k)
    (hk2 : k ≤ 1024) (hZ : 128 * k ≤ Z) (hK : word s.mem B (8 * Impl.Bignum.X86_64.Public.sK) = BitVec.ofNat 64 k) :
    WP isa (.block head) s fun t =>
      Ws t B Z (wk k) ∧ word t.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = mask true ∧
      Frm B [(8 * sW, 8), (8 * sArr 0, 64), (8 * sStride, 8), (8 * Impl.Bignum.X86_64.Public.sMask, 8)]
        s.mem t.mem ∧ Keep [.rax, .rcx, .rdx, .r12] s t := by
  have hn := hs.nowrap
  have hZ16 : slot (wk k) 16 ≤ Z := by simp only [slot, hdrBytes, wk]; omega
  have h8 := hdr_lt_slot (wk k) 8 (show 31 < 32 by decide)
  have eK : Impl.Bignum.X86_64.Public.sK = 18 := rfl
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have hl8 : slot (wk k) 8 ≤ slot (wk k) 16 := by unfold slot; omega
  unfold head
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx, .r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (wk k) ∧
      t.mem = s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 (wk k))) ?_ rfl)
    fun t₁ ⟨⟨h12, hm₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * Impl.Bignum.X86_64.Public.sK) (by omega),
      hs.st (d := 8 * sW) (by omega), hK, shr3_w k (by omega)]
  have hs₁ := hs.congr k₁.2.2
  refine WP.mono (setBases_ok hs₁ ((k₁.gpr (by decide)).trans hdi) h12 (by unfold sArr; omega))
    fun t₂ ⟨hb₂, ho₂, k₂⟩ => ?_
  have hs₂ := hs₁.congr k₂.2.2
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi)
  have h12₂ : t₂.gpr .r12 = BitVec.ofNat 64 (wk k) := (k₂.gpr (by decide)).trans h12
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = (t₂.mem.writeW (off B (8 * sStride))
      (BitVec.ofNat 64 (8 * (wk k + 2)))).writeW (off B (8 * Impl.Bignum.X86_64.Public.sMask)) (mask true)) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, h12₂, hs₂.st (d := 8 * sStride) (by omega),
      hs₂.st (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by omega), ofNat_dbl]
    congr 2
    rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add, ofNat_dbl, ofNat_dbl, ofNat_dbl]
    congr 1; omega) rfl) fun t ⟨hm, k₃⟩ => ?_
  have o1 := writeW_outside t₂.mem B (BitVec.ofNat 64 (8 * (wk k + 2))) (d := 8 * sStride) (by omega)
  have o2 := writeW_outside (t₂.mem.writeW (off B (8 * sStride)) (BitVec.ofNat 64 (8 * (wk k + 2)))) B (mask true)
    (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by omega)
  have hw : ∀ i < 32, i ≠ sStride → i ≠ Impl.Bignum.X86_64.Public.sMask → word t.mem B (8 * i) = word t₂.mem B (8 * i) :=
    fun i hi h1 h2 => by rw [hm, o2.word (by omega) (by omega), o1.word (by omega) (by omega)]
  have kk := ((k₁.trans k₂).trans k₃)
  refine ⟨⟨hs₂.congr k₃.2.2, (k₃.gpr (by decide)).trans hdi₂, ?_, ?_, fun j hj => ?_, hZ16, by unfold wk; omega,
    by unfold wk; omega⟩, by rw [hm, word_writeW_self], ?_, kk.mono (by simp)⟩
  · rw [hw sW (by decide) (by decide) (by decide), ho₂.word (by omega) (by omega), hm₁, word_writeW_self]
  · rw [hm, o2.word (by omega) (by omega), word_writeW_self]
  · rw [hw (sArr j) (by unfold sArr; omega) (by unfold sArr sStride sFn; omega)
      (by unfold sArr Impl.Bignum.X86_64.Public.sMask sFn; omega)]
    exact hb₂ j hj
  · intro x hx
    have a := hx (8 * sW, 8) (by simp)
    have b := hx (8 * sArr 0, 64) (by simp)
    have c := hx (8 * sStride, 8) (by simp)
    have d := hx (8 * Impl.Bignum.X86_64.Public.sMask, 8) (by simp)
    dsimp only at a b c d
    rw [hm, o2 x d, o1 x c, ho₂ x b, hm₁, writeW_outside s.mem B _ (by omega) x a]

end VG.Proof.Rsa.X86_64
