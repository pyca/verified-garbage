import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.CrtHdr

/-!
# RSA with the CRT on AArch64: up to the checks

From the header `entry` leaves, for a valid modulus: the modulus' setup (as
`vg_rsa_public`'s, then `c R mod n`), the primes' workspaces and the checks
(`front_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- `nSetup` after `pcLoad`: the input `c` into `X`, the mask of `c < n`
and the number 1. -/
def nInput : List (Prog isa) := [
  .block [ldh .x1 Public.sIn, ldh .x2 Public.sK, ldh .x8 (sArr Public.aX)],
  loadBE,
  .block [ldh .x12 sW, ldh .x16 (sArr Public.aX), ldh .x17 (sArr Public.aN), movi .x7 0, mov .x14 .x12,
    .subs .x .x3 .x7 .x7],
  cmpLoop,
  .block (borrowMask ++ [sth .x15 Public.sMask, ldh .x12 sW, movi .x9 1, movi .x13 0]),
  setWord Public.aOne]

theorem nSetup_eq (M : Mont) : nSetup M.mm =
    pcLoad ++ (nInput ++ (r2Steps M.mm ++ [M.mm Public.aXm Public.aX Public.aR2])) := rfl

/-- `nInput`: `c` into `X`, the mask of `c < n` into `sMask`, and 1. -/
theorem nInput_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64} {ip : Addr} {xb : List Byte} {N : Nat}
    (hg : Good s B Z ((k + 7) / 8) minv) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 64 ≤ k) (hk2 : k ≤ 1024)
    (hK : word s.mem B (8 * Public.sK) = BitVec.ofNat 64 k) (hIn : word s.mem B (8 * Public.sIn) = ip)
    (hx : Src s B Z ip xb) (hxl : xb.length = k)
    (hN : wv s.mem B (slot ((k + 7) / 8) Public.aN) ((k + 7) / 8) = N) :
    WP isa (seqs nInput) s fun t => Good t B Z ((k + 7) / 8) minv ∧
      wv t.mem B (slot ((k + 7) / 8) Public.aX) ((k + 7) / 8) = Spec.Rsa.os2ip xb ∧
      wv t.mem B (slot ((k + 7) / 8) Public.aOne) ((k + 7) / 8) = 1 ∧
      word t.mem B (8 * Public.sMask) = mask (decide (Spec.Rsa.os2ip xb < N)) ∧
      Frm B [(slot ((k + 7) / 8) Public.aX, 8 * ((k + 7) / 8 + 2)), (8 * Public.sMask, 8),
        (slot ((k + 7) / 8) Public.aOne, 8 * ((k + 7) / 8 + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have lX := slot_le (w := (k + 7) / 8) (show Public.aX < 8 by decide)
  have lN := slot_le (w := (k + 7) / 8) (show Public.aN < 8 by decide)
  have lO := slot_le (w := (k + 7) / 8) (show Public.aOne < 8 by decide)
  have sXN := slot_sep (w := (k + 7) / 8) (show Public.aX ≠ Public.aN by decide)
  have sXO := slot_sep (w := (k + 7) / 8) (show Public.aX ≠ Public.aOne by decide)
  have hX0 := hdr_lt_slot ((k + 7) / 8) Public.aX (show 31 < 32 by decide)
  have hO0 := hdr_lt_slot ((k + 7) / 8) Public.aOne (show 31 < 32 by decide)
  have eM : Public.sMask = 22 := rfl
  have eW : sW = 6 := rfl
  have eMi : sMinv = 7 := rfl
  simp only [nInput, seqs]
  -- `c` into `X`.
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x8] (Q := fun t => t.gpr .x1 = ip ∧ t.gpr .x2 = BitVec.ofNat 64 k ∧
      t.gpr .x8 = off B (slot ((k + 7) / 8) Public.aX) ∧ t.mem = s.mem)
    (by brun [hg.x0, hdr_enc (show Public.sIn < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
      hdr_enc (sArr_lt (show Public.aX < 8 by decide)), hg.ld hZ (show Public.sIn < 32 by decide),
      hg.ld hZ (show Public.sK < 32 by decide), hg.ld hZ (sArr_lt (show Public.aX < 8 by decide)), hIn, hK,
      hg.hdr.harr Public.aX (by decide)]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h1, h2, h8', hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  refine WP.seq (WP.mono (loadArr_ok hs₁ (show Public.aX < 8 by decide) hZ
    (hx.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁) hxl (by omega_arith) (by omega_arith) h1 h2 h8')
    fun s₂ ⟨hX₂, ha₂, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.wr
  have h0₂ : s₂.gpr .x0 = B := ((k₁.trans k₂).gpr .x0 (by decide)).trans hg.x0
  have hH₂ : Hdr s₂.mem B ((k + 7) / 8) minv :=
    ⟨by rw [ha₂.hslot (by decide), hm₁]; exact hg.hdr.hw, by rw [ha₂.hslot (by decide), hm₁]; exact hg.hdr.hminv,
      fun j hj => by rw [ha₂.hslot (sArr_lt hj), hm₁]; exact hg.hdr.harr j hj⟩
  have hN₂ : wv s₂.mem B (slot ((k + 7) / 8) Public.aN) ((k + 7) / 8) = N := by
    rw [ha₂.wv_of_not_mem (by decide) (by decide) (by omega_arith), hm₁]; exact hN
  -- `c < n`.
  refine WP.seq (WP.mono (WP.keep [.x3, .x7, .x12, .x14, .x16, .x17] (Q := fun t =>
      t.gpr .x12 = BitVec.ofNat 64 ((k + 7) / 8) ∧ t.gpr .x16 = off B (slot ((k + 7) / 8) Public.aX) ∧
      t.gpr .x17 = off B (slot ((k + 7) / 8) Public.aN) ∧ t.gpr .x7 = 0 ∧
      t.gpr .x14 = BitVec.ofNat 64 ((k + 7) / 8) ∧ t.c = true ∧ t.mem = s₂.mem)
    (by brun [h0₂, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt (show Public.aX < 8 by decide)),
      hdr_enc (sArr_lt (show Public.aN < 8 by decide)), hs₂.ld (show 8 * sW + 8 ≤ Z by
        have := hdr_lt_slot ((k + 7) / 8) 8 (show sW < 32 by decide); omega_arith),
      hs₂.ld (show 8 * sArr Public.aX + 8 ≤ Z by
        have := hdr_lt_slot ((k + 7) / 8) 8 (sArr_lt (show Public.aX < 8 by decide)); omega_arith),
      hs₂.ld (show 8 * sArr Public.aN + 8 ≤ Z by
        have := hdr_lt_slot ((k + 7) / 8) 8 (sArr_lt (show Public.aN < 8 by decide)); omega_arith),
      hH₂.hw, hH₂.harr Public.aX (by decide), hH₂.harr Public.aN (by decide)])
    (by decide) (by decide) (by decide +kernel))
    fun s₃ ⟨⟨h12, h16, h17, h7, h14, hc, hm₃⟩, k₃⟩ => ?_)
  refine WP.seq (WP.mono (cmpLoop_ok (hs₂.congr k₃.wr) h16 h17 h14 hc (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₄ ⟨hc₄, hm₄, k₄⟩ => ?_)
  rw [hm₃, hX₂, hN₂] at hc₄
  have k24 := k₃.trans k₄
  have h0₄ : s₄.gpr .x0 = B := (k24.gpr .x0 (by decide)).trans h0₂
  have h7₄ : s₄.gpr .x7 = 0 := (k₄.gpr .x7 (by decide)).trans h7
  have hs₄ := hs₂.congr k24.wr
  have hm₂₄ : s₄.mem = s₂.mem := hm₄.trans hm₃
  have hW' : ∀ v : BitVec 64, word (s₄.mem.writeW (off B (8 * Public.sMask)) v) B (8 * sW) =
      BitVec.ofNat 64 ((k + 7) / 8) := fun v => by
    rw [(writeW_outside s₄.mem B v (by omega_arith)).word (by rw [eM]; unfold sW; omega_arith) (by omega_arith), hm₂₄]
    exact hH₂.hw
  -- The mask, and the operands of `setWord`.
  refine WP.seq (WP.mono (WP.keep [.x4, .x9, .x12, .x13, .x15] (Q := fun t =>
      t.mem = s₄.mem.writeW (off B (8 * Public.sMask)) (mask (!s₄.c)) ∧
      t.gpr .x12 = BitVec.ofNat 64 ((k + 7) / 8) ∧ (t.gpr .x9).toNat = 1 ∧ t.gpr .x13 = BitVec.ofNat 64 0)
    (by brun [borrowMask, h0₄, h7₄, hdr_enc (show Public.sMask < 32 by decide), hdr_enc (show sW < 32 by decide),
      hs₄.st (show 8 * Public.sMask + 8 ≤ Z by rw [eM]; omega_arith),
      hs₄.ld (show 8 * sW + 8 ≤ Z by have := hdr_lt_slot ((k + 7) / 8) 8 (show sW < 32 by decide); omega_arith), hW']; cases s₄.c <;> rfl)
    (by decide) (by decide) (by decide +kernel))
    fun s₅ ⟨⟨hm₅, h12₅, h9₅, h13₅⟩, k₅⟩ => ?_)
  have hwo₅ : Outside B (8 * Public.sMask) 8 s₄.mem s₅.mem := by
    rw [hm₅]; exact writeW_outside _ B _ (by omega_arith)
  have hH₅ : Hdr s₅.mem B ((k + 7) / 8) minv := by
    have : ∀ i < 16, word s₅.mem B (8 * i) = word s₂.mem B (8 * i) := fun i hi => by
      rw [hwo₅.word (by rw [eM]; omega_arith) (by omega_arith), hm₂₄]
    exact ⟨(this _ (by decide)).trans hH₂.hw, (this _ (by decide)).trans hH₂.hminv,
      fun j hj => (this _ (by unfold sArr; omega_arith)).trans (hH₂.harr j hj)⟩
  have k25 := k24.trans k₅
  have hs₅ := hs₂.congr k25.wr
  refine WP.mono (setWord_ok hs₅ ((k₅.gpr .x0 (by decide)).trans h0₄) hH₅ hZ h12₅ (by omega_arith) (o := Public.aOne)
    (by decide) (i := 0) (by omega_arith) h13₅) fun t ⟨hone, ho, k₆⟩ => ?_
  have hO : Outside B (slot ((k + 7) / 8) Public.aOne) (8 * ((k + 7) / 8 + 2)) s₅.mem t.mem := ho
  refine ⟨⟨hs.congr ((k₁.trans k₂).trans (k25.trans k₆)).wr,
      (k₆.gpr .x0 (by decide)).trans ((k₅.gpr .x0 (by decide)).trans h0₄), ?_⟩, ?_, ?_, ?_, ?_,
    (((k₁.trans k₂).trans (k25.trans k₆))).mono (by decide)⟩
  · exact ⟨by rw [hO.word (by omega_arith) (by omega_arith)]; exact hH₅.hw,
      by rw [hO.word (by omega_arith) (by omega_arith)]; exact hH₅.hminv,
      fun j hj => by
        have := sArr_lt hj
        rw [hO.word (d := 8 * sArr j) (by have := hdr_lt_slot ((k + 7) / 8) Public.aOne (sArr_lt hj); omega_arith)
          (by omega_arith)]; exact hH₅.harr j hj⟩
  · rw [hO.wv (by omega_arith) (by omega_arith), hwo₅.wv (by omega_arith) (by omega_arith), hm₂₄]; exact hX₂
  · rw [hone, h9₅]
  · rw [hO.word (by omega_arith) (by omega_arith), hm₅, word_writeW_self, hc₄, Bool.not_not]
  · have g2 : Frm B [(slot ((k + 7) / 8) Public.aX, 8 * ((k + 7) / 8 + 2)), (8 * Public.sMask, 8),
        (slot ((k + 7) / 8) Public.aOne, 8 * ((k + 7) / 8 + 2))] s.mem s₂.mem := by
      rw [← hm₁]; exact Frm.of_arrays1 ha₂ (by simp)
    rw [← hm₂₄] at g2
    exact (g2.trans (Frm.of_outside hwo₅ (by simp))).trans (Frm.of_outside hO (by simp))

/-- What `main` starts from: the working space at `B` (its base in `x0`)
holding all three workspaces, the header `entry` leaves, and the byte
strings outside the working space. -/
structure CrtPre (s : State) (B : Addr) (Z k : Nat) (op np ip pp qp dpp dqp qip : Addr) (pl ql : Nat)
    (nb xb pb qb dpb dqb qib : List Byte) : Prop where
  scr : Scr s B Z
  x0 : s.gpr .x0 = B
  z : offQ ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes (wsWords ql) ≤ Z
  zk : 128 * k ≤ Z
  k1 : 64 ≤ k
  k2 : k ≤ 1024
  hO : word s.mem B (8 * Public.sOut) = op
  hN : word s.mem B (8 * Public.sN) = np
  hK : word s.mem B (8 * Public.sK) = BitVec.ofNat 64 k
  hIn : word s.mem B (8 * Public.sIn) = ip
  hP : word s.mem B (8 * sP) = pp
  hPl : word s.mem B (8 * sPlen) = BitVec.ofNat 64 pl
  hQ : word s.mem B (8 * sQ) = qp
  hQl : word s.mem B (8 * sQlen) = BitVec.ofNat 64 ql
  hDp : word s.mem B (8 * sDp) = dpp
  hDq : word s.mem B (8 * sDq) = dqp
  hQi : word s.mem B (8 * sQinv) = qip
  n : Src s B Z np nb
  x : Src s B Z ip xb
  p : Src s B Z pp pb
  q : Src s B Z qp qb
  dp : Src s B Z dpp dpb
  dq : Src s B Z dqp dqb
  qi : Src s B Z qip qib
  nl : nb.length = k
  xl : xb.length = k
  pbl : pb.length = pl
  qbl : qb.length = ql
  dpl : dpb.length = pl
  dql : dqb.length = ql
  qil : qib.length = pl
  pl1 : 1 ≤ pl
  pl2 : pl < k
  ql1 : 1 ≤ ql
  ql2 : ql < k
  out : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1
  outSep : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)

/-- After the checks: the three workspaces, the modulus' values, the mask
`M` and the primes `M ? p : 3`, `M ? q : 3`. -/
structure CrtReady (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N C P Q : Nat)
    (M : Bool) : Prop where
  good : Good t B Z w minv
  nv : NVals t B w minv N
  xm : wv t.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N
  msk : word t.mem B (8 * Public.sMask) = mask M
  wsP : word t.mem B (8 * sWsP) = off B (offP w)
  wsQ : word t.mem B (8 * sWsQ) = off B (offQ w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  pxv : XVals t B (offP w) (wsWords pl) mp (if M then P else 3)
  pmask : word t.mem (off B (offP w)) (8 * sMaskX) = mask M
  qws : WsAt t.mem B (offQ w pl) (wsWords ql) mq
  qxv : XVals t B (offQ w pl) (wsWords ql) mq (if M then Q else 3)
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : Keep mmRegs s t

/-- After `n`'s setup: its values, `c R mod n` and the mask of `c < n`. -/
structure NReady (s t : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N C : Nat) : Prop where
  good : Good t B Z w minv
  nv : NVals t B w minv N
  xm : wv t.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N
  msk : word t.mem B (8 * Public.sMask) = mask (decide (C < N))
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : Keep mmRegs s t

/-- `n`'s setup, for a valid modulus. -/
theorem nPart_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    WP isa (seqs (nSetup M.mm)) s fun t => ∃ minv,
      NReady s t B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) := by
  obtain ⟨hodd, hN1, hlo⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hn := h.scr.nowrap
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega_arith
  have hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega_arith
  have hZs : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, r.1 + r.2 ≤ slot ((k + 7) / 8) 8) → ∀ r ∈ rs, r.1 + r.2 ≤ Z :=
    fun h' r hr => (h' r hr).trans hZ
  have lN := slot_le (w := (k + 7) / 8) (show Public.aN < 8 by decide)
  have lX := slot_le (w := (k + 7) / 8) (show Public.aX < 8 by decide)
  have lO := slot_le (w := (k + 7) / 8) (show Public.aOne < 8 by decide)
  have sNX := slot_sep (w := (k + 7) / 8) (show Public.aN ≠ Public.aX by decide)
  have sNO := slot_sep (w := (k + 7) / 8) (show Public.aN ≠ Public.aOne by decide)
  have hN0 := hdr_lt_slot ((k + 7) / 8) Public.aN (show 31 < 32 by decide)
  rw [nSetup_eq]
  -- The modulus and `-n⁻¹`.
  refine wp_seqs_append (by simp [pcLoad]) (by simp [nInput])
    (WP.mono (pcLoad_ok h.scr h.x0 hZ (by omega_arith) (by omega_arith) h.hK h.hN h.n h.nl hodd)
      fun t₁ ⟨minv, hg₁, hn₁, hi₁, f₁, k₁⟩ => ?_)
  have f₁' : Frm B (setupRanges ((k + 7) / 8)) s.mem t₁.mem :=
    f₁.mono (by simp [pcLoadRanges, setupRanges, loadRanges])
  have hh₁ := HFix.of_frm f₁' (keepsHdr_setupRanges _)
  -- The input, the mask of `c < n` and 1.
  refine wp_seqs_append (by simp [nInput]) (by simp [r2Steps])
    (WP.mono (nInput_ok hg₁ hZ hk1 hk2 (by rw [hh₁ _ (by decide) (by decide)]; exact h.hK)
      (by rw [hh₁ _ (by decide) (by decide)]; exact h.hIn)
      (h.x.congrK (InScr.of_frm f₁' (hZs (setupRanges_le _))) k₁) h.xl hn₁)
      fun t₂ ⟨hg₂, hX₂, hO₂, hM₂, f₂, k₂⟩ => ?_)
  have hN₂ : wv t₂.mem B (slot ((k + 7) / 8) Public.aN) ((k + 7) / 8) = Spec.Rsa.os2ip nb := by
    rw [f₂.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [Public.sMask, sFn] <;> omega_arith) (by omega_arith)]; exact hn₁
  have hI₂ : ((word t₂.mem B (slot ((k + 7) / 8) Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [f₂.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [Public.sMask, sFn] <;> omega_arith) (by omega_arith)]; exact hi₁
  have f₂' : Frm B (setupRanges ((k + 7) / 8)) t₁.mem t₂.mem := f₂.mono (by simp [setupRanges, loadRanges])
  -- `R² mod n`.
  refine wp_seqs_append (by simp [r2Steps]) (by simp)
    (WP.mono (r2_ok M hg₂ hZ (by omega_arith) (by omega_arith) hN₂ hI₂ hodd hlo)
      fun t₃ ⟨hg₃, hlt₃, hr₃, f₃, k₃⟩ => ?_)
  have hX₃ : wv t₃.mem B (slot ((k + 7) / 8) Public.aX) ((k + 7) / 8) = Spec.Rsa.os2ip xb := by
    rw [f₃.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact hX₂
  have hN₃ : wv t₃.mem B (slot ((k + 7) / 8) Public.aN) ((k + 7) / 8) = Spec.Rsa.os2ip nb := by
    rw [f₃.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact hN₂
  have hI₃ : ((word t₃.mem B (slot ((k + 7) / 8) Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [f₃.r2_word hn' (by decide) (by decide) (by decide) (by decide)]; exact hI₂
  have hO₃ : wv t₃.mem B (slot ((k + 7) / 8) Public.aOne) ((k + 7) / 8) = 1 := by
    rw [f₃.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact hO₂
  -- `c R mod n`.
  simp only [seqs]
  refine WP.mono (crtMmN_ok M hg₃ hZ (by omega_arith) (by omega_arith) (o := Public.aXm) (a := Public.aX) (b := Public.aR2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hN₃ hI₃ hlt₃)
    fun t₄ ⟨hg₄, hN₄, hI₄, hlt₄, hm₄, ha₄, k₄⟩ => ?_
  have hR : Nat.Coprime (2 ^ (64 * ((k + 7) / 8))) (Spec.Rsa.os2ip nb) := VG.Proof.Bignum.coprime_pow2 hodd _
  have hxm₄ : wv t₄.mem B (slot ((k + 7) / 8) Public.aXm) ((k + 7) / 8) % Spec.Rsa.os2ip nb =
      Spec.Rsa.os2ip xb * 2 ^ (64 * ((k + 7) / 8)) % Spec.Rsa.os2ip nb := by
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₄, hX₃, Nat.mul_mod, hr₃, ← Nat.mul_mod, Nat.mul_assoc]
  have g₄ : Frm B [(slot ((k + 7) / 8) Public.aAcc, 8 * ((k + 7) / 8 + 2)),
      (slot ((k + 7) / 8) Public.aTmp, 8 * ((k + 7) / 8 + 2)),
      (slot ((k + 7) / 8) Public.aXm, 8 * ((k + 7) / 8 + 2))] t₃.mem t₄.mem :=
    Frm.of_arrays ha₄ fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> simp
  have kg₄ : ∀ r ∈ [(slot ((k + 7) / 8) Public.aAcc, 8 * ((k + 7) / 8 + 2)),
      (slot ((k + 7) / 8) Public.aTmp, 8 * ((k + 7) / 8 + 2)),
      (slot ((k + 7) / 8) Public.aXm, 8 * ((k + 7) / 8 + 2))], KeepsHdr r ∧ r.1 + r.2 ≤ slot ((k + 7) / 8) 8 := by
    have := hdr_lt_slot ((k + 7) / 8) Public.aAcc (show 31 < 32 by decide)
    have := hdr_lt_slot ((k + 7) / 8) Public.aTmp (show 31 < 32 by decide)
    have := hdr_lt_slot ((k + 7) / 8) Public.aXm (show 31 < 32 by decide)
    have := slot_le (w := (k + 7) / 8) (show Public.aAcc < 8 by decide)
    have := slot_le (w := (k + 7) / 8) (show Public.aTmp < 8 by decide)
    have := slot_le (w := (k + 7) / 8) (show Public.aXm < 8 by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl) <;> exact ⟨keepsHdr_ge (by simp only; omega_arith), by simp only; omega_arith⟩
  have e3 : word t₃.mem B (8 * Public.sMask) = word t₂.mem B (8 * Public.sMask) :=
    f₃.word_eq (r2Ranges_hdr _ (by decide) (by decide)) (by unfold Public.sMask sFn; omega_arith)
  exact ⟨minv, hg₄,
    ⟨hN₄, hI₄, by rw [ha₄.wv_of_not_mem (by decide) (by decide) hn']; exact hr₃,
      by rw [ha₄.wv_of_not_mem (by decide) (by decide) hn']; exact hlt₃,
      by rw [ha₄.wv_of_not_mem (by decide) (by decide) hn']; exact hO₃⟩, hxm₄,
    by rw [ha₄.hslot (by decide), e3]; exact hM₂,
    ((hh₁.trans (HFix.of_frm f₂' (keepsHdr_setupRanges _))).trans (HFix.of_frm f₃ (keepsHdr_r2Ranges _))).trans
      (HFix.of_frm g₄ fun r hr => (kg₄ r hr).1),
    (((InScr.of_frm f₁' (hZs (setupRanges_le _))).trans (InScr.of_frm f₂' (hZs (setupRanges_le _)))).trans
      (InScr.of_frm f₃ (hZs (r2Ranges_le _)))).trans (InScr.of_frm g₄ (hZs fun r hr => (kg₄ r hr).2)),
    (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩

/-- After the primes' workspaces: `n`'s values as before, the workspaces,
`p`, `q` and `qInv`. -/
structure PReady (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N C P Q QI : Nat) : Prop
    where
  n : NReady s t B Z w minv N C
  wsP : word t.mem B (8 * sWsP) = off B (offP w)
  wsQ : word t.mem B (8 * sWsQ) = off B (offQ w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  qws : WsAt t.mem B (offQ w pl) (wsWords ql) mq
  pv : wv t.mem (off B (offP w)) (slot (wsWords pl) Public.aN) (wsWords pl) = P
  qiv : wv t.mem (off B (offP w)) (slot (wsWords pl) aChunk) (wsWords pl) = QI
  qv : wv t.mem (off B (offQ w pl)) (slot (wsWords ql) Public.aN) (wsWords ql) = Q

/-- The primes' workspaces, from `n`'s setup. -/
theorem setupPart_ok {s t₃ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv : BitVec 64}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hr : NReady s t₃ B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)) :
    WP isa (seqs primesSetup) t₃ fun t => ∃ mp mq, PReady s t B Z ((k + 7) / 8) pl ql minv mp mq
      (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hn := h.scr.nowrap
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega_arith
  have hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega_arith
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega_arith
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hh₃ : ∀ i < 32, hFixed i = true → word t₃.mem B (8 * i) = word s.mem B (8 * i) := hr.hfix
  refine WP.mono (primesSetup_ok hr.good (by omega_arith) (by omega_arith) hZq
    (by rw [hh₃ _ (by decide) (by decide)]; exact h.hPl) (by rw [hh₃ _ (by decide) (by decide)]; exact h.hQl)
    (by rw [hh₃ _ (by decide) (by decide)]; exact h.hP) (by rw [hh₃ _ (by decide) (by decide)]; exact h.hQ)
    (by rw [hh₃ _ (by decide) (by decide)]; exact h.hQi) (h.p.congrK hr.iscr hr.keep) (h.q.congrK hr.iscr hr.keep)
    (h.qi.congrK hr.iscr hr.keep) h.pbl h.qbl h.qil h.pl1 (by have := h.pl2; omega_arith) h.ql1 (by have := h.ql2; omega_arith))
    fun t₄ ⟨hg₄, hsP₄, hsQ₄, ⟨mp, hwp₄⟩, ⟨mq, hwq₄⟩, hp₄, hc₄, hq₄, f₄, k₄⟩ => ?_
  have kf₄ : ∀ r ∈ [(8 * sWsP, 8), (8 * sWsQ, 8), (offP ((k + 7) / 8), slot (wsWords pl) 8 + tabBytes (wsWords pl) + slot (wsWords ql) 8)],
      KeepsHdr r ∧ r.1 + r.2 ≤ Z ∧ (slot ((k + 7) / 8) 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * 31) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl)
    · exact ⟨keepsHdr_slot (by decide) (by decide), by simp only [sWsP, sFn]; omega_arith,
        Or.inr (by simp only [sWsP, sFn]; omega_arith)⟩
    · exact ⟨keepsHdr_slot (by decide) (by decide), by simp only [sWsQ, sFn]; omega_arith,
        Or.inr (by simp only [sWsQ, sFn]; omega_arith)⟩
    · exact ⟨keepsHdr_ge (by simp only [offP]; omega_arith), by simp only [offP]; unfold offQ at hZq; omega_arith,
        Or.inl (by simp only [offP]; omega_arith)⟩
  have hnv₄ : ∀ j < 8, wv t₄.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) =
      wv t₃.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) := fun j hj =>
    f₄.wv_eq (fun r hr => by
      have := kf₄ r hr
      have := slot_le (w := (k + 7) / 8) hj
      have := hdr_lt_slot ((k + 7) / 8) j (show 31 < 32 by decide)
      omega) (by have := slot_le (w := (k + 7) / 8) hj; omega)
  have hnw₄ : word t₄.mem B (slot ((k + 7) / 8) Public.aN) = word t₃.mem B (slot ((k + 7) / 8) Public.aN) :=
    f₄.word_eq (fun r hr => by
      have := kf₄ r hr
      have := slot_le (w := (k + 7) / 8) (show Public.aN < 8 by decide)
      have := hdr_lt_slot ((k + 7) / 8) Public.aN (show 31 < 32 by decide)
      omega) (by have := slot_le (w := (k + 7) / 8) (show Public.aN < 8 by decide); omega)
  have hM₄ : word t₄.mem B (8 * Public.sMask) = word t₃.mem B (8 * Public.sMask) := by
    refine f₄.word_eq (fun r hr => ?_) (by unfold Public.sMask sFn; omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Or.inl (by simp only [Public.sMask, sWsP, sFn]; omega_arith)
    · exact Or.inl (by simp only [Public.sMask, sWsQ, sFn]; omega_arith)
    · exact Or.inl (by simp only [offP, Public.sMask, sFn]; omega_arith)
  refine ⟨mp, mq, ⟨hg₄, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, hsP₄, hsQ₄, hwp₄, hwq₄, hp₄, hc₄, hq₄⟩
  · rw [hnv₄ _ (by decide)]; exact hr.nv.n
  · rw [hnw₄]; exact hr.nv.inv
  · rw [hnv₄ _ (by decide)]; exact hr.nv.r2
  · rw [hnv₄ _ (by decide)]; exact hr.nv.r2lt
  · rw [hnv₄ _ (by decide)]; exact hr.nv.one
  · rw [hnv₄ _ (by decide)]; exact hr.xm
  · rw [hM₄]; exact hr.msk
  · exact hr.hfix.trans (HFix.of_frm f₄ fun r hr => (kf₄ r hr).1)
  · exact hr.iscr.trans (InScr.of_frm f₄ fun r hr => (kf₄ r hr).2.1)
  · exact (hr.keep.trans k₄).mono (by decide)

/-- The checks, from the primes' workspaces. -/
theorem checksPart_ok {s t₄ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : PReady s t₄ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs checks) t₄ fun t => ∃ mp' mq',
      CrtReady s t B Z ((k + 7) / 8) pl ql minv mp' mq' (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
        (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) := by
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hn := h.scr.nowrap
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega_arith
  have hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega_arith
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega_arith
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega_arith
  have hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega_arith
  refine WP.mono (checks_ok hr.n.good (by omega_arith) (by omega_arith) (le_refl _) (by unfold offQ; omega_arith)
    (by unfold offQ at hZq ⊢; omega_arith) hwp2 (wsWords_le (by have := h.pl2; omega_arith) (by omega_arith)) hwq2
    (wsWords_le (by have := h.ql2; omega_arith) (by omega_arith)) hr.wsP hr.wsQ hr.pws hr.qws hr.n.nv.n hr.n.msk hr.pv hr.qv
    hr.qiv hodd)
    fun t ⟨hg, hMt, hsPt, hsQt, ⟨mp', hwpt, hxpt, hmpt⟩, ⟨mq', hwqt, hxqt⟩, f₅, k₅⟩ => ?_
  have kf₅ : ∀ r ∈ [(slot ((k + 7) / 8) Public.aAcc, 8 * (2 * ((k + 7) / 8) + 2)), (8 * Public.sMask, 8),
      (offP ((k + 7) / 8), slot (wsWords pl) 8), (offQ ((k + 7) / 8) pl, slot (wsWords ql) 8)],
      KeepsHdr r ∧ r.1 + r.2 ≤ Z := by
    have := accs_le ((k + 7) / 8)
    have := hdr_lt_slot ((k + 7) / 8) Public.aAcc (show 31 < 32 by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl)
    · exact ⟨keepsHdr_ge (by simp only; omega_arith), by simp only; omega_arith⟩
    · exact ⟨keepsHdr_slot (by decide) (by decide), by simp only [Public.sMask, sFn]; omega_arith⟩
    · exact ⟨keepsHdr_ge (by simp only [offP]; omega_arith), by simp only [offP]; unfold offQ at hZq; omega_arith⟩
    · exact ⟨keepsHdr_ge (by simp only [offQ]; omega_arith), by simp only; omega_arith⟩
  have hnv₅ : ∀ j < 8, j ≠ Public.aAcc → j ≠ Public.aTmp → wv t.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) =
      wv t₄.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) := fun j hj h1 h2 => by
    have := slot_le (w := (k + 7) / 8) hj
    have := hdr_lt_slot ((k + 7) / 8) j (show 31 < 32 by decide)
    have := accs_le ((k + 7) / 8)
    have : slot ((k + 7) / 8) j + 8 * ((k + 7) / 8) ≤ slot ((k + 7) / 8) Public.aAcc ∨
        slot ((k + 7) / 8) Public.aAcc + 8 * (2 * ((k + 7) / 8) + 2) ≤ slot ((k + 7) / 8) j := by
      unfold slot Public.aAcc
      rw [show Public.aAcc = 2 from rfl] at h1
      rw [show Public.aTmp = 3 from rfl] at h2
      rcases (show j < 2 ∨ 4 ≤ j by omega_arith) with hj' | hj'
      · left; have := Nat.mul_le_mul_right (8 * ((k + 7) / 8 + 2)) (show j + 1 ≤ 2 by omega_arith)
        rw [Nat.add_mul, Nat.one_mul] at this; omega_arith
      · right; have := Nat.mul_le_mul_right (8 * ((k + 7) / 8 + 2)) (show 4 ≤ j by omega_arith); omega_arith
    refine f₅.wv_eq (fun r hr => ?_) (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp only; omega_arith
    · exact Or.inr (by simp only [Public.sMask, sFn]; omega_arith)
    · exact Or.inl (by simp only; omega_arith)
    · exact Or.inl (by simp only [offQ]; omega_arith)
  refine ⟨mp', mq', hg, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, hMt, hsPt, hsQt, hwpt, hxpt, hmpt, hwqt, hxqt, ?_, ?_,
    (hr.n.keep.trans k₅).mono (by decide)⟩
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.nv.n
  · have := accs_le ((k + 7) / 8)
    have := slot_le (w := (k + 7) / 8) (show Public.aN < 8 by decide)
    have hN0 := hdr_lt_slot ((k + 7) / 8) Public.aN (show 31 < 32 by decide)
    rw [f₅.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have : slot ((k + 7) / 8) Public.aN + 8 ≤ slot ((k + 7) / 8) Public.aAcc := by
        unfold slot Public.aN Public.aAcc; omega_arith
      rcases hr with rfl | rfl | rfl | rfl
      · exact Or.inl (by simp only; omega_arith)
      · exact Or.inr (by simp only [Public.sMask, sFn]; omega_arith)
      · exact Or.inl (by simp only; omega_arith)
      · exact Or.inl (by simp only [offQ]; omega_arith)) (by omega_arith)]
    exact hr.n.nv.inv
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.nv.r2
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.nv.r2lt
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.nv.one
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.xm
  · exact hr.n.hfix.trans (HFix.of_frm f₅ fun r hr => (kf₅ r hr).1)
  · exact hr.n.iscr.trans (InScr.of_frm f₅ fun r hr => (kf₅ r hr).2)

/-- Up to the checks, for a valid modulus. -/
theorem front_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    WP isa (seqs (nSetup M.mm ++ primesSetup ++ checks)) s fun t => ∃ minv mp mq,
      CrtReady s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
        (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :=
  wp_seqs_append (by simp [nSetup]) (by simp [checks]) (wp_seqs_append (by simp [nSetup])
    (by simp [primesSetup]) (WP.mono (nPart_ok M h hv) fun _ ⟨minv, hr⟩ =>
      WP.mono (setupPart_ok h hr) fun _ ⟨_, _, hr'⟩ =>
        WP.mono (checksPart_ok h hv hr') fun _ ⟨mp', mq', hr''⟩ => ⟨minv, mp', mq', hr''⟩))

end VG.Proof.Bignum.AArch64
