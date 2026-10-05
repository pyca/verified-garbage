import VerifiedGarbage.Proof.Bignum.X86_64.PcVerified
import VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.CrtP
import Mathlib.Data.Int.GCD

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtFront`. -/
section

/-!
# RSA with the CRT on x86-64: up to the checks

From the header `entry` leaves, for a valid modulus: the modulus' setup (as
`vg_rsa_public`'s, then `c R mod n`), the primes' workspaces and the checks
(`front_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- What `main` starts from: the working space at `B` (its base in `rdi`)
holding all three workspaces, the header `entry` leaves, and the byte
strings outside the working space. -/
structure CrtPre (s : State) (B : Addr) (Z k : Nat) (op np ip pp qp dpp dqp qip : Addr) (pl ql : Nat)
    (nb xb pb qb dpb dqb qib : List Byte) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr s B Z
  rdi : s.gpr .rdi = B
  z : offQ ((k + 7) / 8) pl + VG.Proof.Bignum.X86_64.slot (wsWords ql) 8 + tabBytes (wsWords ql) ≤ Z
  zk : 128 * k ≤ Z
  k1 : 64 ≤ k
  k2 : k ≤ 1024
  hO : VG.Proof.Bignum.X86_64.word s.mem B (8 * Public.sOut) = op
  hN : VG.Proof.Bignum.X86_64.word s.mem B (8 * Public.sN) = np
  hK : VG.Proof.Bignum.X86_64.word s.mem B (8 * Public.sK) = BitVec.ofNat 64 k
  hIn : VG.Proof.Bignum.X86_64.word s.mem B (8 * Public.sIn) = ip
  hP : VG.Proof.Bignum.X86_64.word s.mem B (8 * sP) = pp
  hPl : VG.Proof.Bignum.X86_64.word s.mem B (8 * sPlen) = BitVec.ofNat 64 pl
  hQ : VG.Proof.Bignum.X86_64.word s.mem B (8 * sQ) = qp
  hQl : VG.Proof.Bignum.X86_64.word s.mem B (8 * sQlen) = BitVec.ofNat 64 ql
  hDp : VG.Proof.Bignum.X86_64.word s.mem B (8 * sDp) = dpp
  hDq : VG.Proof.Bignum.X86_64.word s.mem B (8 * sDq) = dqp
  hQi : VG.Proof.Bignum.X86_64.word s.mem B (8 * sQinv) = qip
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
  outSep : ∀ j < k, Z ≤ VG.Proof.Bignum.X86_64.ofs B (op + BitVec.ofNat 64 j)

/-- After the checks: the three workspaces, the modulus' values, the mask
`M` and the primes `M ? p : 3`, `M ? q : 3`. -/
structure CrtReady (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N C P Q : Nat)
    (M : Bool) : Prop where
  good : VG.Proof.Bignum.X86_64.Good t B Z w minv
  nv : NVals t B w minv N
  xm : wv t.mem B (VG.Proof.Bignum.X86_64.slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N
  msk : VG.Proof.Bignum.X86_64.word t.mem B (8 * Public.sMask) = VG.Proof.Bignum.X86_64.mask M
  wsP : VG.Proof.Bignum.X86_64.word t.mem B (8 * sWsP) = VG.Proof.Bignum.X86_64.off B (offP w)
  wsQ : VG.Proof.Bignum.X86_64.word t.mem B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off B (offQ w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  pxv : XVals t B (offP w) (wsWords pl) mp (if M then P else 3)
  pmask : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B (offP w)) (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask M
  qws : WsAt t.mem B (offQ w pl) (wsWords ql) mq
  qxv : XVals t B (offQ w pl) (wsWords ql) mq (if M then Q else 3)
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs s t

theorem nSetup_eq (M : Mont) : nSetup M.mm =
    (loadSteps ++ restSteps) ++ (r2Steps M ++ [M.mm Public.aXm Public.aX Public.aR2]) := rfl

/-- After `n`'s setup: its values, `c R mod n` and the mask of `c < n`. -/
structure NReady (s t : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N C : Nat) : Prop where
  good : VG.Proof.Bignum.X86_64.Good t B Z w minv
  nv : NVals t B w minv N
  xm : wv t.mem B (VG.Proof.Bignum.X86_64.slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N
  msk : VG.Proof.Bignum.X86_64.word t.mem B (8 * Public.sMask) = VG.Proof.Bignum.X86_64.mask (decide (C < N))
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs s t

/-- `n`'s setup, for a valid modulus. -/
theorem nPart_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte}
    (h : VG.Proof.Bignum.X86_64.CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    WP isa (seqs (nSetup M.mm)) s fun t => ∃ minv,
      VG.Proof.Bignum.X86_64.NReady s t B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) := by
  obtain ⟨hodd, hN1, hlo⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hn := h.scr.nowrap
  have hZ : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have hZs : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8) → ∀ r ∈ rs, r.1 + r.2 ≤ Z :=
    fun h' r hr => (h' r hr).trans hZ
  rw [VG.Proof.Bignum.X86_64.nSetup_eq]
  -- The modulus, the input, `-n⁻¹`, 1 and the mask of `c < n`.
  refine wp_seqs_append (by simp [loadSteps]) (by simp [r2Steps])
    (WP.mono (VG.Proof.Bignum.X86_64.setup_ok h.scr h.rdi hZ (by omega) (by omega) h.hK h.hN h.hIn h.n h.x h.nl h.xl hodd)
      fun t₁ ⟨minv, so, f₁, k₁⟩ => ?_)
  -- `R² mod n`.
  refine wp_seqs_append (by simp [r2Steps]) (by simp)
    (WP.mono (r2_ok M so.good hZ (by omega) (by omega) so.n so.inv so.r12 so.r10 hodd hlo)
      fun t₂ ⟨hg₂, hlt₂, hr₂, f₂, k₂⟩ => ?_)
  have hX₂ : wv t₂.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aX) ((k + 7) / 8) = Spec.Rsa.os2ip xb := by
    rw [f₂.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.x
  have hN₂ : wv t₂.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aN) ((k + 7) / 8) = Spec.Rsa.os2ip nb := by
    rw [f₂.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.n
  have hI₂ : ((VG.Proof.Bignum.X86_64.word t₂.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [f₂.r2_word hn' (by decide) (by decide) (by decide) (by decide)]; exact so.inv
  have hO₂ : wv t₂.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aOne) ((k + 7) / 8) = 1 := by
    rw [f₂.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.one
  -- `c R mod n`.
  simp only [seqs]
  refine WP.mono (mmN_ok M hg₂ hZ (by omega) (by omega) (o := Public.aXm) (a := Public.aX) (b := Public.aR2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hN₂ hI₂ hlt₂)
    fun t₃ ⟨hg₃, hN₃, hI₃, hlt₃, hm₃, ha₃, k₃⟩ => ?_
  have hR : Nat.Coprime (2 ^ (64 * ((k + 7) / 8))) (Spec.Rsa.os2ip nb) := VG.Proof.Bignum.coprime_pow2 hodd _
  have hxm₃ : wv t₃.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aXm) ((k + 7) / 8) % Spec.Rsa.os2ip nb =
      Spec.Rsa.os2ip xb * 2 ^ (64 * ((k + 7) / 8)) % Spec.Rsa.os2ip nb := by
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₃, hX₂, Nat.mul_mod, hr₂, ← Nat.mul_mod, Nat.mul_assoc]
  have g₃ : Frm B [(VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aAcc, 8 * ((k + 7) / 8 + 2)),
      (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aTmp, 8 * ((k + 7) / 8 + 2)),
      (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aXm, 8 * ((k + 7) / 8 + 2))] t₂.mem t₃.mem :=
    Frm.of_arrays ha₃ fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> simp
  have kg₃ : ∀ r ∈ [(VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aAcc, 8 * ((k + 7) / 8 + 2)),
      (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aTmp, 8 * ((k + 7) / 8 + 2)),
      (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aXm, 8 * ((k + 7) / 8 + 2))], KeepsHdr r ∧ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 := by
    have := hdr_lt_slot ((k + 7) / 8) Public.aAcc (show 31 < 32 by decide)
    have := hdr_lt_slot ((k + 7) / 8) Public.aTmp (show 31 < 32 by decide)
    have := hdr_lt_slot ((k + 7) / 8) Public.aXm (show 31 < 32 by decide)
    have := slot_le (w := (k + 7) / 8) (show Public.aAcc < 8 by decide)
    have := slot_le (w := (k + 7) / 8) (show Public.aTmp < 8 by decide)
    have := slot_le (w := (k + 7) / 8) (show Public.aXm < 8 by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl) <;> exact ⟨keepsHdr_ge (by simp only; omega), by simp only; omega⟩
  have e2 : VG.Proof.Bignum.X86_64.word t₂.mem B (8 * Public.sMask) = VG.Proof.Bignum.X86_64.word t₁.mem B (8 * Public.sMask) :=
    f₂.word_eq (r2Ranges_hdr _ (by decide) (by decide)) (by unfold Public.sMask sFn; omega)
  exact ⟨minv, hg₃,
    ⟨hN₃, hI₃, by rw [ha₃.wv_of_not_mem (by decide) (by decide) hn']; exact hr₂,
      by rw [ha₃.wv_of_not_mem (by decide) (by decide) hn']; exact hlt₂,
      by rw [ha₃.wv_of_not_mem (by decide) (by decide) hn']; exact hO₂⟩, hxm₃,
    by rw [ha₃.hslot (by decide), e2]; exact so.mask,
    ((HFix.of_frm f₁ (keepsHdr_setupRanges _)).trans (HFix.of_frm f₂ (keepsHdr_r2Ranges _))).trans
      (HFix.of_frm g₃ fun r hr => (kg₃ r hr).1),
    ((InScr.of_frm f₁ (hZs (setupRanges_le _))).trans (InScr.of_frm f₂ (hZs (r2Ranges_le _)))).trans
      (InScr.of_frm g₃ (hZs fun r hr => (kg₃ r hr).2)),
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- After the primes' workspaces: `n`'s values as before, the workspaces,
`p`, `q` and `qInv`. -/
structure PReady (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N C P Q QI : Nat) : Prop
    where
  n : VG.Proof.Bignum.X86_64.NReady s t B Z w minv N C
  wsP : VG.Proof.Bignum.X86_64.word t.mem B (8 * sWsP) = VG.Proof.Bignum.X86_64.off B (offP w)
  wsQ : VG.Proof.Bignum.X86_64.word t.mem B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off B (offQ w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  qws : WsAt t.mem B (offQ w pl) (wsWords ql) mq
  pv : wv t.mem (VG.Proof.Bignum.X86_64.off B (offP w)) (VG.Proof.Bignum.X86_64.slot (wsWords pl) Public.aN) (wsWords pl) = P
  qiv : wv t.mem (VG.Proof.Bignum.X86_64.off B (offP w)) (VG.Proof.Bignum.X86_64.slot (wsWords pl) aChunk) (wsWords pl) = QI
  qv : wv t.mem (VG.Proof.Bignum.X86_64.off B (offQ w pl)) (VG.Proof.Bignum.X86_64.slot (wsWords ql) Public.aN) (wsWords ql) = Q

/-- The primes' workspaces, from `n`'s setup. -/
theorem setupPart_ok {s t₃ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv : BitVec 64}
    (h : VG.Proof.Bignum.X86_64.CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hr : VG.Proof.Bignum.X86_64.NReady s t₃ B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)) :
    WP isa (seqs primesSetup) t₃ fun t => ∃ mp mq, VG.Proof.Bignum.X86_64.PReady s t B Z ((k + 7) / 8) pl ql minv mp mq
      (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hn := h.scr.nowrap
  have hP8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords pl) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hQ8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords ql) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hZ : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hh₃ : ∀ i < 32, hFixed i = true → VG.Proof.Bignum.X86_64.word t₃.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := hr.hfix
  refine WP.mono (primesSetup_ok hr.good (by omega) (by omega) hZq
    (by rw [hh₃ _ (by decide) (by decide)]; exact h.hPl) (by rw [hh₃ _ (by decide) (by decide)]; exact h.hQl)
    (by rw [hh₃ _ (by decide) (by decide)]; exact h.hP) (by rw [hh₃ _ (by decide) (by decide)]; exact h.hQ)
    (by rw [hh₃ _ (by decide) (by decide)]; exact h.hQi) (h.p.congrK hr.iscr hr.keep) (h.q.congrK hr.iscr hr.keep)
    (h.qi.congrK hr.iscr hr.keep) h.pbl h.qbl h.qil h.pl1 (by have := h.pl2; omega) h.ql1 (by have := h.ql2; omega))
    fun t₄ ⟨hg₄, hsP₄, hsQ₄, ⟨mp, hwp₄⟩, ⟨mq, hwq₄⟩, hp₄, hc₄, hq₄, f₄, k₄⟩ => ?_
  have kf₄ : ∀ r ∈ [(8 * sWsP, 8), (8 * sWsQ, 8), (offP ((k + 7) / 8), VG.Proof.Bignum.X86_64.slot (wsWords pl) 8 + tabBytes (wsWords pl) + VG.Proof.Bignum.X86_64.slot (wsWords ql) 8)],
      KeepsHdr r ∧ r.1 + r.2 ≤ Z ∧ (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * 31) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl)
    · exact ⟨keepsHdr_slot (by decide) (by decide), by simp only [sWsP, sFn]; omega,
        Or.inr (by simp only [sWsP, sFn]; omega)⟩
    · exact ⟨keepsHdr_slot (by decide) (by decide), by simp only [sWsQ, sFn]; omega,
        Or.inr (by simp only [sWsQ, sFn]; omega)⟩
    · exact ⟨keepsHdr_ge (by simp only [offP]; omega), by simp only [offP]; unfold offQ at hZq; omega,
        Or.inl (by simp only [offP]; omega)⟩
  have hnv₄ : ∀ j < 8, wv t₄.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j) ((k + 7) / 8) =
      wv t₃.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j) ((k + 7) / 8) := fun j hj =>
    f₄.wv_eq (fun r hr => by
      have := kf₄ r hr
      have := slot_le (w := (k + 7) / 8) hj
      have := hdr_lt_slot ((k + 7) / 8) j (show 31 < 32 by decide)
      omega) (by have := slot_le (w := (k + 7) / 8) hj; omega)
  have hnw₄ : VG.Proof.Bignum.X86_64.word t₄.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aN) = VG.Proof.Bignum.X86_64.word t₃.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aN) :=
    f₄.word_eq (fun r hr => by
      have := kf₄ r hr
      have := slot_le (w := (k + 7) / 8) (show Public.aN < 8 by decide)
      have := hdr_lt_slot ((k + 7) / 8) Public.aN (show 31 < 32 by decide)
      omega) (by have := slot_le (w := (k + 7) / 8) (show Public.aN < 8 by decide); omega)
  have hM₄ : VG.Proof.Bignum.X86_64.word t₄.mem B (8 * Public.sMask) = VG.Proof.Bignum.X86_64.word t₃.mem B (8 * Public.sMask) := by
    refine f₄.word_eq (fun r hr => ?_) (by unfold Public.sMask sFn; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Or.inl (by simp only [Public.sMask, sWsP, sFn]; omega)
    · exact Or.inl (by simp only [Public.sMask, sWsQ, sFn]; omega)
    · exact Or.inl (by simp only [offP, Public.sMask, sFn]; omega)
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
    (h : VG.Proof.Bignum.X86_64.CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : VG.Proof.Bignum.X86_64.PReady s t₄ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs checks) t₄ fun t => ∃ mp' mq',
      VG.Proof.Bignum.X86_64.CrtReady s t B Z ((k + 7) / 8) pl ql minv mp' mq' (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
        (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) := by
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hn := h.scr.nowrap
  have hP8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords pl) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hQ8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords ql) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hZ : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega
  have hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega
  refine WP.mono (checks_ok hr.n.good (by omega) (by omega) (le_refl _) (by unfold offQ; omega)
    (by unfold offQ at hZq ⊢; omega) hwp2 (wsWords_le (by have := h.pl2; omega) (by omega)) hwq2
    (wsWords_le (by have := h.ql2; omega) (by omega)) hr.wsP hr.wsQ hr.pws hr.qws hr.n.nv.n hr.n.msk hr.pv hr.qv
    hr.qiv hodd)
    fun t ⟨hg, hMt, hsPt, hsQt, ⟨mp', hwpt, hxpt, hmpt⟩, ⟨mq', hwqt, hxqt⟩, f₅, k₅⟩ => ?_
  have kf₅ : ∀ r ∈ [(VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aAcc, 8 * (2 * ((k + 7) / 8) + 2)), (8 * Public.sMask, 8),
      (offP ((k + 7) / 8), VG.Proof.Bignum.X86_64.slot (wsWords pl) 8), (offQ ((k + 7) / 8) pl, VG.Proof.Bignum.X86_64.slot (wsWords ql) 8)],
      KeepsHdr r ∧ r.1 + r.2 ≤ Z := by
    have := accs_le ((k + 7) / 8)
    have := hdr_lt_slot ((k + 7) / 8) Public.aAcc (show 31 < 32 by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl)
    · exact ⟨keepsHdr_ge (by simp only; omega), by simp only; omega⟩
    · exact ⟨keepsHdr_slot (by decide) (by decide), by simp only [Public.sMask, sFn]; omega⟩
    · exact ⟨keepsHdr_ge (by simp only [offP]; omega), by simp only [offP]; unfold offQ at hZq; omega⟩
    · exact ⟨keepsHdr_ge (by simp only [offQ]; omega), by simp only; omega⟩
  have hnv₅ : ∀ j < 8, j ≠ Public.aAcc → j ≠ Public.aTmp → wv t.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j) ((k + 7) / 8) =
      wv t₄.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j) ((k + 7) / 8) := fun j hj h1 h2 => by
    have := slot_le (w := (k + 7) / 8) hj
    have := hdr_lt_slot ((k + 7) / 8) j (show 31 < 32 by decide)
    have := accs_le ((k + 7) / 8)
    have : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j + 8 * ((k + 7) / 8) ≤ VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aAcc ∨
        VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aAcc + 8 * (2 * ((k + 7) / 8) + 2) ≤ VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) j := by
      unfold VG.Proof.Bignum.X86_64.slot Public.aAcc
      rw [show Public.aAcc = 2 from rfl] at h1
      rw [show Public.aTmp = 3 from rfl] at h2
      rcases (show j < 2 ∨ 4 ≤ j by omega) with hj' | hj'
      · left; have := Nat.mul_le_mul_right (8 * ((k + 7) / 8 + 2)) (show j + 1 ≤ 2 by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; omega
      · right; have := Nat.mul_le_mul_right (8 * ((k + 7) / 8 + 2)) (show 4 ≤ j by omega); omega
    refine f₅.wv_eq (fun r hr => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp only; omega
    · exact Or.inr (by simp only [Public.sMask, sFn]; omega)
    · exact Or.inl (by simp only; omega)
    · exact Or.inl (by simp only [offQ]; omega)
  refine ⟨mp', mq', hg, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, hMt, hsPt, hsQt, hwpt, hxpt, hmpt, hwqt, hxqt, ?_, ?_,
    (hr.n.keep.trans k₅).mono (by decide)⟩
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.nv.n
  · have := accs_le ((k + 7) / 8)
    have := slot_le (w := (k + 7) / 8) (show Public.aN < 8 by decide)
    have hN0 := hdr_lt_slot ((k + 7) / 8) Public.aN (show 31 < 32 by decide)
    rw [f₅.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aN + 8 ≤ VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aAcc := by
        unfold VG.Proof.Bignum.X86_64.slot Public.aN Public.aAcc; omega
      rcases hr with rfl | rfl | rfl | rfl
      · exact Or.inl (by simp only; omega)
      · exact Or.inr (by simp only [Public.sMask, sFn]; omega)
      · exact Or.inl (by simp only; omega)
      · exact Or.inl (by simp only [offQ]; omega)) (by omega)]
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
    (h : VG.Proof.Bignum.X86_64.CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    WP isa (seqs (nSetup M.mm ++ primesSetup ++ checks)) s fun t => ∃ minv mp mq,
      VG.Proof.Bignum.X86_64.CrtReady s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
        (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :=
  wp_seqs_append (by simp [nSetup]) (by simp [checks]) (wp_seqs_append (by simp [nSetup])
    (by simp [primesSetup]) (WP.mono (VG.Proof.Bignum.X86_64.nPart_ok M h hv) fun _ ⟨minv, hr⟩ =>
      WP.mono (VG.Proof.Bignum.X86_64.setupPart_ok h hr) fun _ ⟨_, _, hr'⟩ =>
        WP.mono (VG.Proof.Bignum.X86_64.checksPart_ok h hv hr') fun _ ⟨mp', mq', hr''⟩ => ⟨minv, mp', mq', hr''⟩))

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtBack`. -/
section

/-!
# RSA with the CRT on x86-64: from the checks to the result

`q`'s phase, `p`'s, and `m = m_q + q h` written out masked (`back_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

theorem finish_out : VG.Impl.Rsa.X86_64.Crt.finish = finishSum ++ outStepsArr Public.aAcc := rfl

/-- A factor of an odd `N`, its cofactor below `N`: odd and above 1. -/
theorem factor_facts {P Q N : Nat} (h : P * Q = N) (hP : P < N) (hN : N % 2 = 1) : 1 < Q ∧ Q % 2 = 1 := by
  have hodd := odd_of_mul_odd (by rw [Nat.mul_comm]; exact h) hN
  refine ⟨?_, hodd⟩
  rcases Nat.lt_or_ge 1 Q with h1 | h1
  · exact h1
  · rcases (show Q = 0 ∨ Q = 1 by omega) with rfl | rfl
    · rw [Nat.mul_zero] at h; omega
    · rw [Nat.mul_one] at h; omega

/-- The CRT's result for a valid key. -/
def crtResult (P Q dp dq QI C : Nat) : Nat :=
  C ^ dq % Q + Q * ((((C ^ dp % P : Nat) : Int) - (C ^ dq % Q : Nat)) * QI % (P : Int)).toNat

theorem decryptCrt_eq {N P Q dp dq QI C : Nat} :
    Spec.Rsa.decryptCrt N P Q dp dq QI C =
      if C < N ∧ P * Q = N ∧ QI < P then some (VG.Proof.Bignum.X86_64.crtResult P Q dp dq QI C) else none := by
  simp only [Spec.Rsa.decryptCrt, VG.Proof.Bignum.X86_64.crtResult, VG.Proof.Bignum.powMod_eq]

theorem keepsHdr_x {o wx : Nat} (ho : 8 * 32 ≤ o) : KeepsHdr (xRange o wx) := keepsHdr_ge (by simp only [xRange]; omega)

theorem keepsHdr_pRanges (w : Nat) : ∀ r ∈ pRanges w, KeepsHdr r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact keepsHdr_gRanges w r hr
  · rw [List.mem_singleton.mp hr]
    exact keepsHdr_ge (by have := hdr_lt_slot w Public.aX (show 31 < 32 by decide); simp only; omega)

/-- What a valid modulus and the key's lengths give. -/
theorem crt_bounds {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte}
    (h : VG.Proof.Bignum.X86_64.CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    Spec.Rsa.os2ip nb % 2 = 1 ∧ 1 < Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip pb < Spec.Rsa.os2ip nb ∧
      Spec.Rsa.os2ip qb < Spec.Rsa.os2ip nb := by
  obtain ⟨hodd, hN1, _⟩ := valid_facts hv h.k1
  have h256 : 256 ^ (k - 1) ≤ Spec.Rsa.os2ip nb := by
    simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, decide_eq_true_eq] at hv; exact hv.2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  refine ⟨hodd, hN1, ?_, ?_⟩
  · have := os2ip_lt pb
    rw [h.pbl] at this
    exact Nat.lt_of_lt_of_le this ((Nat.pow_le_pow_right (by decide) (by omega)).trans h256)
  · have := os2ip_lt qb
    rw [h.qbl] at this
    exact Nat.lt_of_lt_of_le this ((Nat.pow_le_pow_right (by decide) (by omega)).trans h256)

/-- What the mask gives: the key's checks, and primes (or 3) odd and above 1. -/
theorem mask_facts {N C P Q QI : Nat} {Mk : Bool} (hMk : Mk = keyMask (decide (C < N)) N P Q QI)
    (hodd : N % 2 = 1) (hPN : P < N) (hQN : Q < N) :
    (Mk = true → C < N ∧ P * Q = N ∧ QI < P) ∧
      (1 < (if Mk then P else 3) ∧ (if Mk then P else 3) % 2 = 1) ∧
      (1 < (if Mk then Q else 3) ∧ (if Mk then Q else 3) % 2 = 1) := by
  have hMk' : Mk = true → C < N ∧ P * Q = N ∧ QI < P := fun hm => by
    rw [hMk] at hm
    simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq] at hm
    exact ⟨hm.1.1, hm.1.2, hm.2⟩
  refine ⟨hMk', ?_, ?_⟩
  · cases Mk
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨by decide, by decide⟩
    · obtain ⟨_, hpq, _⟩ := hMk' rfl
      simp only [↓reduceIte]
      exact VG.Proof.Bignum.X86_64.factor_facts (by rw [Nat.mul_comm]; exact hpq) hQN hodd
  · cases Mk
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨by decide, by decide⟩
    · obtain ⟨_, hpq, _⟩ := hMk' rfl
      simp only [↓reduceIte]
      exact VG.Proof.Bignum.X86_64.factor_facts hpq hPN hodd

/-- After `q`'s phase: as after the checks, and `m_q` in `q`'s `aY`. -/
structure QReady (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N C P Q : Nat)
    (dqb : List Byte) (Mk : Bool) : Prop extends VG.Proof.Bignum.X86_64.CrtReady s t B Z w pl ql minv mp mq N C P Q Mk where
  qlt : wv t.mem (VG.Proof.Bignum.X86_64.off B (offQ w pl)) (VG.Proof.Bignum.X86_64.slot (wsWords ql) Public.aY) (wsWords ql) < if Mk then Q else 3
  qval : Mk = true →
    wv t.mem (VG.Proof.Bignum.X86_64.off B (offQ w pl)) (VG.Proof.Bignum.X86_64.slot (wsWords ql) Public.aY) (wsWords ql) = C ^ Spec.Rsa.os2ip dqb % Q

/-- `q`'s phase, from the checks. -/
theorem qPart_ok (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : VG.Proof.Bignum.X86_64.CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : VG.Proof.Bignum.X86_64.CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs (qPhase M.mm)) t₀ fun t => VG.Proof.Bignum.X86_64.QReady s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb)
      (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dqb Mk := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := VG.Proof.Bignum.X86_64.crt_bounds h hv
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.z
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', -, hQ'⟩ := VG.Proof.Bignum.X86_64.mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hP8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords pl) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hQ8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords ql) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hZ : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega
  have hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega
  have hwq := wsWords_le (len := ql) (w := (k + 7) / 8) (by omega) (by omega)
  have hh₀ : ∀ i < 32, hFixed i = true → VG.Proof.Bignum.X86_64.word t₀.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := hr.hfix
  refine WP.mono (qPhase_ok M hr.good (by omega) (by omega) (by unfold offQ; omega) hZq hwq2 hwq hr.wsQ hr.qws
    hr.nv hodd hN1 hr.xm hr.qxv hQ'.1 hQ'.2 (by rw [hh₀ _ (by decide) (by decide)]; exact h.hDq)
    (by rw [hh₀ _ (by decide) (by decide), h.dql]; exact h.hQl) (by rw [h.dql]; omega)
    (by rw [h.dql]; omega) (h.dq.congrK hr.iscr hr.keep))
    fun t₁ ⟨hg₁, hwsq₁, hxq₁, hlt₁, hv₁, f₁, k₁⟩ => ?_
  have hz : B.toNat + VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have hloq : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ offQ ((k + 7) / 8) pl := by unfold offQ; omega
  have f₁' : Frm B (pRanges ((k + 7) / 8) ++ [xRange (offQ ((k + 7) / 8) pl) (wsWords ql)]) t₀.mem t₁.mem :=
    f₁.mono fun r hr => (List.mem_append.mp hr).elim
      (fun h' => List.mem_append_left _ (List.mem_append_left _ h')) (fun h' => List.mem_append_right _ h')
  have hb₁ : ∀ i < 32, i ≠ Crt.sD → i ≠ Public.sCnt → VG.Proof.Bignum.X86_64.word t₁.mem B (8 * i) = VG.Proof.Bignum.X86_64.word t₀.mem B (8 * i) :=
    fun i hi h1 h2 => f₁'.px_hdr hloq hi h1 h2
  -- `p`'s workspace, below `q`'s, is kept.
  have hpk : ∀ d, VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ d → d + 8 ≤ offQ ((k + 7) / 8) pl →
      VG.Proof.Bignum.X86_64.word t₁.mem B d = VG.Proof.Bignum.X86_64.word t₀.mem B d := fun d hd hd' => f₁.word_eq (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact Or.inr (by have := pRanges_le ((k + 7) / 8) r (List.mem_append_left _ hr); omega)
    · rw [List.mem_singleton.mp hr]; exact Or.inl (by simp only [xRange]; omega)) (by omega)
  have hpw₁ : ∀ i < 32, VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.Bignum.X86_64.off B (offP ((k + 7) / 8))) (8 * i) =
      VG.Proof.Bignum.X86_64.word t₀.mem (VG.Proof.Bignum.X86_64.off B (offP ((k + 7) / 8))) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hpk _ (by unfold offP; omega) (by unfold offP offQ; omega)
  have hpv₁ : ∀ d m, d + 8 * m ≤ VG.Proof.Bignum.X86_64.slot (wsWords pl) 8 → wv t₁.mem (VG.Proof.Bignum.X86_64.off B (offP ((k + 7) / 8))) d m =
      wv t₀.mem (VG.Proof.Bignum.X86_64.off B (offP ((k + 7) / 8))) d m := fun d m hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hpk _ (by unfold offP; omega) (by unfold offP offQ; omega)
  have i01 : InScr B Z t₀.mem t₁.mem := InScr.of_frm f₁' fun r hr => by
    have := pxR_bound (wx := wsWords ql) hloq r hr; omega
  refine ⟨⟨hg₁, hr.nv.of_frm f₁ hloq hz (by omega), ?_, ?_, ?_, ?_, hr.pws.of_words fun i hi => hpw₁ i (by omega),
    ⟨?_, ?_, ?_⟩, ?_, hwsq₁, hxq₁, ?_, hr.iscr.trans i01, (hr.keep.trans k₁).mono (by decide)⟩, hlt₁, ?_⟩
  · rw [f₁.gx_wv hloq hz (by decide) (by decide) (by decide) (by decide)]; exact hr.xm
  · rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.msk
  · rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsP
  · rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsQ
  · rw [hpv₁ _ _ (by have := slot_le (w := wsWords pl) (show Public.aN < 8 by decide); omega)]; exact hr.pxv.n
  · rw [word_off, hpk _ (by unfold offP; omega) (by
      have := slot_le (w := wsWords pl) (show Public.aN < 8 by decide); unfold offP offQ; omega), ← word_off]
    exact hr.pxv.inv
  · rw [hpv₁ _ _ (by have := slot_le (w := wsWords pl) (show Public.aOne < 8 by decide); omega)]
    exact hr.pxv.one
  · rw [hpw₁ _ (by decide)]; exact hr.pmask
  · intro i hi hf
    have h1 : i ≠ Crt.sD := by rintro rfl; revert hf; decide
    have h2 : i ≠ Public.sCnt := by rintro rfl; revert hf; decide
    rw [hb₁ i hi h1 h2, hh₀ i hi hf]
  · intro hm
    obtain ⟨_, hpq, _⟩ := hMk' hm
    simp only [hm, ↓reduceIte] at hv₁ hlt₁
    rw [← Nat.mod_eq_of_lt hlt₁]; exact hv₁ ⟨P, by rw [← hpq, Nat.mul_comm]⟩

/-- After `p`'s phase: `h` in `p`'s `aY`, `m_q` in `q`'s. -/
structure PDone (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (C P Q QI : Nat)
    (dpb dqb : List Byte) (Mk : Bool) : Prop where
  good : VG.Proof.Bignum.X86_64.Good t B Z w minv
  msk : VG.Proof.Bignum.X86_64.word t.mem B (8 * Public.sMask) = VG.Proof.Bignum.X86_64.mask Mk
  wsP : VG.Proof.Bignum.X86_64.word t.mem B (8 * sWsP) = VG.Proof.Bignum.X86_64.off B (offP w)
  wsQ : VG.Proof.Bignum.X86_64.word t.mem B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off B (offQ w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  qws : WsAt t.mem B (offQ w pl) (wsWords ql) mq
  qn : wv t.mem (VG.Proof.Bignum.X86_64.off B (offQ w pl)) (VG.Proof.Bignum.X86_64.slot (wsWords ql) Public.aN) (wsWords ql) = if Mk then Q else 3
  qlt : wv t.mem (VG.Proof.Bignum.X86_64.off B (offQ w pl)) (VG.Proof.Bignum.X86_64.slot (wsWords ql) Public.aY) (wsWords ql) < if Mk then Q else 3
  qval : Mk = true →
    wv t.mem (VG.Proof.Bignum.X86_64.off B (offQ w pl)) (VG.Proof.Bignum.X86_64.slot (wsWords ql) Public.aY) (wsWords ql) = C ^ Spec.Rsa.os2ip dqb % Q
  plt : wv t.mem (VG.Proof.Bignum.X86_64.off B (offP w)) (VG.Proof.Bignum.X86_64.slot (wsWords pl) Public.aY) (wsWords pl) < if Mk then P else 3
  pval : Mk = true → ∃ a b, a % P = C ^ Spec.Rsa.os2ip dpb * 2 ^ (64 * wsWords pl) % P ∧
    b % P = C ^ Spec.Rsa.os2ip dqb % Q * 2 ^ (64 * wsWords pl) % P ∧ b < P ∧
    wv t.mem (VG.Proof.Bignum.X86_64.off B (offP w)) (VG.Proof.Bignum.X86_64.slot (wsWords pl) Public.aY) (wsWords pl) * 2 ^ (64 * wsWords pl) % P =
      (a + P - b) % P * QI % P
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs s t

/-- `p`'s phase, from `q`'s. -/
theorem pPart_ok (M : Mont) {s t₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : VG.Proof.Bignum.X86_64.CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : VG.Proof.Bignum.X86_64.QReady s t₁ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dqb Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs (pPhase M.mm)) t₁ fun t => VG.Proof.Bignum.X86_64.PDone s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb Mk := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := VG.Proof.Bignum.X86_64.crt_bounds h hv
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.z
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize hQIe : Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', -⟩ := VG.Proof.Bignum.X86_64.mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hP8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords pl) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hQ8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords ql) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hZ : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega
  have hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega
  have hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega
  have hwp := wsWords_le (len := pl) (w := (k + 7) / 8) (by omega) (by omega)
  have hwq := wsWords_le (len := ql) (w := (k + 7) / 8) (by omega) (by omega)
  have hh₁ : ∀ i < 32, hFixed i = true → VG.Proof.Bignum.X86_64.word t₁.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := hr.hfix
  refine WP.mono (pPhase_ok M (X := if Mk then P else 3) (c := Mk) (eb := dpb) (qib := qib)
    (oq := offQ ((k + 7) / 8) pl) (wq := wsWords ql) hr.good (by omega) (by omega)
    (show VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ offP ((k + 7) / 8) from le_refl _) (by unfold offQ offP; omega) hZq hwp2 hwp
    (by omega) hwq hr.wsP hr.pws hr.wsQ hr.qws hr.nv hodd hN1 hr.xm hr.pxv hP'.1 hP'.2 hr.pmask
    (fun hm => by obtain ⟨_, hpq, _⟩ := hMk' hm; simp only [hm, ↓reduceIte]; exact ⟨Q, hpq.symm⟩)
    (by rw [hh₁ _ (by decide) (by decide)]; exact h.hDp)
    (by rw [hh₁ _ (by decide) (by decide), h.dpl]; exact h.hPl)
    (by rw [h.dpl]; omega) (by rw [h.dpl]; omega) (h.dp.congrK hr.iscr hr.keep)
    (by rw [hh₁ _ (by decide) (by decide)]; exact h.hQi)
    (by rw [h.qil, h.dpl]) (h.qi.congrK hr.iscr hr.keep)
    (by rw [h.qil]; unfold wsWords; omega)
    (fun hm => by obtain ⟨_, _, hqi⟩ := hMk' hm; simp only [hm, ↓reduceIte, hQIe]; exact hqi))
    fun t₂ ⟨hg₂, hwsp₂, hxp₂, hlt₂, hh₂, f₂, k₂⟩ => ?_
  have hlop : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ offP ((k + 7) / 8) := le_refl _
  have hb₂ : ∀ i < 32, i ≠ Crt.sD → i ≠ Public.sCnt → VG.Proof.Bignum.X86_64.word t₂.mem B (8 * i) = VG.Proof.Bignum.X86_64.word t₁.mem B (8 * i) :=
    fun i hi h1 h2 => f₂.px_hdr hlop hi h1 h2
  have hqk : ∀ d, offQ ((k + 7) / 8) pl ≤ d → d + 8 ≤ 2 ^ 64 → VG.Proof.Bignum.X86_64.word t₂.mem B d = VG.Proof.Bignum.X86_64.word t₁.mem B d :=
    fun d hd hd' => f₂.px_above hlop (by unfold offQ offP at *; omega) hd'
  have hqw₂ : ∀ i < 32, VG.Proof.Bignum.X86_64.word t₂.mem (VG.Proof.Bignum.X86_64.off B (offQ ((k + 7) / 8) pl)) (8 * i) =
      VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.Bignum.X86_64.off B (offQ ((k + 7) / 8) pl)) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hqk _ (by omega) (by omega)
  have hqv₂ : ∀ d m, d + 8 * m ≤ VG.Proof.Bignum.X86_64.slot (wsWords ql) 8 → wv t₂.mem (VG.Proof.Bignum.X86_64.off B (offQ ((k + 7) / 8) pl)) d m =
      wv t₁.mem (VG.Proof.Bignum.X86_64.off B (offQ ((k + 7) / 8) pl)) d m := fun d m hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hqk _ (by omega) (by omega)
  have hY8 := slot_le (w := wsWords ql) (show Public.aY < 8 by decide)
  have hN8 := slot_le (w := wsWords ql) (show Public.aN < 8 by decide)
  have i12 : InScr B Z t₁.mem t₂.mem := InScr.of_frm f₂ fun r hr' => by
    have := pxR_bound (wx := wsWords pl) hlop r hr'; unfold offQ offP at *; omega
  refine ⟨hg₂, ?_, ?_, ?_, hwsp₂, hr.qws.of_words fun i hi => hqw₂ i (by omega), ?_, ?_, ?_, hlt₂, ?_, ?_,
    hr.iscr.trans i12, (hr.keep.trans k₂).mono (by decide)⟩
  · rw [hb₂ _ (by decide) (by decide) (by decide)]; exact hr.msk
  · rw [hb₂ _ (by decide) (by decide) (by decide)]; exact hr.wsP
  · rw [hb₂ _ (by decide) (by decide) (by decide)]; exact hr.wsQ
  · rw [hqv₂ _ _ (by omega)]; exact hr.qxv.n
  · rw [hqv₂ _ _ (by omega)]; exact hr.qlt
  · intro hm; rw [hqv₂ _ _ (by omega)]; exact hr.qval hm
  · intro hm
    have hq := hr.qval hm
    obtain ⟨a, b, ha, hb, hbP, hh⟩ := hh₂ hm
    simp only [hm, ↓reduceIte] at ha hb hbP hh
    exact ⟨a, b, ha, by rw [hb, hq], hbP, by rw [hh, hQIe]⟩
  · intro i hi hf
    have h1 : i ≠ Crt.sD := by rintro rfl; revert hf; decide
    have h2 : i ≠ Public.sCnt := by rintro rfl; revert hf; decide
    rw [hb₂ i hi h1 h2, hh₁ i hi hf]

/-- `m = m_q + q h` written out masked, from `p`'s phase. -/
theorem finPart_ok {s t₂ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : VG.Proof.Bignum.X86_64.CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : VG.Proof.Bignum.X86_64.PDone s t₂ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs VG.Impl.Rsa.X86_64.Crt.finish) t₂ fun t => MainPost s t B Z k op
      (if Mk then VG.Proof.Bignum.X86_64.crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := VG.Proof.Bignum.X86_64.crt_bounds h hv
  have hNlt : Spec.Rsa.os2ip nb < 2 ^ (64 * ((k + 7) / 8)) := by
    have := os2ip_lt nb
    rw [h.nl, pow256_eq] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.z
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize hQIe : Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := VG.Proof.Bignum.X86_64.mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hP8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords pl) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hQ8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords ql) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega
  have hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega
  have hwp := wsWords_le (len := pl) (w := (k + 7) / 8) (by omega) (by omega)
  have hwq := wsWords_le (len := ql) (w := (k + 7) / 8) (by omega) (by omega)
  have hZ : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega
  have hlop : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ offP ((k + 7) / 8) := le_refl _
  have hY8 := slot_le (w := wsWords ql) (show Public.aY < 8 by decide)
  have hN8 := slot_le (w := wsWords ql) (show Public.aN < 8 by decide)
  -- `m_q + q h`.
  rw [VG.Proof.Bignum.X86_64.finish_out]
  refine wp_seqs_append (by simp [finishSum, zeroAccs]) (by simp [outStepsArr]) ?_
  refine WP.mono (finishSum_ok hr.good (by omega) hr.wsP hr.wsQ hr.pws.hdr.hw hr.qws.hdr.hw
    (by rw [hr.pws.hdr.harr _ (by decide), off_off]) (by rw [hr.qws.hdr.harr _ (by decide), off_off])
    (by rw [hr.qws.hdr.harr _ (by decide), off_off]) hlop (by unfold offQ offP; omega) hZq (by omega) hwp
    (by omega) hwq) fun t₃ ⟨hm₃, ho₃, k₃⟩ => ?_
  rw [← wv_off, ← wv_off, ← wv_off, hr.qn] at hm₃
  have hacc := accs_le ((k + 7) / 8)
  have hA0 := hdr_lt_slot ((k + 7) / 8) Public.aAcc (show 31 < 32 by decide)
  have hb₃ : ∀ i < 32, VG.Proof.Bignum.X86_64.word t₃.mem B (8 * i) = VG.Proof.Bignum.X86_64.word t₂.mem B (8 * i) := fun i hi =>
    ho₃.word (Or.inl (by have := hdr_lt_slot ((k + 7) / 8) Public.aAcc hi; omega)) (by omega)
  have hg₃ : VG.Proof.Bignum.X86_64.Good t₃ B Z ((k + 7) / 8) minv := ⟨hr.good.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hr.good.rdi,
    ⟨(hb₃ _ (by decide)).trans hr.good.hdr.hw, (hb₃ _ (by decide)).trans hr.good.hdr.hminv,
      fun j hj => (hb₃ _ (by unfold sArr; omega)).trans (hr.good.hdr.harr j hj)⟩⟩
  have hfx : ∀ i < 32, hFixed i = true → VG.Proof.Bignum.X86_64.word t₃.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi hf => by
    rw [hb₃ i hi]; exact hr.hfix i hi hf
  have hM₃ : VG.Proof.Bignum.X86_64.word t₃.mem B (8 * Public.sMask) = VG.Proof.Bignum.X86_64.mask Mk := by rw [hb₃ _ (by decide)]; exact hr.msk
  have k03 := hr.keep.trans k₃
  have i03 : InScr B Z s.mem t₃.mem := hr.iscr.trans (InScr.of_outside ho₃ (by omega))
  -- The result.
  refine WP.mono (outPhaseArr_ok (j := Public.aAcc) (by decide) hg₃ hZ (by omega) (by omega) rfl
    (by rw [hfx _ (by decide) (by decide)]; exact h.hO) (by rw [hfx _ (by decide) (by decide)]; exact h.hK) hM₃
    (fun j hj => by rw [k03.2.2]; exact h.out j hj) h.outSep) fun t ⟨hbytes, hax, hsv, hfr, k₄⟩ => ?_
  refine ⟨?_, hax, fun i hi => by rw [hsv i hi]; exact hfx i (by omega) (by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    fun x hx hx' => by rw [hfr x hx', i03 x hx], (k03.trans k₄).mono (by decide)⟩
  rw [hbytes]
  congr 1
  cases hMk2 : Mk
  · simp only [Bool.false_eq_true, ↓reduceIte]
  · simp only [↓reduceIte]
    obtain ⟨_, hpq, _⟩ := hMk' hMk2
    have hmq := hr.qval hMk2
    have hlt₂ := hr.plt
    simp only [hMk2, ↓reduceIte] at hlt₂ hm₃ hP' hQ'
    obtain ⟨a, b, ha, hb, hbP, hh⟩ := hr.pval hMk2
    have hR : Nat.Coprime (2 ^ (64 * wsWords pl)) P := VG.Proof.Bignum.coprime_pow2 hP'.2 _
    have hhv := VG.Proof.Bignum.crt_h (m₁ := C ^ Spec.Rsa.os2ip dpb % P) (by omega) hR
      (by rw [ha, Nat.mod_mul_mod]) hb hbP hh hlt₂
    -- The sum is below `N`, so below `2^(64 w)`.
    generalize wv t₂.mem (VG.Proof.Bignum.X86_64.off B (offP ((k + 7) / 8))) (VG.Proof.Bignum.X86_64.slot (wsWords pl) Public.aY) (wsWords pl) = hv at *
    rw [hmq] at hm₃
    have hQpos : 0 < Q := by omega
    have hlt : C ^ Spec.Rsa.os2ip dqb % Q + hv * Q < N := by
      have h1 := Nat.mod_lt (C ^ Spec.Rsa.os2ip dqb) hQpos
      have h2 : (hv + 1) * Q ≤ P * Q := Nat.mul_le_mul_right Q (by omega)
      rw [Nat.add_mul, Nat.one_mul] at h2
      omega
    have hsplit := wv_split t₃.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aAcc)
      (show (k + 7) / 8 + ((k + 7) / 8 + 2) = 2 * ((k + 7) / 8) + 2 by omega)
    rw [hm₃] at hsplit
    have hrest : wv t₃.mem B (VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aAcc + 8 * ((k + 7) / 8)) ((k + 7) / 8 + 2) = 0 := by
      by_contra hne
      have := Nat.mul_le_mul_left (2 ^ (64 * ((k + 7) / 8))) (show 1 ≤ _ from Nat.pos_of_ne_zero hne)
      omega
    rw [hrest, Nat.mul_zero, Nat.add_zero] at hsplit
    rw [← hsplit, VG.Proof.Bignum.X86_64.crtResult, hhv, Nat.mul_comm hv Q]

/-- From the checks: both phases, and `m = m_q + q h` written out masked. -/
theorem back_ok (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : VG.Proof.Bignum.X86_64.CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : VG.Proof.Bignum.X86_64.CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs (qPhase M.mm ++ pPhase M.mm ++ VG.Impl.Rsa.X86_64.Crt.finish)) t₀ fun t => MainPost s t B Z k op
      (if Mk then VG.Proof.Bignum.X86_64.crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk := by
  rw [List.append_assoc]
  exact wp_seqs_append (by simp [qPhase]) (by simp [pPhase]) (WP.mono (VG.Proof.Bignum.X86_64.qPart_ok M h hv hr hMk) fun _ hq =>
    wp_seqs_append (by simp [pPhase]) (by simp [VG.Impl.Rsa.X86_64.Crt.finish]) (WP.mono (VG.Proof.Bignum.X86_64.pPart_ok M h hv hq hMk) fun _ hp =>
      VG.Proof.Bignum.X86_64.finPart_ok h hv hp hMk))

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtMain`. -/
section

/-!
# RSA with the CRT on x86-64: the computation for a valid modulus

`main`, from the header `entry` leaves, for a valid modulus: `privateCrt`'s
result (zeros if it is `none`) to `out` and whether it is `some` returned
(`crtMain_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

theorem crtMain_eq (mul : Nat → Nat → Nat → Prog isa) :
    Crt.main mul = seqs ((nSetup mul ++ primesSetup ++ checks) ++ (qPhase mul ++ pPhase mul ++ VG.Impl.Rsa.X86_64.Crt.finish)) := by
  simp only [Crt.main, List.append_assoc]

/-- `main`, for a valid modulus: the result `r`, `some` exactly if the mask
is set. -/
theorem crtMain_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    (h : VG.Proof.Bignum.X86_64.CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    WP isa (Crt.main M.mm) s fun t => ∃ Mk : Bool, MainPost s t B Z k op
      (if Mk then VG.Proof.Bignum.X86_64.crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk ∧
      (Mk = true ↔ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb =
        Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb) := by
  rw [VG.Proof.Bignum.X86_64.crtMain_eq]
  refine wp_seqs_append (by simp [nSetup]) (by simp [qPhase]) (WP.mono (VG.Proof.Bignum.X86_64.front_ok M h hv)
    fun t₀ ⟨minv, mp, mq, hr⟩ => WP.mono (VG.Proof.Bignum.X86_64.back_ok M h hv hr rfl) fun t ht => ⟨_, ht, ?_⟩)
  simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCTMain`. -/
section

/-!
# RSA with the CRT on x86-64: `main` in constant time

`main` leaks the same in runs that agree on the public data (`CrtPub`: the
working space, the pointers, the lengths and `n`), from the constant time of
its parts (`crtMain_ct`). Its states between the parts are those of a run
from a state `CrtPre` describes (`Stage`), where the correctness lemmas of
the parts (`nPart_ok`, `setupPart_ok`, …) give what each part's claim needs.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The public data of `main`: the working space, the pointers, the
lengths and `n`'s bytes. -/
structure CrtPub where
  B : Addr
  Z : Nat
  k : Nat
  op : Addr
  np : Addr
  ip : Addr
  pp : Addr
  qp : Addr
  dpp : Addr
  dqp : Addr
  qip : Addr
  pl : Nat
  ql : Nat
  nb : List Byte

abbrev CrtPub.w (p : VG.Proof.Bignum.X86_64.CrtPub) : Nat := (p.k + 7) / 8
abbrev CrtPub.N (p : VG.Proof.Bignum.X86_64.CrtPub) : Nat := Spec.Rsa.os2ip p.nb

/-- What holds of a state of a run from a state `σ` that `CrtPre` describes
with the public data `p`, the input `xb` and the private key. -/
abbrev StageRel := VG.Proof.Bignum.X86_64.CrtPub → State → List Byte → List Byte → List Byte → List Byte → List Byte → List Byte →
  State → Prop

/-- A state satisfying `R` from such a start. -/
def Stage (R : VG.Proof.Bignum.X86_64.StageRel) (p : VG.Proof.Bignum.X86_64.CrtPub) (t : State) : Prop :=
  ∃ (σ : State) (xb pb qb dpb dqb qib : List Byte),
    VG.Proof.Bignum.X86_64.CrtPre σ p.B p.Z p.k p.op p.np p.ip p.pp p.qp p.dpp p.dqp p.qip p.pl p.ql p.nb xb pb qb dpb dqb qib ∧
    Spec.Rsa.modulusValid p.N p.k = true ∧ R p σ xb pb qb dpb dqb qib t

/-- A part constant time from a stage, with its correctness, goes to the
next stage. -/
theorem stage_step {R R' : VG.Proof.Bignum.X86_64.StageRel} {c : Prog isa} (hct : RelCT isa (Two (VG.Proof.Bignum.X86_64.Stage R)) c fun _ _ => True)
    (hw : ∀ p σ xb pb qb dpb dqb qib t,
      VG.Proof.Bignum.X86_64.CrtPre σ p.B p.Z p.k p.op p.np p.ip p.pp p.qp p.dpp p.dqp p.qip p.pl p.ql p.nb xb pb qb dpb dqb qib →
      Spec.Rsa.modulusValid p.N p.k = true → R p σ xb pb qb dpb dqb qib t →
      WP isa c t (R' p σ xb pb qb dpb dqb qib)) :
    RelCT isa (Two (VG.Proof.Bignum.X86_64.Stage R)) c (Two (VG.Proof.Bignum.X86_64.Stage R')) :=
  two_post hct fun p t ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr⟩ =>
    WP.mono (hw p σ xb pb qb dpb dqb qib t h hv hr) fun _ h' => ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, h'⟩

/-! ## The stages -/

def R0 : VG.Proof.Bignum.X86_64.StageRel := fun _ σ _ _ _ _ _ _ t => t = σ

def R1 : VG.Proof.Bignum.X86_64.StageRel := fun p σ xb _ _ _ _ _ t => ∃ minv, VG.Proof.Bignum.X86_64.NReady σ t p.B p.Z p.w minv p.N (Spec.Rsa.os2ip xb)

def R2 : VG.Proof.Bignum.X86_64.StageRel := fun p σ xb pb qb _ _ qib t => ∃ minv mp mq, VG.Proof.Bignum.X86_64.PReady σ t p.B p.Z p.w p.pl p.ql minv mp mq p.N
  (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)

/-- The mask of a run: whether the input and the key are valid. -/
abbrev CrtPub.mask (p : VG.Proof.Bignum.X86_64.CrtPub) (xb pb qb qib : List Byte) : Bool :=
  keyMask (decide (Spec.Rsa.os2ip xb < p.N)) p.N (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)

def R3 : VG.Proof.Bignum.X86_64.StageRel := fun p σ xb pb qb _ _ qib t => ∃ minv mp mq, VG.Proof.Bignum.X86_64.CrtReady σ t p.B p.Z p.w p.pl p.ql minv mp mq p.N
  (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (p.mask xb pb qb qib)

def R4 : VG.Proof.Bignum.X86_64.StageRel := fun p σ xb pb qb _ dqb qib t => ∃ minv mp mq, VG.Proof.Bignum.X86_64.QReady σ t p.B p.Z p.w p.pl p.ql minv mp mq p.N
  (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dqb (p.mask xb pb qb qib)

def R5 : VG.Proof.Bignum.X86_64.StageRel := fun p σ xb pb qb dpb dqb qib t => ∃ minv mp mq, VG.Proof.Bignum.X86_64.PDone σ t p.B p.Z p.w p.pl p.ql minv mp mq
  (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb (p.mask xb pb qb qib)

/-- `-n⁻¹` is the same in runs that agree on `n`. -/
theorem nv_minv {t t' : State} {B : Addr} {w : Nat} {mi mi' : BitVec 64} {N : Nat} (h : NVals t B w mi N)
    (h' : NVals t' B w mi' N) (hodd : N % 2 = 1) (hw : 1 ≤ w) : mi = mi' := by
  have e : ∀ {t : State} {mi : BitVec 64}, NVals t B w mi N →
      (VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN)).toNat = N % 2 ^ 64 := fun h => by
    rw [← wv_mod64 _ _ _ hw, h.n]
  have i := h.inv
  have i' := h'.inv
  rw [e h] at i
  rw [e h'] at i'
  exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact hodd) i i'

/-! ## `n`'s setup -/

/-- The setup's hypotheses, from `main`'s. -/
theorem stage0_sh {p : VG.Proof.Bignum.X86_64.CrtPub} {s : State} (h : VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R0 p s) : SH ⟨p.B, p.Z, p.k, p.np, p.ip, p.nb⟩ s := by
  obtain ⟨σ, xb, _, _, _, _, _, h, hv, rfl⟩ := h
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have := h.k1
  have := h.k2
  have hZq := h.z
  exact ⟨h.scr, h.rdi, show VG.Proof.Bignum.X86_64.slot ((p.k + 7) / 8) 8 ≤ p.Z by unfold offQ at hZq; omega, show 9 ≤ p.k by omega,
    show p.k < 2 ^ 31 by omega, h.hK, h.hN, h.hIn, h.n, h.nl, hodd, xb, h.x, h.xl⟩

/-- After the setup of `n` and the input. -/
def RA : VG.Proof.Bignum.X86_64.StageRel := fun p _ xb _ _ _ _ _ t => ∃ minv, SetupOut t p.B p.Z p.w minv p.N (Spec.Rsa.os2ip xb)

/-- After `R² mod n`. -/
def RB : VG.Proof.Bignum.X86_64.StageRel := fun p _ _ _ _ _ _ _ t => ∃ minv, VG.Proof.Bignum.X86_64.Good t p.B p.Z p.w minv

/-- `n`'s setup leaks the same in runs that agree on `n`. -/
theorem nSetup_ct (M : Mont) : RelCT isa (Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R0)) (seqs (nSetup M.mm)) fun _ _ => True := by
  rw [VG.Proof.Bignum.X86_64.nSetup_eq]
  refine RelCT.seqs_append (by simp [loadSteps]) (by simp [r2Steps]) (RelCT.seq (R := Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.RA)) ?_ ?_)
  · refine VG.Proof.Bignum.X86_64.stage_step (((RelCT.seqs_append (by simp [loadSteps]) (by simp [restSteps])
      (RelCT.seq setupLoad_ct (two_map (fun p : SPub => (⟨p.B, p.Z, p.w⟩ : RPub)) (fun _ _ h => h.sr)
        setupRest_ct))).mono (fun _ _ h => two_bind (fun (p : VG.Proof.Bignum.X86_64.CrtPub) _ _ h₁ h₂ =>
          ⟨(⟨p.B, p.Z, p.k, p.np, p.ip, p.nb⟩ : SPub), VG.Proof.Bignum.X86_64.stage0_sh h₁, VG.Proof.Bignum.X86_64.stage0_sh h₂⟩) h)
        fun _ _ h => h)) ?_
    rintro p σ xb _ _ _ _ _ t h hv rfl
    obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
    have := h.k1
    have := h.k2
    have hZq := h.z
    exact WP.mono (VG.Proof.Bignum.X86_64.setup_ok h.scr h.rdi (by unfold offQ at hZq; omega) (by omega) (by omega) h.hK h.hN h.hIn
      h.n h.x h.nl h.xl hodd) fun t ⟨minv, so, _⟩ => ⟨minv, so⟩
  refine RelCT.seqs_append (by simp [r2Steps]) (by simp) (RelCT.seq (R := Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.RB)) ?_ ?_)
  · refine VG.Proof.Bignum.X86_64.stage_step ((r2_ct M).mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ => ?_) h) fun _ _ h => h) ?_
    · obtain ⟨σ₁, xb₁, _, _, _, _, _, h₁, hv, mi₁, so₁⟩ := h₁
      obtain ⟨σ₂, xb₂, _, _, _, _, _, _, _, mi₂, so₂⟩ := h₂
      obtain ⟨hodd, -, hlo⟩ := valid_facts hv h₁.k1
      have := h₁.k1
      have := h₁.k2
      have hZq := h₁.z
      have hZ : VG.Proof.Bignum.X86_64.slot ((p.k + 7) / 8) 8 ≤ p.Z := by unfold offQ at hZq; omega
      obtain rfl := so_minv so₁ so₂ hodd (show 1 ≤ p.w by unfold CrtPub.w; omega)
      exact ⟨⟨⟨p.B, p.Z, p.w, mi₁⟩, p.N⟩,
        ⟨⟨so₁.good, hZ⟩, show 2 ≤ p.w by unfold CrtPub.w; omega, show p.w < 2 ^ 30 by unfold CrtPub.w; omega, so₁.n, so₁.inv, so₁.r12, so₁.r10,
          hodd, hlo⟩,
        ⟨⟨so₂.good, hZ⟩, show 2 ≤ p.w by unfold CrtPub.w; omega, show p.w < 2 ^ 30 by unfold CrtPub.w; omega, so₂.n, so₂.inv, so₂.r12, so₂.r10,
          hodd, hlo⟩⟩
    · rintro p _ xb _ _ _ _ _ t h hv ⟨minv, so⟩
      obtain ⟨hodd, -, hlo⟩ := valid_facts hv h.k1
      have := h.k1
      have := h.k2
      have hZq := h.z
      exact WP.mono (r2_ok M so.good (by unfold CrtPub.w; unfold offQ at hZq; omega) (by unfold CrtPub.w; omega)
        (by unfold CrtPub.w; omega) so.n so.inv so.r12 so.r10 hodd hlo) fun t' ⟨hg, _⟩ => ⟨minv, hg⟩
  simp only [seqs]
  exact two_map (fun p : VG.Proof.Bignum.X86_64.CrtPub => (⟨p.B, p.Z, p.w⟩ : Ws)) (fun p t ⟨_, _, _, _, _, _, _, h, _, minv, hg⟩ => by
    have hZq := h.z
    exact ⟨minv, hg, show VG.Proof.Bignum.X86_64.slot ((p.k + 7) / 8) 8 ≤ p.Z by unfold offQ at hZq; omega⟩)
    (M.ct (by unfold MmUse; decide))

/-! ## From the stages to the parts' claims -/

/-- Runs at a stage agree on what a part needs, with `-n⁻¹` (the same in both
runs) among its public data. -/
theorem two_stage {R : VG.Proof.Bignum.X86_64.StageRel} {α : Type} {Φ : α → State → Prop} (f : VG.Proof.Bignum.X86_64.CrtPub → BitVec 64 → α)
    (m : ∀ p σ xb pb qb dpb dqb qib t,
      VG.Proof.Bignum.X86_64.CrtPre σ p.B p.Z p.k p.op p.np p.ip p.pp p.qp p.dpp p.dqp p.qip p.pl p.ql p.nb xb pb qb dpb dqb qib →
      Spec.Rsa.modulusValid p.N p.k = true → R p σ xb pb qb dpb dqb qib t →
      ∃ minv, NVals t p.B p.w minv p.N ∧ Φ (f p minv) t)
    {s₁ s₂ : State} (h : Two (VG.Proof.Bignum.X86_64.Stage R) s₁ s₂) : Two Φ s₁ s₂ := by
  obtain ⟨p, ⟨σ₁, xb₁, pb₁, qb₁, dpb₁, dqb₁, qib₁, h₁, hv, r₁⟩, ⟨σ₂, xb₂, pb₂, qb₂, dpb₂, dqb₂, qib₂, h₂, hv₂, r₂⟩⟩ := h
  obtain ⟨m₁, n₁, φ₁⟩ := m p _ _ _ _ _ _ _ _ h₁ hv r₁
  obtain ⟨m₂, n₂, φ₂⟩ := m p _ _ _ _ _ _ _ _ h₂ hv₂ r₂
  obtain ⟨hodd, -, -⟩ := valid_facts hv h₁.k1
  have := h₁.k1
  obtain rfl := VG.Proof.Bignum.X86_64.nv_minv n₁ n₂ hodd (show 1 ≤ p.w by simp only [CrtPub.w]; omega)
  exact ⟨_, φ₁, φ₂⟩

/-- The primes' setup leaks the same in runs that agree on the public data. -/
theorem setupS_ct (hS : SetupCT) : RelCT isa (Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R1)) (seqs primesSetup) (Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R2)) := by
  refine VG.Proof.Bignum.X86_64.stage_step (hS.mono (fun _ _ h => VG.Proof.Bignum.X86_64.two_stage (fun p minv => (⟨p.B, p.Z, p.w, minv, p.pl, p.ql, p.pp, p.qp,
    p.qip⟩ : SetupPub)) (fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, hr⟩ => ?_) h) fun _ _ h => h)
    fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, hr⟩ => WP.mono (VG.Proof.Bignum.X86_64.setupPart_ok h hr) fun _ h' => ⟨minv, h'⟩
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hh : ∀ i < 32, hFixed i = true → VG.Proof.Bignum.X86_64.word t.mem p.B (8 * i) = VG.Proof.Bignum.X86_64.word σ.mem p.B (8 * i) := hr.hfix
  refine ⟨minv, hr.nv, pb, qb, qib, hr.good, by simp only [CrtPub.w]; omega, by simp only [CrtPub.w]; omega, hZq,
    by rw [hh _ (by decide) (by decide)]; exact h.hPl, by rw [hh _ (by decide) (by decide)]; exact h.hQl,
    by rw [hh _ (by decide) (by decide)]; exact h.hP, by rw [hh _ (by decide) (by decide)]; exact h.hQ,
    by rw [hh _ (by decide) (by decide)]; exact h.hQi, h.p.congrK hr.iscr hr.keep, h.q.congrK hr.iscr hr.keep,
    h.qi.congrK hr.iscr hr.keep, h.pbl, h.qbl, h.qil, h.pl1, ?_, h.ql1, ?_⟩
  · have := h.pl2; simp only [CrtPub.w]; omega
  · have := h.ql2; simp only [CrtPub.w]; omega

/-- The checks leak the same in runs that agree on the public data. -/
theorem checksS_ct (hC : ChecksCT) : RelCT isa (Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R2)) (seqs checks) (Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R3)) := by
  refine VG.Proof.Bignum.X86_64.stage_step (hC.mono (fun _ _ h => VG.Proof.Bignum.X86_64.two_stage (fun p minv => (⟨p.B, p.Z, p.w, minv, p.N, offP p.w,
    offQ p.w p.pl, wsWords p.pl, wsWords p.ql⟩ : ChecksPub)) (fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ =>
      ?_) h) fun _ _ h => h)
    fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => WP.mono (VG.Proof.Bignum.X86_64.checksPart_ok h hv hr) fun _ ⟨mp', mq', h'⟩ =>
      ⟨minv, mp', mq', h'⟩
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hP8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords p.pl) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hQ8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords p.ql) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hwp2 : 2 ≤ wsWords p.pl := by unfold wsWords; omega
  have hwq2 : 2 ≤ wsWords p.ql := by unfold wsWords; omega
  refine ⟨minv, hr.n.nv, ?_⟩
  unfold ChecksPre
  dsimp only [CrtPub.w]
  refine ⟨mp, mq, _, _, _, _, hr.n.good, by omega, by omega,
    show VG.Proof.Bignum.X86_64.slot ((p.k + 7) / 8) 8 ≤ offP ((p.k + 7) / 8) from le_refl _, by unfold offQ offP; omega, hZq, hwp2,
    wsWords_le (by have := h.pl2; omega) (by omega), hwq2, wsWords_le (by have := h.ql2; omega) (by omega),
    hr.wsP, hr.wsQ, hr.pws, hr.qws, hr.n.nv.n, hr.n.msk, hr.pv, hr.qv, hr.qiv, hodd⟩

/-- `q`'s phase leaks the same in runs that agree on the public data. -/
theorem qS_ct (M : Mont) (hQ : QPhaseCT M) : RelCT isa (Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R3)) (seqs (qPhase M.mm)) (Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R4)) := by
  refine VG.Proof.Bignum.X86_64.stage_step (hQ.mono (fun _ _ h => VG.Proof.Bignum.X86_64.two_stage (fun p minv => (⟨p.B, p.Z, p.w, minv, p.N, offQ p.w p.pl,
    wsWords p.ql, p.dqp, p.ql⟩ : PhasePub)) (fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => ?_) h)
      fun _ _ h => h)
    fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => WP.mono (VG.Proof.Bignum.X86_64.qPart_ok M h hv hr rfl) fun _ h' =>
      ⟨minv, mp, mq, h'⟩
  obtain ⟨hodd, hN1, hPN, hQN⟩ := VG.Proof.Bignum.X86_64.crt_bounds h hv
  obtain ⟨-, -, hQ'⟩ := VG.Proof.Bignum.X86_64.mask_facts (Mk := p.mask xb pb qb qib) rfl hodd hPN hQN
  have hk1 := h.k1
  have hk2 := h.k2
  have hql2 := h.ql2
  have hql1 := h.ql1
  have hZq := h.z
  have hQ8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords p.ql) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hwq2 : 2 ≤ wsWords p.ql := by unfold wsWords; omega
  have hh : ∀ i < 32, hFixed i = true → VG.Proof.Bignum.X86_64.word t.mem p.B (8 * i) = VG.Proof.Bignum.X86_64.word σ.mem p.B (8 * i) := hr.hfix
  refine ⟨minv, hr.nv, ?_⟩
  unfold QPre
  dsimp only [CrtPub.w]
  exact ⟨mq, _, _, dqb, hr.good, by omega, by omega,
    by unfold offQ; omega, hZq, hwq2, wsWords_le (by omega) (by omega), hr.wsQ, hr.qws, hr.nv,
    hodd, hN1, hr.xm, hr.qxv, hQ'.1, hQ'.2, by rw [hh _ (by decide) (by decide)]; exact h.hDq,
    by rw [hh _ (by decide) (by decide), h.dql]; exact h.hQl, h.dql, by rw [h.dql]; omega,
    by rw [h.dql]; omega, h.dq.congrK hr.iscr hr.keep⟩

/-- `p`'s phase leaks the same in runs that agree on the public data. -/
theorem pS_ct (M : Mont) (hP : PPhaseCT M) : RelCT isa (Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R4)) (seqs (pPhase M.mm)) (Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R5)) := by
  refine VG.Proof.Bignum.X86_64.stage_step (hP.mono (fun _ _ h => VG.Proof.Bignum.X86_64.two_stage (fun p minv => (⟨⟨p.B, p.Z, p.w, minv, p.N, offP p.w,
    wsWords p.pl, p.dpp, p.pl⟩, offQ p.w p.pl, wsWords p.ql, p.qip⟩ : PPhasePub))
      (fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => ?_) h) fun _ _ h => h)
    fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => WP.mono (VG.Proof.Bignum.X86_64.pPart_ok M h hv hr rfl) fun _ h' =>
      ⟨minv, mp, mq, h'⟩
  obtain ⟨hodd, hN1, hPN, hQN⟩ := VG.Proof.Bignum.X86_64.crt_bounds h hv
  obtain ⟨hMk', hP', -⟩ := VG.Proof.Bignum.X86_64.mask_facts (Mk := p.mask xb pb qb qib) rfl hodd hPN hQN
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.z
  have hP8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords p.pl) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hQ8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords p.ql) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hwp2 : 2 ≤ wsWords p.pl := by unfold wsWords; omega
  have hh : ∀ i < 32, hFixed i = true → VG.Proof.Bignum.X86_64.word t.mem p.B (8 * i) = VG.Proof.Bignum.X86_64.word σ.mem p.B (8 * i) := hr.hfix
  refine ⟨minv, hr.nv, ?_⟩
  unfold PPre
  dsimp only [CrtPub.w]
  refine ⟨mp, mq, _, _, dpb, qib, p.mask xb pb qb qib, hr.good, by omega,
    by omega, show VG.Proof.Bignum.X86_64.slot ((p.k + 7) / 8) 8 ≤ offP ((p.k + 7) / 8) from le_refl _, by unfold offQ offP; omega, hZq, hwp2,
    wsWords_le (by omega) (by omega), by unfold wsWords; omega,
    wsWords_le (by omega) (by omega), hr.wsP, hr.pws, hr.wsQ, hr.qws, hr.nv, hodd, hN1, hr.xm,
    hr.pxv, hP'.1, hP'.2, hr.pmask, fun hm => ?_, by rw [hh _ (by decide) (by decide)]; exact h.hDp,
    by rw [hh _ (by decide) (by decide), h.dpl]; exact h.hPl, h.dpl, by rw [h.dpl]; omega, by rw [h.dpl]; omega,
    h.dp.congrK hr.iscr hr.keep, by rw [hh _ (by decide) (by decide)]; exact h.hQi, by rw [h.qil, h.dpl],
    h.qi.congrK hr.iscr hr.keep, by rw [h.qil]; unfold wsWords; omega, fun hm => ?_⟩
  · obtain ⟨_, hpq, _⟩ := hMk' hm; simp only [hm, ↓reduceIte]; exact ⟨_, hpq.symm⟩
  · obtain ⟨_, _, hqi⟩ := hMk' hm; simp only [hm, ↓reduceIte]; exact hqi

/-! ## The result -/

/-- The public data of the result, without `-n⁻¹`. -/
structure OPubW where
  B : Addr
  Z : Nat
  w : Nat
  k : Nat
  op : Addr

/-- `outPhase_ok`'s hypotheses, for some `-n⁻¹`. -/
def OPreW (p : VG.Proof.Bignum.X86_64.OPubW) (s : State) : Prop := ∃ minv, OPre ⟨⟨p.B, p.Z, p.w, minv⟩, p.k, p.op⟩ s

/-- Before `storeBE`, from array `j`. -/
def O1Arr (j : Nat) (p : VG.Proof.Bignum.X86_64.OPubW) (s : State) : Prop :=
  ∃ c : Bool, VG.Proof.Bignum.X86_64.Scr s p.B p.Z ∧ s.gpr .rdi = p.B ∧ p.w = (p.k + 7) / 8 ∧ VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.Z ∧
    1 ≤ p.k ∧ p.k < 2 ^ 31 ∧ s.gpr .rbx = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w j) ∧ s.gpr .rsi = p.op ∧
    s.gpr .rcx = BitVec.ofNat 64 p.k ∧ s.gpr .r15 = VG.Proof.Bignum.X86_64.mask c ∧
    (∀ j < p.k, InRegions s.wr (p.op + BitVec.ofNat 64 j) 1) ∧
    (∀ j < p.k, p.Z ≤ VG.Proof.Bignum.X86_64.ofs p.B (p.op + BitVec.ofNat 64 j))

/-- The result's store from array `j` (`out_ct`'s), given that the taint
analysis checks its loads. -/
theorem outArr_ct {j : Nat} (hj : j < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rbx (.mem (hdr (sArr j))), .mov .rsi (.mem (hdr Public.sOut)),
      .mov .rcx (.mem (hdr Public.sK)), .mov .r15 (.mem (hdr Public.sMask))]) hc).isSome = true) :
    RelCT isa (Two VG.Proof.Bignum.X86_64.OPreW) (seqs (outStepsArr j)) fun _ _ => True := by
  unfold outStepsArr
  refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.O1Arr j) [.rdi] (fun p s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi, h₂.rdi]) hT ?_) ?_
  · rintro p s ⟨_, c, hg, hw, hZ, hk1, hk, hO, hK, hM, hout, hsep⟩
    dsimp only at hg hw hZ hk1 hk hO hK hM hout hsep
    have hn := hg.scr.nowrap
    obtain ⟨g0, g8⟩ := slot0_ge p.w
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off p.B (8 * i)) 8 := fun i hi => hg.scr.ld (by omega)
    refine WP.mono (WP.keep [.rbx, .rsi, .rcx, .r15] (Q := fun t =>
        t.gpr .rbx = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w j) ∧ t.gpr .rsi = p.op ∧ t.gpr .rcx = BitVec.ofNat 64 p.k ∧
        t.gpr .r15 = VG.Proof.Bignum.X86_64.mask c ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr j) (by unfold sArr; omega), hl Public.sOut (by decide),
        hl Public.sK (by decide), hl Public.sMask (by decide), hg.hdr.harr j hj, hO, hK, hM]) rfl)
      fun t ⟨⟨hbx, hsi, hcx, h15, hm⟩, k⟩ => ⟨c, hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hw, hZ,
        hk1, hk, hbx, hsi, hcx, h15, fun j hj => by rw [k.2.2]; exact hout j hj, hsep⟩
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .rdi = p.B) [.rbx, .rsi, .rcx]
    (fun p s₁ s₂ ⟨_, _, _, _, _, _, _, a₁, b₁, c₁, _⟩ ⟨_, _, _, _, _, _, _, a₂, b₂, c₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]) (by taint_decide) ?_) ?_
  · rintro p s ⟨c, hs, hdi, hw, hZ, hk1, hk, hbx, hsi, hcx, h15, hout, hsep⟩
    exact WP.mono (storeBE_ok hs hbx hsi hcx h15 hk1 hk hw
      (by have := slot_le (w := p.w) hj; omega) hout hsep)
      fun t ⟨_, _, _, _, k⟩ => (k.gpr (by decide)).trans hdi
  exact two_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide)

/-! ## `main` -/

/-- `main` leaks the same in runs that agree on the public data, given that
its parts do. -/
theorem crtMain_ct (M : Mont) (hS : SetupCT) (hC : ChecksCT) (hQ : QPhaseCT M) (hP : PPhaseCT M)
    (hF : RelCT isa (Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R5)) (seqs VG.Impl.Rsa.X86_64.Crt.finish) fun _ _ => True) :
    RelCT isa (Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R0)) (Crt.main M.mm) fun _ _ => True := by
  rw [VG.Proof.Bignum.X86_64.crtMain_eq]
  refine RelCT.seqs_append (by simp [nSetup]) (by simp [qPhase]) (RelCT.seq (R := Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R3)) ?_ ?_)
  · refine RelCT.seqs_append (by simp [nSetup]) (by simp [checks])
      (RelCT.seq (R := Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R2)) ?_ (VG.Proof.Bignum.X86_64.checksS_ct hC))
    refine RelCT.seqs_append (by simp [nSetup]) (by simp [primesSetup])
      (RelCT.seq (R := Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R1)) ?_ (VG.Proof.Bignum.X86_64.setupS_ct hS))
    exact VG.Proof.Bignum.X86_64.stage_step (VG.Proof.Bignum.X86_64.nSetup_ct M) fun p σ xb _ _ _ _ _ t h hv ht => by
      subst ht; exact WP.mono (VG.Proof.Bignum.X86_64.nPart_ok M h hv) fun _ ⟨minv, hr⟩ => ⟨minv, hr⟩
  rw [List.append_assoc]
  refine RelCT.seqs_append (by simp [qPhase]) (by simp [pPhase]) (RelCT.seq (VG.Proof.Bignum.X86_64.qS_ct M hQ) ?_)
  exact RelCT.seqs_append (by simp [pPhase]) (by simp [VG.Impl.Rsa.X86_64.Crt.finish]) (RelCT.seq (VG.Proof.Bignum.X86_64.pS_ct M hP) hF)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCode`. -/
section

/-!
# RSA with the CRT on x86-64: correctness

`Crt.code`, from a state its contract allows, writes `privateCrt` of its
inputs (`crtCode_correct`), against `crtContract` (`CrtContract.lean`),
which states the shared contract's precondition on the registers and the
stack.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## The result -/

/-- What `Crt.code` leaves: the result `r` and flag `c` of `fail` or
`main`. -/
theorem crtWritten_of {m : Mem} {out : Addr} {k : Nat} {rax : BitVec 64} {nb xb pb qb dpb dqb qib : List Byte}
    (hnl : nb.length = k) {r : Nat} {c : Bool}
    (hb : Spec.Rsa.bytesAt m out k = Spec.Rsa.i2osp r k) (hr : rax = BitVec.ofNat 64 c.toNat)
    (hc : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true →
      (c = true ↔ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb =
        Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb) ∧
      r = if c then VG.Proof.Bignum.X86_64.crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0)
    (hf : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = false → c = false ∧ r = 0) :
    Spec.Rsa.written m out k (rax.setWidth 32) (Spec.Rsa.privateCrt nb xb pb qb dpb dqb qib) := by
  simp only [Spec.Rsa.privateCrt]
  rw [hnl, hr, setWidth_flag]
  cases hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k
  · obtain ⟨rfl, rfl⟩ := hf hv
    simp only [Bool.false_eq_true, ite_false, Spec.Rsa.written]
    exact ⟨trivial, by rw [hb, i2osp_zero']⟩
  · obtain ⟨hiff, rfl⟩ := hc hv
    simp only [ite_true, VG.Proof.Bignum.X86_64.decryptCrt_eq]
    cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hb
    · have hx := mt hiff.mpr (by decide)
      simp only [hx, Bool.false_eq_true, ite_false, Option.map_none, Spec.Rsa.written]
      exact ⟨trivial, by rw [hb, i2osp_zero']⟩
    · simp only [hiff.mp rfl, and_self, ite_true, Option.map_some, Spec.Rsa.written]
      exact ⟨trivial, hb⟩

/-! ## The precondition, as `main` uses it -/

theorem stackArgAddr_add (s : State) (j b : Nat) :
    stackArgAddr s j + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j + b) := by
  rw [stackArgAddr_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- What `Crt.code` uses of its contract's precondition, for the working
space `B` (stack argument 10) of `Z` bytes, `n`'s length `k` and the
primes' lengths (stack arguments 1 and 3). -/
structure CrtCtx (s : State) : Prop where
  hk1 : 64 ≤ (s.gpr .rcx).toNat
  hk2 : (s.gpr .rcx).toNat ≤ 1024
  hpl1 : 1 ≤ (stackArg s 1).toNat
  hpl2 : (stackArg s 1).toNat < (s.gpr .rcx).toNat
  hql1 : 1 ≤ (stackArg s 3).toNat
  hql2 : (stackArg s 3).toNat < (s.gpr .rcx).toNat
  hZ : 128 * (s.gpr .rcx).toNat ≤ (stackArg s 11).toNat * 8
  hs : VG.Proof.Bignum.X86_64.Scr s (stackArg s 10) ((stackArg s 11).toNat * 8)
  ha : ∀ j < 11, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 11, ∀ m', VG.Proof.Bignum.X86_64.Outside (stackArg s 10) 0 (8 * 32) s.mem m' →
    m'.readW (stackArgAddr s j) 64 = stackArg s j
  hnb : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (s.gpr .rdx)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  hxb : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (s.gpr .r8)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .rcx).toNat)
  hpb : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (stackArg s 0)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
  hqb : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (stackArg s 2)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
  hdpb : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (stackArg s 4)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
  hdqb : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (stackArg s 6)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
  hqib : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (stackArg s 8)
    (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)
  hout : ∀ j < (s.gpr .rcx).toNat, InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 j) 1
  houts : ∀ j < (s.gpr .rcx).toNat,
    (stackArg s 11).toNat * 8 ≤ VG.Proof.Bignum.X86_64.ofs (stackArg s 10) (s.gpr .rdi + BitVec.ofNat 64 j)
  hret : ∀ b < 8, (stackArg s 11).toNat * 8 ≤ VG.Proof.Bignum.X86_64.ofs (stackArg s 10) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    ∀ j < (s.gpr .rcx).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdi + BitVec.ofNat 64 j

theorem crtCtx_of {s : State} (h : crtContract.pre s) : VG.Proof.Bignum.X86_64.CrtCtx s := by
  simp only [crtContract] at h
  obtain ⟨hsp, hrd, hwr, dOn, dOi, dOp, dOq, dOdp, dOdq, dOqi, dOs, dOa, dns, dis, dps, dqs, ddps, ddqs, dqis, dsa,
    dRo, dRn, dRi, dRp, dRq, dRdp, dRdq, dRqi, dRs, dRa, wO, wN, wI, wP, wQ, wDp, wDq, wQi, wS, hk, hol, hil,
    hpl1, hpl2, hql1, hql2, hdpl, hqil, hdql, hsl⟩ := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : VG.Proof.Bignum.X86_64.Scr s (stackArg s 10) ((stackArg s 11).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 96⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  refine ⟨hk1, hk2, hpl1, hpl2, hql1, hql2, by omega, hs,
    fun j hj => ⟨_, hargs, by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 96) (by omega) (by omega))
      rw [← VG.Proof.Bignum.X86_64.stackArgAddr_add s j b] at this; omega)),
    src_of_region (by rw [hrd]; simp) (by omega) dns,
    src_of_region (by rw [hrd, ← hil]; simp) (by omega) (by rw [← hil]; exact dis),
    src_of_region (by rw [hrd]; simp) (by omega) dps,
    src_of_region (by rw [hrd]; simp) (by omega) dqs,
    src_of_region (by rw [hrd, ← hdpl]; simp) (by omega) (by rw [← hdpl]; exact ddps),
    src_of_region (by rw [hrd, ← hdql]; simp) (by omega) (by rw [← hdql]; exact ddqs),
    src_of_region (by rw [hrd, ← hqil]; simp) (by omega) (by rw [← hqil]; exact dqis),
    fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self, contains_byte _ (by omega) (by omega)⟩,
    fun j hj => out_scr dOs (contains_byte _ (by omega) (by omega)), fun b hb => ?_⟩
  have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega) (by omega)
  exact ⟨out_scr dRs hc, fun j hj he => dRo _ hc (by rw [he]; exact contains_byte _ (by omega) (by omega))⟩

/-- After `entry` and the reloads of `n` and `k`, from `s`. -/
structure CrtHeadPost (s t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t (stackArg s 10) ((stackArg s 11).toNat * 8)
  rdi : t.gpr .rdi = stackArg s 10
  rdx : t.gpr .rdx = s.gpr .rdx
  rcx : t.gpr .rcx = BitVec.ofNat 64 (s.gpr .rcx).toNat
  saved : ∀ i < 6, VG.Proof.Bignum.X86_64.word t.mem (stackArg s 10) (8 * i) = s.gpr (saved.getD i .rax)
  hO : VG.Proof.Bignum.X86_64.word t.mem (stackArg s 10) (8 * sOut) = s.gpr .rdi
  hN : VG.Proof.Bignum.X86_64.word t.mem (stackArg s 10) (8 * sN) = s.gpr .rdx
  hK : VG.Proof.Bignum.X86_64.word t.mem (stackArg s 10) (8 * sK) = BitVec.ofNat 64 (s.gpr .rcx).toNat
  hIn : VG.Proof.Bignum.X86_64.word t.mem (stackArg s 10) (8 * sIn) = s.gpr .r8
  hP : VG.Proof.Bignum.X86_64.word t.mem (stackArg s 10) (8 * sP) = stackArg s 0
  hPl : VG.Proof.Bignum.X86_64.word t.mem (stackArg s 10) (8 * sPlen) = BitVec.ofNat 64 (stackArg s 1).toNat
  hQ : VG.Proof.Bignum.X86_64.word t.mem (stackArg s 10) (8 * sQ) = stackArg s 2
  hQl : VG.Proof.Bignum.X86_64.word t.mem (stackArg s 10) (8 * sQlen) = BitVec.ofNat 64 (stackArg s 3).toNat
  hDp : VG.Proof.Bignum.X86_64.word t.mem (stackArg s 10) (8 * sDp) = stackArg s 4
  hDq : VG.Proof.Bignum.X86_64.word t.mem (stackArg s 10) (8 * sDq) = stackArg s 6
  hQi : VG.Proof.Bignum.X86_64.word t.mem (stackArg s 10) (8 * sQinv) = stackArg s 8
  inScr : InScr (stackArg s 10) ((stackArg s 11).toNat * 8) s.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep [.r11, .rax, .rdi, .rdx, .rcx] s t

/-- `entry`, and `n` and `k` into `rdx` and `rcx`. -/
theorem crtHead_ok {s : State} (c : VG.Proof.Bignum.X86_64.CrtCtx s) :
    WP isa (.block (Crt.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr))) s
      (VG.Proof.Bignum.X86_64.CrtHeadPost s) := by
  have hn := c.hs.nowrap
  have hZ := c.hZ
  have hk1 := c.hk1
  have hw : ∀ i < 32, InRegions s.wr (VG.Proof.Bignum.X86_64.off (stackArg s 10) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (crtEntry_ok rfl hw c.ha c.hsep) fun t₀ ⟨hdi, hsv, hO, hN, hK, hI, hP, hPl, hQ, hQl, hDp, hDq,
    hQi, ho₀, k₀⟩ => ?_
  have hs₀ := c.hs.congr k₀.2.2
  refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = s.gpr .rdx ∧
      t.gpr .rcx = s.gpr .rcx ∧ t.mem = t₀.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hs₀.ld (d := 8 * sN) (by unfold sN sFn; omega),
      hs₀.ld (d := 8 * sK) (by unfold sK sFn; omega), hN, hK]) rfl) fun t₁ ⟨⟨hdx, hcx, hm⟩, k₁⟩ => ?_
  rw [← hm] at hsv hO hN hK hI hP hPl hQ hQl hDp hDq hQi
  exact ⟨hs₀.congr k₁.2.2, (k₁.gpr (by decide)).trans hdi, hdx, by rw [hcx, VG.Proof.Bignum.X86_64.ofNat_toNat64], hsv, hO, hN,
    by rw [hK, VG.Proof.Bignum.X86_64.ofNat_toNat64], hI, hP, by rw [hPl, VG.Proof.Bignum.X86_64.ofNat_toNat64], hQ, by rw [hQl, VG.Proof.Bignum.X86_64.ofNat_toNat64], hDp, hDq, hQi,
    by rw [hm]; exact InScr.of_outside ho₀ (by omega), (k₀.trans k₁).mono (by decide)⟩

/-- `main`'s hypotheses after the head and the modulus' check. -/
theorem crtPre_of {s t₁ t : State} (c : VG.Proof.Bignum.X86_64.CrtCtx s) (h : VG.Proof.Bignum.X86_64.CrtHeadPost s t₁) (hm : t.mem = t₁.mem)
    (k : VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .rsi] t₁ t) :
    VG.Proof.Bignum.X86_64.CrtPre t (stackArg s 10) ((stackArg s 11).toNat * 8) (s.gpr .rcx).toNat (s.gpr .rdi) (s.gpr .rdx)
      (s.gpr .r8) (stackArg s 0) (stackArg s 2) (stackArg s 4) (stackArg s 6) (stackArg s 8)
      (stackArg s 1).toNat (stackArg s 3).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .rcx).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat) := by
  have kk := h.keep.trans k
  have hi : InScr (stackArg s 10) ((stackArg s 11).toNat * 8) s.mem t.mem := by rw [hm]; exact h.inScr
  have hZ := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hpl2 := c.hpl2
  have hql2 := c.hql2
  have hdi : t.gpr .rdi = stackArg s 10 := (k.gpr (by decide)).trans h.rdi
  have hz : offQ (((s.gpr .rcx).toNat + 7) / 8) (stackArg s 1).toNat + VG.Proof.Bignum.X86_64.slot (wsWords (stackArg s 3).toNat) 8 +
      tabBytes (wsWords (stackArg s 3).toNat) ≤ (stackArg s 11).toNat * 8 := by
    unfold offQ VG.Proof.Bignum.X86_64.slot wsWords hdrBytes tabBytes; omega
  exact
    { scr := h.scr.congr k.2.2, rdi := hdi, z := hz, zk := hZ, k1 := hk1, k2 := hk2, hO := (by rw [hm]; exact h.hO),
      hN := (by rw [hm]; exact h.hN), hK := (by rw [hm]; exact h.hK), hIn := (by rw [hm]; exact h.hIn),
      hP := (by rw [hm]; exact h.hP), hPl := (by rw [hm]; exact h.hPl), hQ := (by rw [hm]; exact h.hQ),
      hQl := (by rw [hm]; exact h.hQl), hDp := (by rw [hm]; exact h.hDp), hDq := (by rw [hm]; exact h.hDq),
      hQi := (by rw [hm]; exact h.hQi), n := c.hnb.congrK hi kk, x := c.hxb.congrK hi kk,
      p := c.hpb.congrK hi kk, q := c.hqb.congrK hi kk, dp := c.hdpb.congrK hi kk, dq := c.hdqb.congrK hi kk,
      qi := c.hqib.congrK hi kk, nl := VG.Proof.Bignum.X86_64.bytesAt_length _ _ _, xl := VG.Proof.Bignum.X86_64.bytesAt_length _ _ _,
      pbl := VG.Proof.Bignum.X86_64.bytesAt_length _ _ _, qbl := VG.Proof.Bignum.X86_64.bytesAt_length _ _ _, dpl := VG.Proof.Bignum.X86_64.bytesAt_length _ _ _,
      dql := VG.Proof.Bignum.X86_64.bytesAt_length _ _ _, qil := VG.Proof.Bignum.X86_64.bytesAt_length _ _ _, pl1 := c.hpl1, pl2 := hpl2, ql1 := c.hql1,
      ql2 := hql2, out := (fun j hj => by rw [kk.2.2]; exact c.hout j hj), outSep := c.houts }

/-- What `Crt.code` leaves, from what `fail` or `main` leaves. -/
theorem crtCode_fin {s t₁ t₂ t : State} (c : VG.Proof.Bignum.X86_64.CrtCtx s) (h : VG.Proof.Bignum.X86_64.CrtHeadPost s t₁) (hm : t₂.mem = t₁.mem)
    (k : VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .rsi] t₁ t₂) {r : Nat} {cb : Bool}
    (hp : MainPost t₂ t (stackArg s 10) ((stackArg s 11).toNat * 8) (s.gpr .rcx).toNat (s.gpr .rdi) r cb)
    (hc : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = true →
      (cb = true ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .rcx).toNat) <
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) *
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat) =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat) <
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)) ∧
      r = if cb then VG.Proof.Bignum.X86_64.crtResult (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .rcx).toNat)) else 0)
    (hf : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = false → cb = false ∧ r = 0) :
    gprPreserved s t ∧ crtContract.post s t := by
  refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩,
    VG.Proof.Bignum.X86_64.crtWritten_of (VG.Proof.Bignum.X86_64.bytesAt_length _ _ _) hp.bytes hp.rax hc hf⟩
  · have kk := h.keep.trans k
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.saved 0 (by decide)).trans (by rw [hm]; exact h.saved 0 (by decide))
    · exact (hp.saved 1 (by decide)).trans (by rw [hm]; exact h.saved 1 (by decide))
    · exact (hp.keep.gpr (by decide)).trans (kk.gpr (by decide))
    · exact (hp.saved 2 (by decide)).trans (by rw [hm]; exact h.saved 2 (by decide))
    · exact (hp.saved 3 (by decide)).trans (by rw [hm]; exact h.saved 3 (by decide))
    · exact (hp.saved 4 (by decide)).trans (by rw [hm]; exact h.saved 4 (by decide))
    · exact (hp.saved 5 (by decide)).trans (by rw [hm]; exact h.saved 5 (by decide))
  · obtain ⟨hZx, hne⟩ := c.hret b hb
    rw [hp.frame _ hZx hne, hm, h.inScr _ hZx]

/-- `vg_rsa_private_crt` with Montgomery multiplication `M`, given that its
code never loads MXCSR (which the registration file evaluates). -/
theorem crtCode_correct (M : Mont) (hmx : (Crt.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : crtContract.pre s) :
    ∃ t s', Exec isa (Crt.code M.mm) s t s' ∧ abiPreserved s s' ∧ crtContract.post s s' := by
  have c := VG.Proof.Bignum.X86_64.crtCtx_of h
  clear h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  suffices hwp : WP isa (Crt.code M.mm) s fun s' => gprPreserved s s' ∧ crtContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold Crt.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.crtHead_ok c) fun t₁ h₁ => ?_
  have hnb₁ := c.hnb.congrK h₁.inScr h₁.keep
  refine WP.mono (invalid_ok h₁.rdx h₁.rcx hk1 hk2 (VG.Proof.Bignum.X86_64.bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by
    rw [VG.Proof.Bignum.X86_64.bytesAt_length]; exact hi)) (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_
  have hpre := VG.Proof.Bignum.X86_64.crtPre_of c h₁ hm₂ k₂
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (s.gpr .rcx).toNat) (by simp [VG.X86_64.eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = false := by simpa using hb
    exact WP.mono (fail_ok hpre.scr hpre.rdi (by omega)
      (by omega) (by omega) hpre.hO hpre.hK hpre.out hpre.outSep)
      fun t hp => VG.Proof.Bignum.X86_64.crtCode_fin c h₁ hm₂ k₂ hp (fun h => absurd h (by rw [hv]; decide)) fun _ => ⟨rfl, rfl⟩
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = true := by simpa using hb
    exact WP.mono (VG.Proof.Bignum.X86_64.crtMain_ok M hpre hv) fun t ⟨Mk, hp, hiff⟩ => VG.Proof.Bignum.X86_64.crtCode_fin c h₁ hm₂ k₂ hp
      (fun _ => ⟨hiff, rfl⟩) fun h => absurd h (by rw [hv]; decide)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCode`. -/
section

/-!
# `vg_rsa_private_crt` on x86-64: constant time but for `n`

`entry` and the modulus' check leak the same in runs that agree on the
public data (the arguments but the input and the key's values, and `n`),
and so do `fail` and `main` (`crtMain_ct`): `crtCode_ct`, and the contract's
`ConstantTime` (`crtCode_constantTime`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The public data of `vg_rsa_private_crt`: `main`'s and the stack pointer. -/
structure CCPub where
  m : VG.Proof.Bignum.X86_64.CrtPub
  rsp : Addr

/-- A state the contract allows, with the public data `p`. -/
def CCRel (p : VG.Proof.Bignum.X86_64.CCPub) (s : State) : Prop :=
  crtContract.pre s ∧ s.gpr .rsp = p.rsp ∧ stackArg s 10 = p.m.B ∧ (stackArg s 11).toNat * 8 = p.m.Z ∧
    (s.gpr .rcx).toNat = p.m.k ∧ s.gpr .rdi = p.m.op ∧ s.gpr .rdx = p.m.np ∧ s.gpr .r8 = p.m.ip ∧
    stackArg s 0 = p.m.pp ∧ stackArg s 2 = p.m.qp ∧ stackArg s 4 = p.m.dpp ∧ stackArg s 6 = p.m.dqp ∧
    stackArg s 8 = p.m.qip ∧ (stackArg s 1).toNat = p.m.pl ∧ (stackArg s 3).toNat = p.m.ql ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = p.m.nb

theorem crtEntry_split : Crt.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) =
    ([.mov .r11 (.mem { base := .rsp, disp := 88 })] : List Instr) ++
      ((Crt.entry.drop 1) ++ [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))]) := rfl

/-- After `entry`'s first instruction. -/
def CC1 (p : VG.Proof.Bignum.X86_64.CCPub) (t : State) : Prop :=
  ∃ s, VG.Proof.Bignum.X86_64.CCRel p s ∧ t.gpr .r11 = p.m.B ∧ t.gpr .rsp = p.rsp ∧
    WP isa (.block ((Crt.entry.drop 1) ++ [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))])) t
      (VG.Proof.Bignum.X86_64.CrtHeadPost s)

/-- After `entry` and the reloads. -/
def CC2 (p : VG.Proof.Bignum.X86_64.CCPub) (t : State) : Prop := ∃ s, VG.Proof.Bignum.X86_64.CCRel p s ∧ VG.Proof.Bignum.X86_64.CrtHeadPost s t

/-- After the modulus' check. -/
def CC3 (p : VG.Proof.Bignum.X86_64.CCPub) (t : State) : Prop :=
  ∃ s t₁, VG.Proof.Bignum.X86_64.CCRel p s ∧ VG.Proof.Bignum.X86_64.CrtHeadPost s t₁ ∧ t.mem = t₁.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .rsi] t₁ t ∧
    t.zf = some (Spec.Rsa.modulusValid p.m.N p.m.k)

/-- `main`'s hypotheses after the head and the modulus' check. -/
theorem cc3_pre {p : VG.Proof.Bignum.X86_64.CCPub} {t : State} (h : VG.Proof.Bignum.X86_64.CC3 p t) :
    ∃ xb pb qb dpb dqb qib, VG.Proof.Bignum.X86_64.CrtPre t p.m.B p.m.Z p.m.k p.m.op p.m.np p.m.ip p.m.pp p.m.qp p.m.dpp p.m.dqp
      p.m.qip p.m.pl p.m.ql p.m.nb xb pb qb dpb dqb qib := by
  obtain ⟨s, t₁, ⟨hpre, -, hB, hZ, hk, hop, hnp, hip, hpp, hqp, hdpp, hdqp, hqip, hpl, hql, hnb⟩, h, hm, k, -⟩ := h
  have := VG.Proof.Bignum.X86_64.crtPre_of (VG.Proof.Bignum.X86_64.crtCtx_of hpre) h hm k
  rw [hB, hZ, hk, hop, hnp, hip, hpp, hqp, hdpp, hdqp, hqip, hpl, hql] at this
  rw [hnp, hk] at hnb
  rw [hnb] at this
  exact ⟨_, _, _, _, _, _, this⟩

variable (M : Mont)

/-- `vg_rsa_private_crt` leaks the same in runs that agree on the public data,
given that `main`'s parts do. -/
theorem crtCode_ct (hS : SetupCT) (hC : ChecksCT) (hQ : QPhaseCT M) (hP : PPhaseCT M)
    (hF : RelCT isa (Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R5)) (seqs VG.Impl.Rsa.X86_64.Crt.finish) fun _ _ => True) :
    RelCT isa (Two VG.Proof.Bignum.X86_64.CCRel) (Crt.code M.mm) fun _ _ => True := by
  unfold Crt.code
  refine RelCT.seq (R := Two VG.Proof.Bignum.X86_64.CC3) (RelCT.block_append (RelCT.seq (R := Two VG.Proof.Bignum.X86_64.CC2) ?_ ?_)) ?_
  · rw [VG.Proof.Bignum.X86_64.crtEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.CC1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := VG.Proof.Bignum.X86_64.crtCtx_of hs.1
    have hh : WP isa (.block (([.mov .r11 (.mem { base := .rsp, disp := 88 })] : List Instr) ++
        ((Crt.entry.drop 1) ++ [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))]))) s (VG.Proof.Bignum.X86_64.CrtHeadPost s) := by
      rw [← VG.Proof.Bignum.X86_64.crtEntry_split]; exact VG.Proof.Bignum.X86_64.crtHead_ok c
    have e10 : s.gpr .rsp + BitVec.ofInt 64 88 = stackArgAddr s 10 := rfl
    have hB' : s.mem.readW (stackArgAddr s 10) 64 = stackArg s 10 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 10)
      (by xrun [State.ea, e10, c.ha 10 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans hs.2.2.1, (k.gpr (by decide)).trans hs.2.1, hw⟩
  -- The modulus' check.
  · refine two_piece [.rdx, .rcx] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.rdx, h₂.rdx, c₁.2.2.2.2.2.2.1, c₂.2.2.2.2.2.2.1]
      · rw [h₁.rcx, h₂.rcx, c₁.2.2.2.2.1, c₂.2.2.2.2.1]) (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := VG.Proof.Bignum.X86_64.crtCtx_of hs.1
    have hnb := c.hnb.congrK h.inScr h.keep
    obtain ⟨-, -, -, -, hk, -, -, -, -, -, -, -, -, -, -, hn⟩ := id hs
    refine WP.mono (invalid_ok h.rdx h.rcx c.hk1 c.hk2 (VG.Proof.Bignum.X86_64.bytesAt_length _ _ _) (fun i hi => hnb.rd i (by
      rw [VG.Proof.Bignum.X86_64.bytesAt_length]; exact hi)) (fun i hi => hnb.val i _)) fun t' ⟨hz, hm, k⟩ =>
        ⟨s, t, hs, h, hm, k, ?_⟩
    rw [hz, hn, hk]
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    simp only [VG.X86_64.eval, z₁, z₂]) ?_ ?_
  · -- `fail`.
    unfold fail
    have pin : ∀ p t, (VG.Proof.Bignum.X86_64.CC3 p t ∧ isa.eval .ne t = some true) → t.gpr .rdi = p.m.B := fun p t ⟨h, _⟩ => by
      obtain ⟨_, _, _, _, _, _, hpre⟩ := VG.Proof.Bignum.X86_64.cc3_pre h
      exact hpre.rdi
    refine RelCT.seq (two_piece (Ψ := fun (p : VG.Proof.Bignum.X86_64.CCPub) t => t.gpr .rsi = p.m.op ∧
        t.gpr .rcx = BitVec.ofNat 64 p.m.k ∧ t.gpr .rdi = p.m.B) [.rdi]
      (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [pin p s₁ h₁, pin p s₂ h₂]) (by taint_decide) ?_)
      (two_taint [.rsi, .rcx, .rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
    rintro p t ⟨h, -⟩
    obtain ⟨_, _, _, _, _, _, hpre⟩ := VG.Proof.Bignum.X86_64.cc3_pre h
    have hn := hpre.scr.nowrap
    have hk1 := hpre.k1
    have hk2 := hpre.k2
    have hZq := hpre.z
    have h8 := hdr_lt_slot ((p.m.k + 7) / 8) 8 (show 31 < 32 by decide)
    have hZ : 8 * 32 ≤ p.m.Z := by unfold offQ at hZq; omega
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off p.m.B (8 * i)) 8 := fun i hi => hpre.scr.ld (by omega)
    refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t' => t'.gpr .rsi = p.m.op ∧
        t'.gpr .rcx = BitVec.ofNat 64 p.m.k) (by
      xrun [State.ea, hdr, hpre.rdi, hdrOff, hl sOut (by decide), hl sK (by decide), hpre.hO, hpre.hK]) rfl)
      fun t' ⟨⟨hsi, hcx⟩, k'⟩ => ⟨hsi, hcx, (k'.gpr (by decide)).trans hpre.rdi⟩
  · -- `main`.
    have toM : ∀ p t, VG.Proof.Bignum.X86_64.CC3 p t ∧ isa.eval .ne t = some false → VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R0 p.m t := by
      rintro p t ⟨h, he⟩
      obtain ⟨xb, pb, qb, dpb, dqb, qib, hpre⟩ := VG.Proof.Bignum.X86_64.cc3_pre h
      obtain ⟨_, _, _, _, _, _, hz⟩ := h
      have hv : Spec.Rsa.modulusValid p.m.N p.m.k = true := by
        simp only [VG.X86_64.eval, hz] at he; simpa using he
      exact ⟨t, xb, pb, qb, dpb, dqb, qib, hpre, hv, rfl⟩
    exact (VG.Proof.Bignum.X86_64.crtMain_ct M hS hC hQ hP hF).mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ =>
      ⟨p.m, toM p t₁ h₁, toM p t₂ h₂⟩) h) fun _ _ h => h

/-- The public data of a state. -/
def ccPubOf (s : State) : VG.Proof.Bignum.X86_64.CCPub :=
  ⟨⟨stackArg s 10, (stackArg s 11).toNat * 8, (s.gpr .rcx).toNat, s.gpr .rdi, s.gpr .rdx, s.gpr .r8,
    stackArg s 0, stackArg s 2, stackArg s 4, stackArg s 6, stackArg s 8, (stackArg s 1).toNat,
    (stackArg s 3).toNat, Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat⟩, s.gpr .rsp⟩

/-- `vg_rsa_private_crt` is constant time but for `n`, given that `main`'s
parts are. -/
theorem crtCode_constantTime_of (hS : SetupCT) (hC : ChecksCT) (hQ : QPhaseCT M) (hP : PPhaseCT M)
    (hF : RelCT isa (Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R5)) (seqs VG.Impl.Rsa.X86_64.Crt.finish) fun _ _ => True) :
    ConstantTime isa crtContract.pre crtContract.pub (Crt.code M.mm) := by
  refine RelCT.constantTime ((VG.Proof.Bignum.X86_64.crtCode_ct M hS hC hQ hP hF).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨VG.Proof.Bignum.X86_64.ccPubOf s₁, ?_, ?_⟩)
    fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, a0, a1, a2, a3, a4, -, a6, -, a8, -, a10, a11, hn⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, r .rsp (by decide), a10.symm, by rw [← a11]; rfl, by rw [r .rcx (by decide)]; rfl,
      r .rdi (by decide), r .rdx (by decide), r .r8 (by decide), a0.symm, a2.symm, a4.symm, a6.symm, a8.symm,
      by rw [← a1]; rfl, by rw [← a3]; rfl, hn.symm⟩

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows`. -/
section

/-!
# RSA with the CRT on x86-64: products in constant time

`zeroAccs` (`zeroAccs_ct`), and a product of an array of `p`'s workspace and
`q`'s `n` into the modulus' accumulators (`rows_ct`), which `pqProduct` and
`finish` make. `rowsHdr` loads each prime's workspace's base from the header
and then its header through it: the taint analysis, to which memory is
secret, checks it in three parts, each from the registers that correctness
pins after the one before.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-- `acc := 0` over `2 w + 2` words. -/
theorem zeroAccs_ct : RelCT isa (Two GoodW) (seqs Crt.zeroAccs) fun _ _ => True := by
  unfold Crt.zeroAccs
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .r8 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aAcc) ∧
      t.gpr .rbx = BitVec.ofNat 64 L.w) [.rdi] pins_goodW (by taint_decide) fun L s h => ?_)
    (two_taint [.r8, .rbx] (pins_of (fun L r => if r = .r8 then VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aAcc) else BitVec.ofNat 64 L.w)
      fun L s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) (by taint_decide))
  have hl := h.hl
  obtain ⟨_, hg, -⟩ := h
  exact WP.mono (WP.keep [.r8, .rbx] (Q := fun t => t.gpr .r8 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aAcc) ∧
      t.gpr .rbx = BitVec.ofNat 64 L.w)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr aAcc) (by decide), hl sW (by decide),
      hg.hdr.harr aAcc (by decide), hg.hdr.hw]) rfl) fun _ h => h.1

/-- The public data of a product: `n`'s workspace and the primes'. -/
structure RowsPub where
  B : Addr
  Z : Nat
  w : Nat
  op : Nat
  oq : Nat
  wp : Nat
  wq : Nat

/-- What `rowsHdr ja` loads (`rowsHdr_ok`'s hypotheses), with `[ja]` at its
base. -/
def RowsPre (ja : Nat) (p : VG.Proof.Bignum.X86_64.RowsPub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.Scr s p.B p.Z ∧ s.gpr .rdi = p.B ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sArr aAcc) = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aAcc) ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * Crt.sWsP) = VG.Proof.Bignum.X86_64.off p.B p.op ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * Crt.sWsQ) = VG.Proof.Bignum.X86_64.off p.B p.oq ∧
    VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off p.B p.op) (8 * sW) = BitVec.ofNat 64 p.wp ∧
    VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off p.B p.oq) (8 * sW) = BitVec.ofNat 64 p.wq ∧
    VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off p.B p.op) (8 * sArr ja) = VG.Proof.Bignum.X86_64.off p.B (p.op + VG.Proof.Bignum.X86_64.slot p.wp ja) ∧
    VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off p.B p.oq) (8 * sArr aN) = VG.Proof.Bignum.X86_64.off p.B (p.oq + VG.Proof.Bignum.X86_64.slot p.wq aN) ∧ ja < 8 ∧
    VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.op ∧ p.op + VG.Proof.Bignum.X86_64.slot p.wp 8 ≤ p.oq ∧ p.oq + VG.Proof.Bignum.X86_64.slot p.wq 8 ≤ p.Z

theorem rowsHdr_split (ja : Nat) : rowsHdr ja = ([.mov .rax (.mem (hdr Crt.sWsP))] : List Instr) ++
    (([.mov .r11 (.mem (Crt.ws .rax (sArr ja))), .mov .r10 (.mem (Crt.ws .rax sW)),
      .mov .rax (.mem (hdr Crt.sWsQ))] : List Instr) ++
    ([.mov .r9 (.mem (Crt.ws .rax (sArr aN))), .mov .r12 (.mem (Crt.ws .rax sW)),
      .mov .r8 (.mem (hdr (sArr aAcc)))] : List Instr)) := rfl

/-- The header words the parts of `rowsHdr` read. -/
theorem RowsPre.hl {ja : Nat} {p : VG.Proof.Bignum.X86_64.RowsPub} {s : State} (h : VG.Proof.Bignum.X86_64.RowsPre ja p s) :
    (∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off p.B (8 * i)) 8) ∧
      (∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.op) (8 * i)) 8) ∧
      ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.oq) (8 * i)) 8 := by
  obtain ⟨hs, -, -, -, -, -, -, -, -, -, hlo, hop, hoq⟩ := h
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have h8p := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have h8q := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  exact ⟨fun i hi => hs.ld (by omega),
    fun i hi => (hs.sub (o := p.op) (n := VG.Proof.Bignum.X86_64.slot p.wp 8) (by omega) (by omega)).ld (by omega),
    fun i hi => (hs.sub (o := p.oq) (n := VG.Proof.Bignum.X86_64.slot p.wq 8) (by omega) (by omega)).ld (by omega)⟩

theorem RowsPre.keep {ja : Nat} {p : VG.Proof.Bignum.X86_64.RowsPub} {s t : State} (h : VG.Proof.Bignum.X86_64.RowsPre ja p s) (hm : t.mem = s.mem)
    {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t) (hr : .rdi ∉ regs) : VG.Proof.Bignum.X86_64.RowsPre ja p t := by
  obtain ⟨hs, hdi, a, b, c, d, e, f, g, rest⟩ := h
  exact ⟨hs.congr k.2.2, (k.gpr hr).trans hdi, hm ▸ a, hm ▸ b, hm ▸ c, hm ▸ d, hm ▸ e, hm ▸ f, hm ▸ g, rest⟩

/-- `rowsHdr ja` and `mulRows`, given that the taint analysis checks the
part of `rowsHdr` that reads `p`'s workspace (`by taint_decide` for a given
`ja`). -/
theorem rows_ct {ja : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi, .rax]) (.block ([.mov .r11 (.mem (Crt.ws .rax (sArr ja))),
      .mov .r10 (.mem (Crt.ws .rax sW)), .mov .rax (.mem (hdr Crt.sWsQ))] : List Instr)) hc).isSome = true) :
    RelCT isa (Two (VG.Proof.Bignum.X86_64.RowsPre ja)) (.seq (.block (rowsHdr ja)) Crt.mulRows) fun _ _ => True := by
  rw [VG.Proof.Bignum.X86_64.rowsHdr_split]
  refine RelCT.seq (R := Two fun (p : VG.Proof.Bignum.X86_64.RowsPub) t => t.gpr .r11 = VG.Proof.Bignum.X86_64.off p.B (p.op + VG.Proof.Bignum.X86_64.slot p.wp ja) ∧
      t.gpr .r10 = BitVec.ofNat 64 p.wp ∧ t.gpr .r9 = VG.Proof.Bignum.X86_64.off p.B (p.oq + VG.Proof.Bignum.X86_64.slot p.wq aN) ∧
      t.gpr .r12 = BitVec.ofNat 64 p.wq ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aAcc)) (RelCT.block_append (RelCT.seq (R := Two fun (p : VG.Proof.Bignum.X86_64.RowsPub) t => VG.Proof.Bignum.X86_64.RowsPre ja p t ∧
      t.gpr .rax = VG.Proof.Bignum.X86_64.off p.B p.op) ?_ (RelCT.block_append (RelCT.seq (R := Two fun (p : VG.Proof.Bignum.X86_64.RowsPub) t => VG.Proof.Bignum.X86_64.RowsPre ja p t ∧
      t.gpr .rax = VG.Proof.Bignum.X86_64.off p.B p.oq ∧ t.gpr .r11 = VG.Proof.Bignum.X86_64.off p.B (p.op + VG.Proof.Bignum.X86_64.slot p.wp ja) ∧
      t.gpr .r10 = BitVec.ofNat 64 p.wp) ?_ ?_)))) ?_
  · refine two_piece [.rdi] (pins_of (fun p _ => p.B) fun p s h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.2.1) (by taint_decide) fun p s h => ?_
    obtain ⟨hl, -, -⟩ := h.hl
    obtain ⟨-, hdi, -, hp, -⟩ := id h
    exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = VG.Proof.Bignum.X86_64.off p.B p.op ∧ t.mem = s.mem)
      (by xrun [State.ea, hdr, hdi, hdrOff, hl Crt.sWsP (by decide), hp]) rfl)
      fun t ⟨⟨hax, hm⟩, k⟩ => ⟨h.keep hm k (by decide), hax⟩
  · refine two_piece [.rdi, .rax] (pins_of (fun p r => if r = .rdi then p.B else VG.Proof.Bignum.X86_64.off p.B p.op)
      fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.2.1
        · exact h.2) hT fun p s h => ?_
    obtain ⟨h, hax⟩ := h
    obtain ⟨hl, hlp, -⟩ := h.hl
    obtain ⟨-, hdi, -, -, hq, hpw, -, hpa, -, hja, -⟩ := id h
    exact WP.mono (WP.keep [.r11, .r10, .rax] (Q := fun t => t.gpr .rax = VG.Proof.Bignum.X86_64.off p.B p.oq ∧
        t.gpr .r11 = VG.Proof.Bignum.X86_64.off p.B (p.op + VG.Proof.Bignum.X86_64.slot p.wp ja) ∧ t.gpr .r10 = BitVec.ofNat 64 p.wp ∧ t.mem = s.mem)
      (by xrun [State.ea, hdr, Crt.ws, hdi, hax, hdrOff, hl Crt.sWsQ (by decide),
        hlp (sArr ja) (by unfold sArr; omega), hlp sW (by decide), hq, hpw, hpa]) rfl)
      fun t ⟨⟨hax', h11, h10, hm⟩, k⟩ => ⟨h.keep hm k (by decide), hax', h11, h10⟩
  · refine two_piece (Ψ := fun (p : VG.Proof.Bignum.X86_64.RowsPub) t => t.gpr .r11 = VG.Proof.Bignum.X86_64.off p.B (p.op + VG.Proof.Bignum.X86_64.slot p.wp ja) ∧
        t.gpr .r10 = BitVec.ofNat 64 p.wp ∧ t.gpr .r9 = VG.Proof.Bignum.X86_64.off p.B (p.oq + VG.Proof.Bignum.X86_64.slot p.wq aN) ∧
        t.gpr .r12 = BitVec.ofNat 64 p.wq ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aAcc)) [.rdi, .rax]
      (pins_of (fun p r => if r = .rdi then p.B else VG.Proof.Bignum.X86_64.off p.B p.oq) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.2.1
        · exact h.2.1) (by taint_decide) fun p s h => ?_
    obtain ⟨h, hax, h11, h10⟩ := h
    obtain ⟨hl, -, hlq⟩ := h.hl
    obtain ⟨-, hdi, hacc, -, -, -, hqw, -, hqa, -⟩ := h
    exact WP.mono (WP.keep [.r9, .r12, .r8] (Q := fun t => t.gpr .r9 = VG.Proof.Bignum.X86_64.off p.B (p.oq + VG.Proof.Bignum.X86_64.slot p.wq aN) ∧
        t.gpr .r12 = BitVec.ofNat 64 p.wq ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aAcc))
      (by xrun [State.ea, hdr, Crt.ws, hdi, hax, hdrOff, hl (sArr aAcc) (by decide),
        hlq (sArr aN) (by decide), hlq sW (by decide), hqa, hqw, hacc]) rfl)
      fun t ⟨⟨h9, h12, h8⟩, k⟩ => ⟨(k.gpr (by decide)).trans h11, (k.gpr (by decide)).trans h10, h9, h12, h8⟩
  exact two_taint [.r11, .r10, .r9, .r12, .r8] (pins_of (fun p r => if r = .r11 then VG.Proof.Bignum.X86_64.off p.B (p.op + VG.Proof.Bignum.X86_64.slot p.wp ja)
      else if r = .r10 then BitVec.ofNat 64 p.wp else if r = .r9 then VG.Proof.Bignum.X86_64.off p.B (p.oq + VG.Proof.Bignum.X86_64.slot p.wq aN)
      else if r = .r12 then BitVec.ofNat 64 p.wq else VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aAcc)) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2.1
        · exact h.2.2.2.2) (by taint_decide)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCTFin`. -/
section

/-!
# RSA with the CRT on x86-64: the result in constant time

`finish` sums `m_q + q h` into the modulus' accumulators (`finishSum`), whose
parts keep the header and the primes' workspaces (`FA`), and stores it masked
(`outArr_ct`): `crtFinish_ct`.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-- What `finishSum`'s parts need, which they keep: the workspaces, `m_q`'s
base and the sizes. -/
def FA (p : VG.Proof.Bignum.X86_64.RowsPub) (s : State) : Prop :=
  GoodW ⟨p.B, p.Z, p.w⟩ s ∧ VG.Proof.Bignum.X86_64.RowsPre aY p s ∧
    VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off p.B p.oq) (8 * sArr aY) = VG.Proof.Bignum.X86_64.off p.B (p.oq + VG.Proof.Bignum.X86_64.slot p.wq aY) ∧ 1 ≤ p.wq ∧ p.wq ≤ p.w ∧
    p.w < 2 ^ 29

/-- `FA` after changes to the modulus' accumulators only. -/
theorem FA.outside {p : VG.Proof.Bignum.X86_64.RowsPub} {s t : State} (h : VG.Proof.Bignum.X86_64.FA p s) {n : Nat} (ho : VG.Proof.Bignum.X86_64.Outside p.B (VG.Proof.Bignum.X86_64.slot p.w aAcc) n s.mem t.mem)
    (hn : n ≤ 8 * (2 * p.w + 2)) {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs s t) (hr : .rdi ∉ regs) : VG.Proof.Bignum.X86_64.FA p t := by
  obtain ⟨⟨minv, hg, hZ⟩, ⟨hs, hdi, hacc, hp, hq, hpw, hqw, hpa, hqa, hja, hlo, hop, hoq⟩, hqy, hwq, hwq', hw⟩ := h
  have hZ' : VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.Z := hZ
  have hnw := hs.nowrap
  have eW : sW = 6 := rfl
  have eN : sArr aN = 8 := rfl
  have eY : sArr aY = 14 := rfl
  have hA := accs_le p.w
  have hh : ∀ i < 32, VG.Proof.Bignum.X86_64.word t.mem p.B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem p.B (8 * i) := fun i hi =>
    ho.word (Or.inl (by have := hdr_lt_slot p.w aAcc hi; omega)) (by omega)
  have hab : ∀ {o d : Nat}, VG.Proof.Bignum.X86_64.slot p.w 8 ≤ o → o + d + 8 ≤ 2 ^ 64 → VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off p.B o) d = VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off p.B o) d :=
    fun h1 h2 => word_above ho (by omega) h2
  have h8p := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have h8q := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  exact ⟨⟨minv, ⟨hg.scr.congr k.2.2, (k.gpr hr).trans hg.rdi, hg.hdr.of_outside ho (by
      unfold VG.Proof.Bignum.X86_64.slot; omega)⟩, hZ⟩,
    ⟨hs.congr k.2.2, (k.gpr hr).trans hdi, (hh _ (by decide)).trans hacc, (hh _ (by decide)).trans hp,
      (hh _ (by decide)).trans hq, (hab hlo (by omega)).trans hpw, (hab (by omega) (by omega)).trans hqw,
      (hab hlo (by unfold sArr; omega)).trans hpa, (hab (by omega) (by omega)).trans hqa, hja, hlo, hop, hoq⟩,
    (hab (by omega) (by omega)).trans hqy, hwq, hwq', hw⟩

/-- `finishSum`'s copy of `m_q`, in two parts: `q`'s workspace's base, then
its header through it. -/
theorem finishCopy_split : finishCopy = ([.mov .rax (.mem (hdr Crt.sWsQ))] : List Instr) ++
    ([.mov .rsi (.mem (Crt.ws .rax (sArr aY))), .mov .r12 (.mem (Crt.ws .rax sW)),
      .mov .rbx (.mem (hdr (sArr aAcc)))] : List Instr) := rfl

/-- After the copy's loads. -/
def FC (p : VG.Proof.Bignum.X86_64.RowsPub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.FA p s ∧ s.gpr .rsi = VG.Proof.Bignum.X86_64.off p.B (p.oq + VG.Proof.Bignum.X86_64.slot p.wq aY) ∧ s.gpr .r12 = BitVec.ofNat 64 p.wq ∧
    s.gpr .rbx = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aAcc)

/-- `finishSum` leaks the same in runs that agree on the workspaces. -/
theorem finSum_ct : RelCT isa (Two VG.Proof.Bignum.X86_64.FA) (seqs finishSum) fun _ _ => True := by
  unfold finishSum
  refine RelCT.seqs_append (by simp [Crt.zeroAccs]) (by simp) (RelCT.seq (R := Two VG.Proof.Bignum.X86_64.FA) ?_ ?_)
  · refine two_post (two_map (fun p : VG.Proof.Bignum.X86_64.RowsPub => (⟨p.B, p.Z, p.w⟩ : Ws)) (fun _ _ h => h.1) VG.Proof.Bignum.X86_64.zeroAccs_ct)
      fun p s h => ?_
    obtain ⟨⟨minv, hg, hZ⟩, -, -, -, -, hw⟩ := id h
    exact WP.mono (zeroAccs_ok hg hZ (show p.w < 2 ^ 30 by omega)) fun t ⟨_, ho, k⟩ =>
      h.outside ho (le_refl _) k (by decide)
  simp only [seqs]
  refine RelCT.seq (R := Two VG.Proof.Bignum.X86_64.FC) ?_ (RelCT.seq (R := Two VG.Proof.Bignum.X86_64.FA) ?_
    (two_map id (fun _ _ h => h.2.1) (VG.Proof.Bignum.X86_64.rows_ct (ja := aY) (by taint_decide))))
  · rw [VG.Proof.Bignum.X86_64.finishCopy_split]
    refine RelCT.block_append (RelCT.seq (R := Two fun (p : VG.Proof.Bignum.X86_64.RowsPub) t => VG.Proof.Bignum.X86_64.FA p t ∧ t.gpr .rax = VG.Proof.Bignum.X86_64.off p.B p.oq)
      (two_piece [.rdi] (pins_of (fun p _ => p.B) fun p s h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.2.1.2.1) (by taint_decide) fun p s h => ?_)
      (two_piece [.rdi, .rax] (pins_of (fun p r => if r = .rdi then p.B else VG.Proof.Bignum.X86_64.off p.B p.oq) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.2.1.2.1
        · exact h.2) (by taint_decide) fun p s h => ?_))
    · obtain ⟨hl, -, -⟩ := h.2.1.hl
      obtain ⟨-, ⟨-, hdi, -, -, hq, -⟩, -⟩ := id h
      exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = VG.Proof.Bignum.X86_64.off p.B p.oq ∧ t.mem = s.mem)
        (by xrun [State.ea, hdr, hdi, hdrOff, hl Crt.sWsQ (by decide), hq]) rfl)
        fun t ⟨⟨hax, hm⟩, k⟩ => ⟨h.outside (n := 0) (by rw [hm]; exact Outside.refl _ _ _ _) (by omega) k
          (by decide), hax⟩
    · obtain ⟨h, hax⟩ := h
      obtain ⟨hl, -, hlq⟩ := h.2.1.hl
      obtain ⟨-, ⟨-, hdi, hacc, -, -, -, hqw, -⟩, hqy, -⟩ := id h
      exact WP.mono (WP.keep [.rsi, .r12, .rbx] (Q := fun t => t.gpr .rsi = VG.Proof.Bignum.X86_64.off p.B (p.oq + VG.Proof.Bignum.X86_64.slot p.wq aY) ∧
          t.gpr .r12 = BitVec.ofNat 64 p.wq ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aAcc) ∧ t.mem = s.mem)
        (by xrun [State.ea, hdr, Crt.ws, hdi, hax, hdrOff, hl (sArr aAcc) (by decide),
          hlq (sArr aY) (by decide), hlq sW (by decide), hqy, hqw, hacc]) rfl)
        fun t ⟨⟨hsi, h12, hbx, hm⟩, k⟩ => ⟨h.outside (n := 0) (by rw [hm]; exact Outside.refl _ _ _ _) (by omega) k
          (by decide), hsi, h12, hbx⟩
  · refine two_post (two_taint [.rsi, .rbx, .r12] (pins_of (fun p r => if r = .rsi then VG.Proof.Bignum.X86_64.off p.B (p.oq + VG.Proof.Bignum.X86_64.slot p.wq aY)
        else if r = .rbx then VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w aAcc) else BitVec.ofNat 64 p.wq) fun p s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.2.1
          · exact h.2.2.2
          · exact h.2.2.1) (by taint_decide)) fun p s h => ?_
    obtain ⟨hf, hsi, h12, hbx⟩ := h
    obtain ⟨-, ⟨hs, -, -, -, -, -, -, -, -, -, hlo, hop, hoq⟩, -, hwq, hwq', hw⟩ := id hf
    have hn := hs.nowrap
    have hA := accs_le p.w
    have hqY := slot_le (w := p.wq) (show aY < 8 by decide)
    refine WP.mono (copyWords_ok hsi hbx h12 hwq (by omega) (by omega)
      (fun j hj => hs.ld (by omega)) (fun j hj => hs.st (by omega))
      (fun j hj b hb => by rw [VG.Proof.Bignum.X86_64.ofs_off p.B (by omega)]; omega)) fun t ⟨_, _, ho, k⟩ =>
        hf.outside ho (by omega) k (by decide)

/-- `finishSum`'s hypotheses after `p`'s phase. -/
theorem stage5_fa {p : VG.Proof.Bignum.X86_64.CrtPub} {t : State} (h : VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R5 p t) :
    VG.Proof.Bignum.X86_64.FA ⟨p.B, p.Z, p.w, offP p.w, offQ p.w p.pl, wsWords p.pl, wsWords p.ql⟩ t := by
  unfold CrtPub.w
  obtain ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, minv, mp, mq, hr⟩ := h
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hZq := h.z
  have hP8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords p.pl) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hQ8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords p.ql) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hwq2 : 2 ≤ wsWords p.ql := by unfold wsWords; omega
  have hwq := wsWords_le (len := p.ql) (w := (p.k + 7) / 8) (by omega) (by omega)
  have hZ : VG.Proof.Bignum.X86_64.slot ((p.k + 7) / 8) 8 ≤ p.Z := by unfold offQ at hZq; omega
  unfold VG.Proof.Bignum.X86_64.FA VG.Proof.Bignum.X86_64.RowsPre
  dsimp only
  exact ⟨⟨minv, hr.good, hZ⟩, ⟨hr.good.scr, hr.good.rdi, hr.good.hdr.harr aAcc (by decide), hr.wsP, hr.wsQ,
      hr.pws.hdr.hw, hr.qws.hdr.hw, by rw [hr.pws.hdr.harr _ (by decide), off_off],
      by rw [hr.qws.hdr.harr _ (by decide), off_off], by decide, le_refl _, by unfold offQ offP; omega, by omega⟩,
    by rw [hr.qws.hdr.harr _ (by decide), off_off], by omega, hwq, by omega⟩

/-- `finishSum` leaves what the store needs. -/
theorem finSum_out {p : VG.Proof.Bignum.X86_64.CrtPub} {t₂ : State} (h : VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R5 p t₂) :
    WP isa (seqs finishSum) t₂ (VG.Proof.Bignum.X86_64.OPreW ⟨p.B, p.Z, p.w, p.k, p.op⟩) := by
  have hfa := VG.Proof.Bignum.X86_64.stage5_fa h
  obtain ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, minv, mp, mq, hr⟩ := h
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, hlo, hop, hoq⟩, -, hwq, hwq', hw⟩ := hfa
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hpl1 := h.pl1
  have hZq := h.z
  have hn := hr.good.scr.nowrap
  have hwp2 : 2 ≤ wsWords p.pl := by unfold wsWords; omega
  have hwp := wsWords_le (len := p.pl) (w := (p.k + 7) / 8) (by omega) (by omega)
  have hZ : VG.Proof.Bignum.X86_64.slot ((p.k + 7) / 8) 8 ≤ p.Z := by unfold offQ at hZq; omega
  refine WP.mono (finishSum_ok hr.good (by unfold CrtPub.w at hw; omega) hr.wsP hr.wsQ hr.pws.hdr.hw hr.qws.hdr.hw
    (by rw [hr.pws.hdr.harr _ (by decide), off_off]) (by rw [hr.qws.hdr.harr _ (by decide), off_off])
    (by rw [hr.qws.hdr.harr _ (by decide), off_off]) hlo (by unfold offQ offP; omega) hZq (by omega) hwp (by omega) hwq')
    fun t₃ ⟨_, ho₃, k₃⟩ => ?_
  have hacc := accs_le ((p.k + 7) / 8)
  have hb₃ : ∀ i < 32, VG.Proof.Bignum.X86_64.word t₃.mem p.B (8 * i) = VG.Proof.Bignum.X86_64.word t₂.mem p.B (8 * i) := fun i hi =>
    ho₃.word (Or.inl (by have := hdr_lt_slot ((p.k + 7) / 8) Public.aAcc hi; omega)) (by omega)
  have hfx : ∀ i < 32, hFixed i = true → VG.Proof.Bignum.X86_64.word t₃.mem p.B (8 * i) = VG.Proof.Bignum.X86_64.word σ.mem p.B (8 * i) := fun i hi hf => by
    rw [hb₃ i hi]; exact hr.hfix i hi hf
  have k03 := hr.keep.trans k₃
  unfold VG.Proof.Bignum.X86_64.OPreW OPre
  dsimp only
  exact ⟨minv, p.mask xb pb qb qib, ⟨hr.good.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hr.good.rdi,
      ⟨(hb₃ _ (by decide)).trans hr.good.hdr.hw, (hb₃ _ (by decide)).trans hr.good.hdr.hminv,
        fun j hj => (hb₃ _ (by unfold sArr; omega)).trans (hr.good.hdr.harr j hj)⟩⟩, rfl, hZ, by omega,
    by omega, by rw [hfx _ (by decide) (by decide)]; exact h.hO, by rw [hfx _ (by decide) (by decide)]; exact h.hK,
    by rw [hb₃ _ (by decide)]; exact hr.msk, fun j hj => by rw [k03.2.2]; exact h.out j hj, h.outSep⟩

/-- `finish` leaks the same in runs that agree on the public data. -/
theorem crtFinish_ct : RelCT isa (Two (VG.Proof.Bignum.X86_64.Stage VG.Proof.Bignum.X86_64.R5)) (seqs Crt.finish) fun _ _ => True := by
  rw [VG.Proof.Bignum.X86_64.finish_out]
  refine RelCT.seqs_append (by simp [finishSum, Crt.zeroAccs]) (by simp [outStepsArr])
    (RelCT.seq (R := Two VG.Proof.Bignum.X86_64.OPreW) ?_ (VG.Proof.Bignum.X86_64.outArr_ct (j := Public.aAcc) (by decide) (by taint_decide)))
  refine (two_post (Ψ := fun (p : VG.Proof.Bignum.X86_64.CrtPub) t => VG.Proof.Bignum.X86_64.OPreW ⟨p.B, p.Z, p.w, p.k, p.op⟩ t)
    (two_map (fun p : VG.Proof.Bignum.X86_64.CrtPub => (⟨p.B, p.Z, p.w, offP p.w, offQ p.w p.pl, wsWords p.pl, wsWords p.ql⟩ : VG.Proof.Bignum.X86_64.RowsPub))
      (fun _ _ h => VG.Proof.Bignum.X86_64.stage5_fa h) VG.Proof.Bignum.X86_64.finSum_ct) fun p t h => VG.Proof.Bignum.X86_64.finSum_out h).mono (fun _ _ h => h)
    fun _ _ h => two_bind (fun (p : VG.Proof.Bignum.X86_64.CrtPub) _ _ h₁ h₂ => ⟨(⟨p.B, p.Z, p.w, p.k, p.op⟩ : VG.Proof.Bignum.X86_64.OPubW), h₁, h₂⟩) h

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPH`. -/
section

/-!
# RSA with the CRT on x86-64: constant time, `h = (m_p - m_q) qInv mod p`

`hSteps` (`hPart_ok`) is constant time (`h_ct`) for a predicate (`H0`) that
carries, before each piece, its claim's hypotheses and what correctness
gives after it; `h_chain` proves it from `hPart_ok`'s hypotheses, as
`hPart_ok` runs the pieces.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The public data of `hSteps`: the modulus' workspace, `p`'s, and `qInv`'s
pointer and length. -/
structure HPub where
  B : Addr
  Z : Nat
  w : Nat
  o : Nat
  wx : Nat
  qp : Addr
  len : Nat

/-- `p`'s workspace. -/
abbrev HPub.pw (p : VG.Proof.Bignum.X86_64.HPub) : Ws := ⟨VG.Proof.Bignum.X86_64.off p.B p.o, VG.Proof.Bignum.X86_64.slot p.wx 8, p.wx⟩

/-- `p`'s workspace, as `redc`'s and `loadArr`'s claims take it. -/
abbrev HPub.x (p : VG.Proof.Bignum.X86_64.HPub) : XPub := ⟨p.B, p.Z, p.o, p.w, p.wx⟩

/-- `qInv`, as `loadArr`'s claim takes it. -/
abbrev HPub.q (p : VG.Proof.Bignum.X86_64.HPub) : BPub := ⟨p.x, p.qp, p.len⟩

/-- Before the way back to the modulus' workspace. -/
def H6 (p : VG.Proof.Bignum.X86_64.HPub) (s : State) : Prop := s.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B p.o

/-- Before `h := T qInv R⁻¹`. -/
def H5 (M : Mont) (p : VG.Proof.Bignum.X86_64.HPub) (s : State) : Prop :=
  GoodW p.pw s ∧ WP isa (M.mm Public.aY aT aChunk) s (VG.Proof.Bignum.X86_64.H6 p)

/-- Before `qInv`'s mask. -/
def H4 (M : Mont) (p : VG.Proof.Bignum.X86_64.HPub) (s : State) : Prop :=
  GoodW p.pw s ∧ WP isa (seqs (maskArr aChunk)) s (VG.Proof.Bignum.X86_64.H5 M p)

/-- Before `qInv`'s load. -/
def H3 (M : Mont) (p : VG.Proof.Bignum.X86_64.HPub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.LPre aChunk sQinv sPlen p.q s ∧ WP isa (seqs (loadArr aChunk sQinv sPlen)) s (VG.Proof.Bignum.X86_64.H4 M p)

/-- Before `T := m_p - m_q`. -/
def H2 (M : Mont) (p : VG.Proof.Bignum.X86_64.HPub) (s : State) : Prop :=
  SmPre p.pw s ∧ WP isa (seqs (subModArr aT Public.aY aXc)) s (VG.Proof.Bignum.X86_64.H3 M p)

/-- Before `m_q R_p` into `p`'s `X_c`. -/
def H1 (M : Mont) (p : VG.Proof.Bignum.X86_64.HPub) (s : State) : Prop :=
  RPre Public.aX p.x s ∧ WP isa (seqs (redc M.mm Public.aX)) s (VG.Proof.Bignum.X86_64.H2 M p)

/-- Before `hSteps`. -/
def H0 (M : Mont) (p : VG.Proof.Bignum.X86_64.HPub) (s : State) : Prop :=
  s.gpr .rdi = p.B ∧ WP isa (.block [.mov .rdi (.mem (hdr sWsP))]) s (VG.Proof.Bignum.X86_64.H1 M p)

/-- `hSteps` after its `redc` is constant time. -/
theorem h2_ct (M : Mont) (hL : LoadCT aChunk sQinv sPlen) :
    RelCT isa (Two (VG.Proof.Bignum.X86_64.H2 M)) (seqs (subModArr aT Public.aY aXc ++ (loadArr aChunk sQinv sPlen ++ (maskArr aChunk ++
      [M.mm Public.aY aT aChunk, .block [leave]])))) fun _ _ => True := by
  refine ct_steps (by simp [subModArr]) (by simp [loadArr]) HPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2)
    subModArr_ct ?_
  refine ct_steps (by simp [loadArr]) (by simp [maskArr]) HPub.q (fun _ _ h => h.1) (fun _ _ h => h.2) hL ?_
  refine ct_steps (by simp [maskArr]) (by simp) HPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (maskArr_ct (by decide) (by taint_decide)) ?_
  exact ct_step HPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2) (M.ct (by unfold MmUse; decide))
    (two_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [show s₁.gpr .rdi = _ from h₁, h₂]) (by taint_decide))

/-- `hSteps` is constant time. -/
theorem h_ct (M : Mont) (hR : RedcCT M Public.aX) (hL : LoadCT aChunk sQinv sPlen) :
    RelCT isa (Two (VG.Proof.Bignum.X86_64.H0 M)) (seqs (hSteps M.mm)) fun _ _ => True := by
  simp only [hSteps, List.append_assoc]
  refine RelCT.seqs_app (by simp) (by simp [redc]) (ct_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) (by taint_decide) (fun _ _ h => h.2) ?_)
  exact ct_steps (by simp [redc]) (by simp [subModArr]) HPub.x (fun _ _ h => h.1) (fun _ _ h => h.2) hR
    (VG.Proof.Bignum.X86_64.h2_ct M hL)

/-- `hTail_ok`'s hypotheses give `H2`. -/
theorem h2_chain (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mx : BitVec 64} {X o wx : Nat}
    {qp : Addr} {qib : List Byte} {c : Bool}
    (hc : SubCtx s B Z o w wx mx) (hX : XVals s B o wx mx X) (hX1 : 1 < X) (hw28 : w < 2 ^ 28) (hwx2 : 2 ≤ wx)
    (hwx : wx ≤ w) (hyl : wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx < X)
    (hlt : wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aXc) wx < X) (hmask : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask c)
    (hqp : VG.Proof.Bignum.X86_64.word s.mem B (8 * sQinv) = qp) (hql : VG.Proof.Bignum.X86_64.word s.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length)
    (hqs : Src s B Z qp qib) (hq1 : 1 ≤ qib.length) (hq2 : qib.length < 2 ^ 31) (hqw : (qib.length + 7) / 8 ≤ wx)
    (hqi : c = true → Spec.Rsa.os2ip qib < X) : VG.Proof.Bignum.X86_64.H2 M ⟨B, Z, w, o, wx, qp, qib.length⟩ s := by
  have hn := hc.scr.nowrap
  have hhi := hc.hi
  have hlo := hc.lo
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  have hoL : o + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64 := by omega
  -- `T = (m_p - m_q) R_p mod p`.
  refine ⟨⟨⟨mx, hc.good, Nat.le_refl _⟩, hwx2, show wx < 2 ^ 31 by omega⟩,
    WP.mono (subModArr_ok hc.good.scr hc.rdi hc.hdr (Nat.le_refl _) hwx2 (by omega)
    (o := aT) (a := Public.aY) (b := aXc) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hX.n]; exact hyl) (by rw [hX.n]; exact hlt))
    fun s₃ ⟨_, ha₃, k₃⟩ => ?_⟩
  obtain ⟨hc₃, hX₃, fx₃⟩ := hc.of_arrays hX ha₃ (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> decide) k₃.2.2 (k₃.gpr (by decide)) (by omega)
  have hb₃ : ∀ d, d + 8 ≤ o → VG.Proof.Bignum.X86_64.word s₃.mem B d = VG.Proof.Bignum.X86_64.word s.mem B d := fun d hd => fx₃.x_below hd ho64
  have i03 : InScr B Z s.mem s₃.mem :=
    InScr.of_frm fx₃ fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega
  have hM₃ : VG.Proof.Bignum.X86_64.word s₃.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask c := by
    rw [ha₃.hslot (by decide)]; exact hmask
  -- `qInv`, masked.
  have a1 : VG.Proof.Bignum.X86_64.word s₃.mem B (8 * sQinv) = qp := by rw [hb₃ _ (by unfold sQinv sFn; omega)]; exact hqp
  have a2 : VG.Proof.Bignum.X86_64.word s₃.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length := by
    rw [hb₃ _ (by unfold sPlen sFn; omega)]; exact hql
  have a3 : Src s₃ B Z qp qib := hqs.congrK i03 k₃
  refine ⟨⟨mx, qib, hc₃, hwx2, hwx, show w < 2 ^ 30 by omega, by decide, by decide, by decide, a1, a2, rfl, a3,
      hq1, hq2, hqw⟩,
    WP.mono (primeLoad_ok hc₃ hwx2 hwx (by omega) (j := aChunk) (by decide) (sp := sQinv) (sl := sPlen)
      (by decide) (by decide) a1 a2 a3 hq1 hq2 hqw) fun s₄ ⟨hc₄, hq₄, ho₄, k₄⟩ => ?_⟩
  have hz₄ : (VG.Proof.Bignum.X86_64.off B o).toNat + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64 := by have := hc₄.good.scr.nowrap; omega
  have hX₄ := hX₃.of_outside ho₄ (by decide) (by decide) (by decide) (Nat.le_refl _) hz₄
  have hM₄ : VG.Proof.Bignum.X86_64.word s₄.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask c := by
    rw [ho₄.word (Or.inl (by have := hdr_lt_slot wx aChunk (show sMaskX < 32 by decide); omega))
      (by unfold sMaskX sFn; omega)]; exact hM₃
  refine ⟨⟨mx, hc₄.good, Nat.le_refl _⟩, WP.mono (maskArr_ok hc₄.good (Nat.le_refl _) (by omega) (by omega)
    (j := aChunk) (by decide) hM₄) fun s₅ ⟨_, hq₅, ho₅, k₅⟩ => ?_⟩
  have ho₅' : VG.Proof.Bignum.X86_64.Outside (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aChunk) (8 * (wx + 2)) s₄.mem s₅.mem :=
    ho₅.mono (Nat.le_refl _) (by omega)
  have hc₅ := hc₄.of_frm (rs := [(VG.Proof.Bignum.X86_64.slot wx aChunk, 8 * (wx + 2))]) (Frm.of_outside ho₅' (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := slot_le (w := wx) (show aChunk < 8 by decide)
    have := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
    simp only; omega) k₅.2.2 (k₅.gpr (by decide))
  have hX₅ := hX₄.of_outside ho₅' (by decide) (by decide) (by decide) (Nat.le_refl _) hz₄
  have hch : wv s₅.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx aChunk) wx < X := by
    rw [hq₅, hq₄]
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte]; omega
    · simp only [↓reduceIte]; exact hqi rfl
  -- `h = T qInv R_p⁻¹`.
  exact ⟨⟨mx, hc₅.good, Nat.le_refl _⟩, WP.mono (M.mm_ok (o := Public.aY) (a := aT) (b := aChunk) hc₅.good
    (Nat.le_refl _) hwx2 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hX₅.inv (by rw [hX₅.n]; exact hch)) fun _ h₆ => h₆.1.rdi⟩


/-- `hPart_ok`'s hypotheses give `H0`. -/
theorem h_chain (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {X o wx : Nat}
    {qp : Addr} {qib : List Byte} {c : Bool}
    (hg : VG.Proof.Bignum.X86_64.Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ o) (hhi : o + VG.Proof.Bignum.X86_64.slot wx 8 + tabBytes wx ≤ Z)
    (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hslv : VG.Proof.Bignum.X86_64.word s.mem B (8 * sWsP) = VG.Proof.Bignum.X86_64.off B o) (hws : WsAt s.mem B o wx mx)
    (hX : XVals s B o wx mx X) (hX1 : 1 < X)
    (hyl : wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx < X)
    (hmask : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask c)
    (hqp : VG.Proof.Bignum.X86_64.word s.mem B (8 * sQinv) = qp) (hql : VG.Proof.Bignum.X86_64.word s.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length)
    (hqs : Src s B Z qp qib) (hq1 : 1 ≤ qib.length) (hq2 : qib.length < 2 ^ 31) (hqw : (qib.length + 7) / 8 ≤ wx)
    (hqi : c = true → Spec.Rsa.os2ip qib < X) : VG.Proof.Bignum.X86_64.H0 M ⟨B, Z, w, o, wx, qp, qib.length⟩ s := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  have hoL : o + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64 := by omega
  refine ⟨hg.rdi, WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off B o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sWsP) (by unfold sWsP sFn; omega), hslv]) rfl)
    fun s₁ ⟨⟨hdi₁, hm₁⟩, k₁⟩ => ?_⟩
  have hc₁ : SubCtx s₁ B Z o w wx mx :=
    SubCtx.mk' (hs.congr k₁.2.2) (by rw [hm₁]; exact hg.hdr) (by rw [hm₁]; exact hws) hdi₁ hlo hhi
  have hX₁ : XVals s₁ B o wx mx X := ⟨by rw [hm₁]; exact hX.n, by rw [hm₁]; exact hX.inv, by rw [hm₁]; exact hX.one⟩
  -- `m_q R_p` into `p`'s `X_c`.
  refine ⟨⟨mx, X, hc₁, hX₁, hwx2, hwx, show w < 2 ^ 30 by omega, hX1, by decide⟩,
    WP.mono (redc_ok M hc₁ hX₁ hwx2 hwx (by omega) hX1 (j := Public.aX) (by decide))
    fun s₂ ⟨hc₂, hX₂, hlt₂, _, f₂, k₂⟩ => ?_⟩
  have fx₂ : Frm B [xRange o wx] s₁.mem s₂.mem := f₂.to_x (redcRanges_ok wx) hoL (List.mem_singleton_self _)
  have hY₂ : wv s₂.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx = wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx := by
    have rY := redcRanges_arr wx (j := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have := slot_le (w := wx) (show Public.aY < 8 by decide)
    have := hc₁.good.scr.nowrap
    rw [f₂.wv_eq (fun r hr => by have := rY r hr; omega) (by omega), hm₁]
  have hM₂ : VG.Proof.Bignum.X86_64.word s₂.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask c := by
    rw [f₂.word_eq (fun r hr => by
      simp only [redcRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      have := hdr_lt_slot wx Public.aAcc (show 31 < 32 by decide)
      have := hdr_lt_slot wx Public.aTmp (show 31 < 32 by decide)
      have := hdr_lt_slot wx aXc (show 31 < 32 by decide)
      have := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
      have := hdr_lt_slot wx aT (show 31 < 32 by decide)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [sMaskX, sSrc, sRem, sFn] <;> omega)
      (by unfold sMaskX sFn; omega), hm₁]
    exact hmask
  have hb₂ : ∀ d, d + 8 ≤ o → VG.Proof.Bignum.X86_64.word s₂.mem B d = VG.Proof.Bignum.X86_64.word s.mem B d := fun d hd => by
    rw [fx₂.x_below hd ho64, hm₁]
  have i02 : InScr B Z s.mem s₂.mem := by
    have f := fx₂
    rw [hm₁] at f
    exact InScr.of_frm f fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega
  exact VG.Proof.Bignum.X86_64.h2_chain M hc₂ hX₂ hX1 hw28 hwx2 hwx (by rw [hY₂]; exact hyl) hlt₂ hM₂
    (by rw [hb₂ _ (by unfold sQinv sFn; omega)]; exact hqp) (by rw [hb₂ _ (by unfold sPlen sFn; omega)]; exact hql)
    (hqs.congrK i02 (k₁.trans k₂)) hq1 hq2 hqw hqi

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCTP`. -/
section

/-!
# RSA with the CRT on x86-64: constant time, `p`'s phase

`pPhase` is constant time (`pPhase_ct`) given its pieces' claims: before
each piece, a predicate (`PO0` … `PO4`, then `hSteps`' `H0`) carries the
piece's hypotheses and what correctness gives after it; `o0_of` proves the
first from `PPre`, as `pPhase_ok` runs the pieces.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The modulus' workspace. -/
abbrev PPhasePub.nw (p : PPhasePub) : Ws := ⟨p.ph.B, p.ph.Z, p.ph.w⟩

/-- The public data of the phase's first part. -/
abbrev PPhasePub.u (p : PPhasePub) : UPub := ⟨p.ph.B, p.ph.Z, p.ph.w, p.ph.minv, p.ph.N, p.ph.o, p.ph.wx⟩

/-- The public data of `m_q G mod n`. -/
abbrev PPhasePub.mq (p : PPhasePub) : MqPub := ⟨p.ph.B, p.ph.Z, p.ph.w, p.oq, p.wq⟩

/-- The public data of the exponentiation. -/
abbrev PPhasePub.pw (p : PPhasePub) : BPub := ⟨⟨p.ph.B, p.ph.Z, p.ph.o, p.ph.w, p.ph.wx⟩, p.ph.ep, p.ph.len⟩

/-- The public data of `h`. -/
abbrev PPhasePub.h (p : PPhasePub) : VG.Proof.Bignum.X86_64.HPub := ⟨p.ph.B, p.ph.Z, p.ph.w, p.ph.o, p.ph.wx, p.qp, p.ph.len⟩

/-- Before the way back to the modulus' workspace. -/
def PO4 (M : Mont) (p : PPhasePub) (s : State) : Prop :=
  s.gpr .rdi = VG.Proof.Bignum.X86_64.off p.ph.B p.ph.o ∧ WP isa (.block [leave]) s (VG.Proof.Bignum.X86_64.H0 M p.h)

/-- Before the exponentiation. -/
def PO3 (M : Mont) (p : PPhasePub) (s : State) : Prop :=
  PwPre sWsP sDp sPlen p.pw s ∧ WP isa (seqs (powSteps M.mm sWsP sDp sPlen)) s (VG.Proof.Bignum.X86_64.PO4 M p)

/-- Before `c G mod N`. -/
def PO2 (M : Mont) (p : PPhasePub) (s : State) : Prop :=
  GoodW p.nw s ∧ WP isa (M.mm Public.aY Public.aXm Public.aY) s (VG.Proof.Bignum.X86_64.PO3 M p)

/-- Before `m_q G mod N`. -/
def PO1 (M : Mont) (p : PPhasePub) (s : State) : Prop :=
  Mq0 M p.mq s ∧ WP isa (seqs (mqSteps M.mm)) s (VG.Proof.Bignum.X86_64.PO2 M p)

/-- Before `pPhase`. -/
def PO0 (M : Mont) (p : PPhasePub) (s : State) : Prop :=
  UPre sWsP p.u s ∧ WP isa (seqs (unitSteps M.mm sWsP)) s (VG.Proof.Bignum.X86_64.PO1 M p)

/-- From before the exponentiation: `PO3`, as `pPhase_ok` runs the rest. -/
theorem o3_of (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64}
    {N X C o wx oq wq : Nat} {ep qp : Addr} {eb qib : List Byte} {c : Bool}
    (hg : VG.Proof.Bignum.X86_64.Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ o) (hhi : o + VG.Proof.Bignum.X86_64.slot wx 8 + tabBytes wx ≤ Z)
    (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hslv : VG.Proof.Bignum.X86_64.word s.mem B (8 * sWsP) = VG.Proof.Bignum.X86_64.off B o) (hws : WsAt s.mem B o wx mx)
    (hX : XVals s B o wx mx X) (hX1 : 1 < X) (hXodd : X % 2 = 1)
    (hcg : wv s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aY) w % N = C * 2 ^ (64 * wx * (nChunks w wx + 1)) % N)
    (hpl : wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx < X)
    (hpy : X ∣ N → wv s.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X)
    (hep : VG.Proof.Bignum.X86_64.word s.mem B (8 * sDp) = ep) (hel : VG.Proof.Bignum.X86_64.word s.mem B (8 * sPlen) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb)
    (hmask : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask c)
    (hqp : VG.Proof.Bignum.X86_64.word s.mem B (8 * sQinv) = qp) (hql : qib.length = eb.length) (hqs : Src s B Z qp qib)
    (hqw : (qib.length + 7) / 8 ≤ wx) (hqi : c = true → Spec.Rsa.os2ip qib < X) :
    VG.Proof.Bignum.X86_64.PO3 M ⟨⟨B, Z, w, minv, N, o, wx, ep, eb.length⟩, oq, wq, qp⟩ s := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  -- `c^dP R_p mod p`.
  refine ⟨⟨minv, mx, N, X, C, eb, hg, hw28, hlo, hhi, hwx2, hwx, by decide, hslv, hws, hX, hX1, hXodd, hcg, hpl,
      hpy, by decide, by decide, hep, hel, rfl, hL1, hL2, he⟩,
    WP.mono (powPhase_ok M hg hw28 hlo hhi hwx2 hwx (sl := sWsP) (by decide) hslv hws hX hX1 hXodd hcg hpl hpy
      (sd := sDp) (slen := sPlen) (by decide) (by decide) hep hel hL1 hL2 he)
      fun s₄ ⟨hc₄, hX₄, hlt₄, _, hM₄, fx₄, k₄⟩ => ?_⟩
  -- Back to the modulus'.
  have hl₄ : InRegions (s₄.rd ++ s₄.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B o) (8 * sLink)) 8 :=
    hc₄.good.scr.ld (by unfold sLink sFn; omega)
  refine ⟨hc₄.rdi, WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s₄.mem)
    (by xrun [leave, State.ea, hdr, hc₄.rdi, hdrOff, hl₄, hc₄.link]) rfl) fun s₅ ⟨⟨hdi₅, hm₅⟩, k₅⟩ => ?_⟩
  have fx₅ : Frm B [xRange o wx] s.mem s₅.mem := by rw [hm₅]; exact fx₄
  have k05 := k₄.trans k₅
  have hb₅ : ∀ d, d + 8 ≤ o → VG.Proof.Bignum.X86_64.word s₅.mem B d = VG.Proof.Bignum.X86_64.word s.mem B d := fun d hd => fx₅.x_below hd ho64
  have hg₅ : VG.Proof.Bignum.X86_64.Good s₅ B Z w minv := ⟨hs.congr k05.2.2, hdi₅, ⟨(hb₅ _ (by unfold sW; omega)).trans hg.hdr.hw,
    (hb₅ _ (by unfold sMinv; omega)).trans hg.hdr.hminv,
    fun j hj => (hb₅ _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega); omega)).trans
      (hg.hdr.harr j hj)⟩⟩
  have hX₅ : XVals s₅ B o wx mx X := ⟨by rw [hm₅]; exact hX₄.n, by rw [hm₅]; exact hX₄.inv, by rw [hm₅]; exact hX₄.one⟩
  have i05 : InScr B Z s.mem s₅.mem := InScr.of_frm fx₅ fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only [xRange]; omega
  -- `h`.
  have a1 : VG.Proof.Bignum.X86_64.word s₅.mem B (8 * sWsP) = VG.Proof.Bignum.X86_64.off B o := by rw [hb₅ _ (by unfold sWsP sFn; omega)]; exact hslv
  have a2 : WsAt s₅.mem B o wx mx := by rw [hm₅]; exact hc₄.ws
  have a3 : wv s₅.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx < X := by rw [hm₅]; exact hlt₄
  have a5 : VG.Proof.Bignum.X86_64.word s₅.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask c := by rw [hm₅, hM₄]; exact hmask
  have a6 : VG.Proof.Bignum.X86_64.word s₅.mem B (8 * sQinv) = qp := by rw [hb₅ _ (by unfold sQinv sFn; omega)]; exact hqp
  have a7 : VG.Proof.Bignum.X86_64.word s₅.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length := by
    rw [hb₅ _ (by unfold sPlen sFn; omega), hql]; exact hel
  have := VG.Proof.Bignum.X86_64.h_chain M hg₅ hw28 hlo hhi hwx2 hwx a1 a2 hX₅ hX1 a3 a5 a6 a7 (hqs.congrK i05 k05) (by omega)
    (by omega) hqw hqi
  rw [hql] at this
  exact this

/-- `pPhase_ok`'s hypotheses give `PO0`. -/
theorem o0_of (M : Mont) {p : PPhasePub} {s : State} (h : PPre p s) : VG.Proof.Bignum.X86_64.PO0 M p s := by
  obtain ⟨⟨B, Z, w, minv, N, o, wx, ep, len⟩, oq, wq, qp⟩ := p
  dsimp only [PPre] at h
  obtain ⟨mx, mq, X, C, eb, qib, c, hg, hw, hw28, hlo, hhi, hqhi, hwx2, hwx, hwq, hwq', hslv, hws, hslq, hwsq, hN,
    hodd, hN1, hXm, hX, hX1, hXodd, hmask, hc, hep, hel, rfl, hL1, hL2, he, hqp, hql, hqs, hqw, hqi⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hQ8 : 256 ≤ VG.Proof.Bignum.X86_64.slot wq 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hz : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by omega
  have hhi' : o + VG.Proof.Bignum.X86_64.slot wx 8 + tabBytes wx ≤ Z := by omega
  have hsub : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, r ∈ pRanges w ++ [xRange o wx]) → ∀ {m m' : Mem},
      Frm B rs m m' → Frm B (pRanges w ++ [xRange o wx]) m m' := fun h _ _ f => f.mono h
  have sgx : ∀ r ∈ gRanges w ++ [xRange o wx], r ∈ pRanges w ++ [xRange o wx] := fun r hr =>
    (List.mem_append.mp hr).elim (fun h => List.mem_append_left _ (List.mem_append_left _ h))
      (fun h => List.mem_append_right _ h)
  have sp : ∀ r ∈ pRanges w, r ∈ pRanges w ++ [xRange o wx] := fun r hr => List.mem_append_left _ hr
  have sg : ∀ r ∈ gRanges w, r ∈ pRanges w ++ [xRange o wx] := fun r hr =>
    List.mem_append_left _ (List.mem_append_left _ hr)
  have hqh : ∀ {m m' : Mem}, Frm B (pRanges w ++ [xRange o wx]) m m' → ∀ i < 32,
      VG.Proof.Bignum.X86_64.word m' (VG.Proof.Bignum.X86_64.off B oq) (8 * i) = VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B oq) (8 * i) := fun f i hi => by
    rw [word_off, word_off]; exact f.px_above hlo (by omega) (by omega)
  -- `R_p mod p`.
  refine ⟨⟨mx, X, hg, hw, hw28, hlo, hhi', hwx2, hwx, by decide, by decide, by decide, hslv, hws, hN, hodd, hN1,
      hX, hX1, hXodd⟩,
    WP.mono (unitPhase_ok M hg hw hw28 hlo hhi' hwx2 hwx (sl := sWsP) (by decide) (by decide) (by decide) hslv
      hws hN hodd hN1 hX hX1 hXodd) fun s₁ ⟨hg₁, hws₁, hX₁, hlt₁, hG₁, hpl₁, hpy₁, hM₁, f₁, k₁⟩ => ?_⟩
  have f₁' := hsub sgx f₁
  have hN₁ := hN.of_frm f₁ hlo hz (by omega)
  have hslq₁ : VG.Proof.Bignum.X86_64.word s₁.mem B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off B oq := by
    rw [f₁'.px_hdr hlo (by decide) (by decide) (by decide)]; exact hslq
  have hwsq₁ : WsAt s₁.mem B oq wq mq := hwsq.of_words fun i hi => hqh f₁' i (by omega)
  -- `m_q G mod N`.
  refine ⟨mq_chain M hg₁ hw hw28 hN₁ hslq₁ hwsq₁ (show VG.Proof.Bignum.X86_64.slot w 8 ≤ oq by omega) hqhi hwq hwq',
    WP.mono (mqPart_ok M hg₁ hw hw28 hN₁ hodd hlt₁ hG₁ hslq₁ hwsq₁ (show VG.Proof.Bignum.X86_64.slot w 8 ≤ oq by omega) hqhi hwq hwq')
    fun s₂ ⟨hg₂, _, hmq₂, hY₂, f₂, k₂⟩ => ?_⟩
  have f₂' := hsub sp f₂
  have f₀₂ := f₁'.trans f₂'
  have hN₂ : NVals s₂ B w minv N := by
    exact ⟨by rw [f₂'.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hN₁.n,
      by rw [f₂'.word_eq (fun r hr => by
        have := pxR_bound hlo r hr
        have := slot_le (w := w) (show Public.aN < 8 by decide)
        simp only [pRanges, gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        have s1 := VG.Proof.Bignum.X86_64.slot_sep (w := w) (show Public.aN ≠ Public.aAcc by decide)
        have s2 := VG.Proof.Bignum.X86_64.slot_sep (w := w) (show Public.aN ≠ Public.aTmp by decide)
        have s3 := VG.Proof.Bignum.X86_64.slot_sep (w := w) (show Public.aN ≠ Public.aY by decide)
        have s4 := VG.Proof.Bignum.X86_64.slot_sep (w := w) (show Public.aN ≠ Public.aX by decide)
        have := hdr_lt_slot w Public.aN (show 31 < 32 by decide)
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [Crt.sD, Public.sCnt, sFn] at * <;> omega)
        (by have := slot_le (w := w) (show Public.aN < 8 by decide); omega)]; exact hN₁.inv,
      by rw [f₂'.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hN₁.r2,
      by rw [f₂'.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hN₁.r2lt,
      by rw [f₂'.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hN₁.one⟩
  -- `c G mod N`.
  refine ⟨⟨minv, hg₂, show VG.Proof.Bignum.X86_64.slot w 8 ≤ Z by omega⟩,
    WP.mono (mmY_ok M hg₂ (by omega) (by omega) (by omega) (a := Public.aXm) (by decide) (by decide)
      (by decide) hN₂ (by rw [hY₂]; exact hlt₁)) fun s₃ ⟨hg₃, _, hm₃, f₃, k₃⟩ => ?_⟩
  have f₃' := hsub sg f₃
  have f₀₃ := f₀₂.trans f₃'
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hXm₂ : wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w Public.aXm) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aXm) w :=
    f₀₂.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)
  have hcg : wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w Public.aY) w % N = C * 2 ^ (64 * wx * (nChunks w wx + 1)) % N := by
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₃, Nat.mul_mod, hXm₂, hXm, hY₂, hG₁, ← Nat.mul_mod]
    congr 1; ac_rfl
  have hpo : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm B rs m m' → (∀ r ∈ rs, r ∈ pRanges w) → ∀ d,
      o ≤ d → d + 8 ≤ 2 ^ 64 → VG.Proof.Bignum.X86_64.word m' B d = VG.Proof.Bignum.X86_64.word m B d := fun f hrs d hd hd' =>
    f.word_eq (fun r hr => Or.inr (by have := pRanges_le w r (hrs r hr); omega)) hd'
  have hpw : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm B rs m m' → (∀ r ∈ rs, r ∈ pRanges w) → ∀ i < 32,
      VG.Proof.Bignum.X86_64.word m' (VG.Proof.Bignum.X86_64.off B o) (8 * i) = VG.Proof.Bignum.X86_64.word m (VG.Proof.Bignum.X86_64.off B o) (8 * i) := fun f hrs i hi => by
    rw [word_off, word_off]; exact hpo f hrs _ (by omega) (by omega)
  have sg' : ∀ r ∈ gRanges w, r ∈ pRanges w := fun r hr => List.mem_append_left _ hr
  have hpv : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm B rs m m' → (∀ r ∈ rs, r ∈ pRanges w) → ∀ d k,
      d + 8 * k ≤ VG.Proof.Bignum.X86_64.slot wx 8 → wv m' (VG.Proof.Bignum.X86_64.off B o) d k = wv m (VG.Proof.Bignum.X86_64.off B o) d k := fun f hrs d k hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hpo f hrs _ (by omega) (by omega)
  have hY8 := slot_le (w := wx) (show Public.aY < 8 by decide)
  have hpY₃ : wv s₃.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx = wv s₁.mem (VG.Proof.Bignum.X86_64.off B o) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx := by
    rw [hpv f₃ sg' _ _ (by omega), hpv f₂ (fun r h => h) _ _ (by omega)]
  have hws₃ : WsAt s₃.mem B o wx mx := hws₁.of_words fun i hi => by
    rw [hpw f₃ sg' i (by omega), hpw f₂ (fun r h => h) i (by omega)]
  have hX₃ : XVals s₃ B o wx mx X :=
    (hX₁.of_below f₂ (fun r hr => (pRanges_le w r hr).trans hlo) (by omega)).of_below f₃
      (fun r hr => (pRanges_le w r (sg' r hr)).trans hlo) (by omega)
  have i03 : InScr B Z s.mem s₃.mem := InScr.of_frm f₀₃ fun r hr => by have := pxR_bound hlo r hr; omega
  have k03 := (k₁.trans k₂).trans k₃
  have hM₃ : VG.Proof.Bignum.X86_64.word s₃.mem (VG.Proof.Bignum.X86_64.off B o) (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask c := by
    rw [hpw f₃ sg' _ (by decide), hpw f₂ (fun r h => h) _ (by decide), hM₁]; exact hmask
  exact VG.Proof.Bignum.X86_64.o3_of M hg₃ hw28 hlo hhi' hwx2 hwx (by rw [f₀₃.px_hdr hlo (by decide) (by decide) (by decide)]; exact hslv)
    hws₃ hX₃ hX1 hXodd hcg (by rw [hpY₃]; exact hpl₁) (fun hd => by rw [hpY₃]; exact hpy₁ hd)
    (by rw [f₀₃.px_hdr hlo (by decide) (by decide) (by decide)]; exact hep)
    (by rw [f₀₃.px_hdr hlo (by decide) (by decide) (by decide)]; exact hel) hL1 hL2 (he.congrK i03 k03) hM₃
    (by rw [f₀₃.px_hdr hlo (by decide) (by decide) (by decide)]; exact hqp) hql (hqs.congrK i03 k03) hqw hqi

/-- `p`'s phase is constant time, given its pieces' claims. -/
theorem pPhase_ct (M : Mont) (hU : UnitCT M sWsP) (hP : PowCT M sWsP sDp sPlen) (hRX : RedcCT M Public.aX)
    (hL : LoadCT aChunk sQinv sPlen) : PPhaseCT M := by
  unfold PPhaseCT
  refine two_map id (fun _ _ h => VG.Proof.Bignum.X86_64.o0_of M h) ?_
  rw [pPhase_eq]
  refine ct_steps (by simp [unitSteps]) (by simp [mqSteps]) PPhasePub.u (fun _ _ h => h.1) (fun _ _ h => h.2)
    hU ?_
  refine ct_steps (by simp [mqSteps]) (by simp) PPhasePub.mq (fun _ _ h => h.1) (fun _ _ h => h.2) (mq_ct M) ?_
  refine ct_steps (by simp) (by simp [powSteps]) PPhasePub.nw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (M.ct (by unfold MmUse; decide)) ?_
  refine ct_steps (by simp [powSteps]) (by simp) PPhasePub.pw (fun _ _ h => h.1) (fun _ _ h => h.2) hP ?_
  refine RelCT.seqs_app (by simp) (by simp [hSteps]) (ct_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) (by taint_decide) (fun _ _ h => h.2) ?_)
  exact two_map PPhasePub.h (fun _ _ h => h) (VG.Proof.Bignum.X86_64.h_ct M hRX hL)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupChk`. -/
section

/-!
# RSA with the CRT on x86-64: constant time of the checks' pieces

Between the pieces of `checks`, what they read from the headers (`CK`: the
modulus' header, the primes' workspaces' bases, links, sizes and arrays, and
a mask in `sMask`) is kept by their frames. Each piece is constant time from
`CK` and `rdi` (`pq_ct`, `eq_ct`, `qinv_ct`, `fixP_ct`, …).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- What the checks keep. -/
def CK (p : ChecksPub) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.Scr t p.B p.Z ∧ Hdr t.mem p.B p.w p.minv ∧ VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sWsP) = VG.Proof.Bignum.X86_64.off p.B p.op ∧
    VG.Proof.Bignum.X86_64.word t.mem p.B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off p.B p.oq ∧ WsF t.mem p.B p.op p.wp ∧ WsF t.mem p.B p.oq p.wq ∧
    (∃ c, VG.Proof.Bignum.X86_64.word t.mem p.B (8 * Public.sMask) = VG.Proof.Bignum.X86_64.mask c) ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.op ∧
    p.op + VG.Proof.Bignum.X86_64.slot p.wp 8 + tabBytes p.wp ≤ p.oq ∧ p.oq + VG.Proof.Bignum.X86_64.slot p.wq 8 + tabBytes p.wq ≤ p.Z ∧ 2 ≤ p.wp ∧
    p.wp ≤ p.w ∧ 2 ≤ p.wq ∧ p.wq ≤ p.w

/-- `CK` with `rdi` at `f p`. -/
def CKr (f : ChecksPub → Addr) (p : ChecksPub) (t : State) : Prop := VG.Proof.Bignum.X86_64.CK p t ∧ t.gpr .rdi = f p

theorem pins_ckr (f : ChecksPub → Addr) : Pins (VG.Proof.Bignum.X86_64.CKr f) [.rdi] :=
  pins_of (fun p _ => f p) fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.2

theorem CK.bounds {p : ChecksPub} {t : State} (h : VG.Proof.Bignum.X86_64.CK p t) :
    p.B.toNat + p.Z ≤ 2 ^ 64 ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.op ∧
      p.op + VG.Proof.Bignum.X86_64.slot p.wp 8 + tabBytes p.wp ≤ p.oq ∧ p.oq + VG.Proof.Bignum.X86_64.slot p.wq 8 + tabBytes p.wq ≤ p.Z ∧ 2 ≤ p.wp ∧
      p.wp ≤ p.w ∧ 2 ≤ p.wq ∧ p.wq ≤ p.w :=
  let ⟨hs, _, _, _, _, _, _, b⟩ := h; ⟨hs.nowrap, b⟩

/-- A change above the modulus' header, keeping the primes' workspaces. -/
theorem CK.frm {p : ChecksPub} {t t' : State} (h : VG.Proof.Bignum.X86_64.CK p t) {rs : List (Nat × Nat)} (hf : Frm p.B rs t.mem t'.mem)
    (hr : ∀ r ∈ rs, 256 ≤ r.1) (hP : WsF t'.mem p.B p.op p.wp) (hQ : WsF t'.mem p.B p.oq p.wq) {regs : List Reg}
    (k : VG.Proof.MlKem.X86_64.Keep regs t t') : VG.Proof.Bignum.X86_64.CK p t' := by
  obtain ⟨hs, hH, hWP, hWQ, -, -, ⟨c, hM⟩, b⟩ := h
  have hn := hs.nowrap
  have h8 : 256 ≤ VG.Proof.Bignum.X86_64.slot p.w 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hw : ∀ i < 32, VG.Proof.Bignum.X86_64.word t'.mem p.B (8 * i) = VG.Proof.Bignum.X86_64.word t.mem p.B (8 * i) := fun i hi =>
    hf.word_eq (fun r hr' => Or.inl (by have := hr r hr'; omega)) (by omega)
  exact ⟨hs.congr k.2.2, ⟨(hw _ (by decide)).trans hH.hw, (hw _ (by decide)).trans hH.hminv,
    fun j hj => (hw _ (by unfold sArr; omega)).trans (hH.harr j hj)⟩, (hw _ (by decide)).trans hWP,
    (hw _ (by decide)).trans hWQ, hP, hQ, ⟨c, (hw _ (by decide)).trans hM⟩, b⟩

theorem CK.mem {p : ChecksPub} {t t' : State} (h : VG.Proof.Bignum.X86_64.CK p t) (hm : t'.mem = t.mem) {regs : List Reg}
    (k : VG.Proof.MlKem.X86_64.Keep regs t t') : VG.Proof.Bignum.X86_64.CK p t' :=
  h.frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (hm ▸ h.2.2.2.2.1) (hm ▸ h.2.2.2.2.2.1) k

/-- A change in the accumulators. -/
theorem CK.acc {p : ChecksPub} {t t' : State} (h : VG.Proof.Bignum.X86_64.CK p t)
    (ho : VG.Proof.Bignum.X86_64.Outside p.B (VG.Proof.Bignum.X86_64.slot p.w Public.aAcc) (8 * (2 * p.w + 2)) t.mem t'.mem) {regs : List Reg}
    (k : VG.Proof.MlKem.X86_64.Keep regs t t') : VG.Proof.Bignum.X86_64.CK p t' := by
  obtain ⟨hn, -, -, hlo, hop, hoq, -⟩ := h.bounds
  have hA := accs_le p.w
  have := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  have h0 := hdr_lt_slot p.w Public.aAcc (show 31 < 32 by decide)
  have f := Frm.of_outside (rs := [(VG.Proof.Bignum.X86_64.slot p.w Public.aAcc, 8 * (2 * p.w + 2))]) ho (by simp)
  have hr : ∀ r ∈ [(VG.Proof.Bignum.X86_64.slot p.w Public.aAcc, 8 * (2 * p.w + 2))], r.1 + r.2 ≤ p.op := fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega
  exact h.frm f (fun r hr' => by rw [List.mem_singleton.mp hr']; simp only; omega)
    (h.2.2.2.2.1.frm f (fun r hr' => Or.inr (hr r hr')) (by omega))
    (h.2.2.2.2.2.1.frm f (fun r hr' => Or.inr (by have := hr r hr'; omega)) (by omega)) k

/-- A change of the mask. -/
theorem CK.newMask {p : ChecksPub} {t t' : State} (h : VG.Proof.Bignum.X86_64.CK p t) (ho : VG.Proof.Bignum.X86_64.Outside p.B (8 * Public.sMask) 8 t.mem t'.mem)
    (hM : ∃ c, VG.Proof.Bignum.X86_64.word t'.mem p.B (8 * Public.sMask) = VG.Proof.Bignum.X86_64.mask c) {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs t t') : VG.Proof.Bignum.X86_64.CK p t' := by
  obtain ⟨hn, -, -, hlo, hop, hoq, -⟩ := h.bounds
  have h8 : 256 ≤ VG.Proof.Bignum.X86_64.slot p.w 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  have f := Frm.of_outside (rs := [(8 * Public.sMask, 8)]) ho (by simp)
  have hr : ∀ r ∈ [(8 * Public.sMask, 8)], r.1 + r.2 ≤ p.op := fun r hr => by
    rw [List.mem_singleton.mp hr]; unfold Public.sMask sFn; simp only; omega
  obtain ⟨hs, hH, hWP, hWQ, hP, hQ, -, b⟩ := h
  have hw : ∀ i < 32, i ≠ Public.sMask → VG.Proof.Bignum.X86_64.word t'.mem p.B (8 * i) = VG.Proof.Bignum.X86_64.word t.mem p.B (8 * i) := fun i hi hne =>
    ho.word (by unfold Public.sMask sFn at hne ⊢; omega) (by omega)
  exact ⟨hs.congr k.2.2, ⟨(hw _ (by decide) (by decide)).trans hH.hw, (hw _ (by decide) (by decide)).trans hH.hminv,
    fun j hj => (hw _ (by unfold sArr; omega) (by unfold sArr Public.sMask sFn; omega)).trans (hH.harr j hj)⟩,
    (hw _ (by decide) (by decide)).trans hWP, (hw _ (by decide) (by decide)).trans hWQ,
    hP.frm f (fun r hr' => Or.inr (hr r hr')) (by omega),
    hQ.frm f (fun r hr' => Or.inr (by have := hr r hr'; omega)) (by omega), hM, b⟩

theorem ChecksPre.ck {p : ChecksPub} {s : State} (h : ChecksPre p s) : VG.Proof.Bignum.X86_64.CKr (·.B) p s := by
  obtain ⟨mp, mq, P, Q, QI, m0, hg, a1, a2, b1, b2, b3, c1, c2, c3, c4, hsP, hsQ, hwsP, hwsQ, -, hM, -⟩ := h
  exact ⟨⟨hg.scr, hg.hdr, hsP, hsQ, ⟨hwsP.link, hwsP.hdr.hw, hwsP.hdr.harr⟩, ⟨hwsQ.link, hwsQ.hdr.hw, hwsQ.hdr.harr⟩,
    ⟨m0, hM⟩, a1, a2, b1, b2, b3, c1, c2, c3, c4⟩, hg.rdi⟩

theorem CK.good {p : ChecksPub} {t : State} (h : VG.Proof.Bignum.X86_64.CK p t) (hdi : t.gpr .rdi = p.B) : VG.Proof.Bignum.X86_64.Good t p.B p.Z p.w p.minv :=
  ⟨h.1, hdi, h.2.1⟩

theorem CK.slotZ {p : ChecksPub} {t : State} (h : VG.Proof.Bignum.X86_64.CK p t) : VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.Z := by
  obtain ⟨-, -, h28, hlo, hop, hoq, -⟩ := h.bounds; omega

/-- Into a workspace from the modulus' (`enterP`, `enterQ`), or back (`leave`). -/
theorem CK.move {p : ChecksPub} {s : State} (h : VG.Proof.Bignum.X86_64.CK p s) {X : Addr} {i : Nat} {A' : Addr}
    (hdi : s.gpr .rdi = X) (hl : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off X (8 * i)) 8) (hw : VG.Proof.Bignum.X86_64.word s.mem X (8 * i) = A') :
    WP isa (.block [.mov .rdi (.mem (hdr i))]) s (VG.Proof.Bignum.X86_64.CKr (fun _ => A') p) :=
  WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = A' ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hl, hw]) rfl) fun t ⟨⟨hdi', hm⟩, k⟩ => ⟨h.mem hm k, hdi'⟩

theorem CK.ldB {p : ChecksPub} {s : State} (h : VG.Proof.Bignum.X86_64.CK p s) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off p.B (8 * i)) 8 :=
  h.1.ld (by have := h.slotZ; have := hdr_lt_slot p.w 8 hi; omega)

theorem CK.ldP {p : ChecksPub} {s : State} (h : VG.Proof.Bignum.X86_64.CK p s) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.op) (8 * i)) 8 := by
  obtain ⟨hn, -, -, hlo, hop, hoq, -⟩ := h.bounds
  have h8 := hdr_lt_slot p.wp 8 hi
  exact (h.1.sub (o := p.op) (n := VG.Proof.Bignum.X86_64.slot p.wp 8) (by omega) (by omega)).ld (by omega)

theorem CK.ldQ {p : ChecksPub} {s : State} (h : VG.Proof.Bignum.X86_64.CK p s) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.oq) (8 * i)) 8 := by
  obtain ⟨hn, -, -, hlo, hop, hoq, -⟩ := h.bounds
  have h8 := hdr_lt_slot p.wq 8 hi
  exact (h.1.sub (o := p.oq) (n := VG.Proof.Bignum.X86_64.slot p.wq 8) (by omega) (by omega)).ld (by omega)

/-- `p`'s workspace. -/
abbrev ckP (p : ChecksPub) : Addr := VG.Proof.Bignum.X86_64.off p.B p.op
/-- `q`'s workspace. -/
abbrev ckQ (p : ChecksPub) : Addr := VG.Proof.Bignum.X86_64.off p.B p.oq

theorem enterP_ck {p : ChecksPub} {s : State} (h : VG.Proof.Bignum.X86_64.CKr (·.B) p s) : WP isa (.block [enterP]) s (VG.Proof.Bignum.X86_64.CKr VG.Proof.Bignum.X86_64.ckP p) :=
  h.1.move (X := p.B) (i := sWsP) h.2 (h.1.ldB (by decide)) h.1.2.2.1

theorem enterQ_ck {p : ChecksPub} {s : State} (h : VG.Proof.Bignum.X86_64.CKr (·.B) p s) : WP isa (.block [enterQ]) s (VG.Proof.Bignum.X86_64.CKr VG.Proof.Bignum.X86_64.ckQ p) :=
  h.1.move (X := p.B) (i := sWsQ) h.2 (h.1.ldB (by decide)) h.1.2.2.2.1

theorem leaveP_ck {p : ChecksPub} {s : State} (h : VG.Proof.Bignum.X86_64.CKr VG.Proof.Bignum.X86_64.ckP p s) : WP isa (.block [leave]) s (VG.Proof.Bignum.X86_64.CKr (·.B) p) :=
  h.1.move (X := VG.Proof.Bignum.X86_64.ckP p) (i := sLink) h.2 (h.1.ldP (by decide)) h.1.2.2.2.2.1.1

theorem leaveQ_ck {p : ChecksPub} {s : State} (h : VG.Proof.Bignum.X86_64.CKr VG.Proof.Bignum.X86_64.ckQ p s) : WP isa (.block [leave]) s (VG.Proof.Bignum.X86_64.CKr (·.B) p) :=
  h.1.move (X := VG.Proof.Bignum.X86_64.ckQ p) (i := sLink) h.2 (h.1.ldQ (by decide)) h.1.2.2.2.2.2.1.1

/-! ## `p q` -/

theorem CKr.rows {p : ChecksPub} {s : State} (h : VG.Proof.Bignum.X86_64.CKr (·.B) p s) :
    VG.Proof.Bignum.X86_64.RowsPre Public.aN ⟨p.B, p.Z, p.w, p.op, p.oq, p.wp, p.wq⟩ s := by
  obtain ⟨⟨hs, hH, hWP, hWQ, hP, hQ, -, -, -, hlo, hop, hoq, -⟩, hdi⟩ := h
  exact ⟨hs, hdi, hH.harr _ (by decide), hWP, hWQ, hP.2.1, hQ.2.1, (hP.2.2 _ (by decide)).trans (off_off _ _ _),
    (hQ.2.2 _ (by decide)).trans (off_off _ _ _), by decide, hlo, by dsimp only; omega, by dsimp only; omega⟩

theorem pq_ct : RelCT isa (Two (VG.Proof.Bignum.X86_64.CKr (·.B))) (seqs pqProduct) (Two (VG.Proof.Bignum.X86_64.CKr (·.B))) := by
  refine two_post ?_ fun p s h => ?_
  · rw [pqProduct_eq]
    refine RelCT.seqs_append (by simp [zeroAccs]) (by simp) (RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.CKr (·.B))
      (two_map (fun p : ChecksPub => (⟨p.B, p.Z, p.w⟩ : Ws)) (fun p s h => ⟨p.minv, h.1.good h.2, h.1.slotZ⟩)
        VG.Proof.Bignum.X86_64.zeroAccs_ct) fun p s h => ?_) ?_)
    · obtain ⟨hn, -, h28, -⟩ := h.1.bounds
      exact WP.mono (zeroAccs_ok (h.1.good h.2) h.1.slotZ (by omega)) fun t ⟨_, ho, k⟩ =>
        ⟨h.1.acc ho k, (k.gpr (by decide)).trans h.2⟩
    · exact two_map (fun p : ChecksPub => (⟨p.B, p.Z, p.w, p.op, p.oq, p.wp, p.wq⟩ : VG.Proof.Bignum.X86_64.RowsPub))
        (fun p s h => h.rows) (VG.Proof.Bignum.X86_64.rows_ct (by taint_decide))
  · obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, a3, a4⟩ := h.1.bounds
    have hR := h.rows
    exact WP.mono (pqProduct_ok (h.1.good h.2) (by omega) hR.2.2.2.1 hR.2.2.2.2.1 hR.2.2.2.2.2.1
      hR.2.2.2.2.2.2.1 hR.2.2.2.2.2.2.2.1 hR.2.2.2.2.2.2.2.2.1 hlo hop hoq (show 1 ≤ p.wp by omega) a2 (show 1 ≤ p.wq by omega) a4)
      fun t ⟨_, ho, k⟩ => ⟨h.1.acc ho k, (k.gpr (by decide)).trans h.2⟩

/-! ## `p q = n` -/

/-- `eqCheck`'s registers. -/
def EQ1 (p : ChecksPub) (t : State) : Prop :=
  t.gpr .rdi = p.B ∧ t.gpr .r12 = BitVec.ofNat 64 p.w ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w Public.aAcc) ∧
    t.gpr .r10 = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w Public.aN)

theorem eq_ct : RelCT isa (Two (VG.Proof.Bignum.X86_64.CKr (·.B))) (seqs eqCheck) (Two (VG.Proof.Bignum.X86_64.CKr (·.B))) := by
  refine two_post ?_ fun p s h => ?_
  · unfold eqCheck
    simp only [seqs]
    refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.EQ1) [.rdi] (VG.Proof.Bignum.X86_64.pins_ckr _) (by taint_decide) fun p s h => ?_)
      (two_taint [.rdi, .r12, .rbx, .r10] (pins_of (fun (p : ChecksPub) r => if r = .rdi then p.B else
        if r = .r12 then BitVec.ofNat 64 p.w else if r = .rbx then VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w Public.aAcc) else
        VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w Public.aN)) fun p s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact h.1
          · exact h.2.1
          · exact h.2.2.1
          · exact h.2.2.2) (by taint_decide))
    obtain ⟨hk, hdi⟩ := h
    have hH := hk.2.1
    exact WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧
        t.gpr .rbx = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w Public.aAcc) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off p.B (VG.Proof.Bignum.X86_64.slot p.w Public.aN))
      (by xrun [State.ea, hdr, hdi, hdrOff, hk.ldB (i := sW) (by decide), hk.ldB (i := sArr Public.aAcc) (by decide),
        hk.ldB (i := sArr Public.aN) (by decide), hH.hw, hH.harr Public.aAcc (by decide),
        hH.harr Public.aN (by decide)]) rfl)
      fun t ⟨h', k⟩ => ⟨(k.gpr (by decide)).trans hdi, h'⟩
  · obtain ⟨hn, a1, a2, -⟩ := h.1.bounds
    obtain ⟨c, hM⟩ := h.1.2.2.2.2.2.2.1
    exact WP.mono (eqCheck_ok (h.1.good h.2) h.1.slotZ (by omega) (by omega)) fun t ⟨hM', ho, k⟩ =>
      ⟨h.1.newMask ho ⟨_, by rw [hM', hM, mask_and]⟩ k, (k.gpr (by decide)).trans h.2⟩

/-! ## `qInv < p` -/

/-- `qinvCheck`'s registers. -/
def QI1 (p : ChecksPub) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.CKr VG.Proof.Bignum.X86_64.ckP p t ∧ t.gpr .r12 = BitVec.ofNat 64 p.wp ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.ckP p) (VG.Proof.Bignum.X86_64.slot p.wp aChunk) ∧
    t.gpr .r10 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.ckP p) (VG.Proof.Bignum.X86_64.slot p.wp Public.aN) ∧ t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false

theorem qinv_ct : RelCT isa (Two (VG.Proof.Bignum.X86_64.CKr VG.Proof.Bignum.X86_64.ckP)) (seqs qinvCheck) (Two (VG.Proof.Bignum.X86_64.CKr VG.Proof.Bignum.X86_64.ckP)) := by
  refine two_post ?_ fun p s h => ?_
  · unfold qinvCheck
    simp only [seqs]
    refine RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.QI1) [.rdi] (VG.Proof.Bignum.X86_64.pins_ckr _) (by taint_decide) fun p s h => ?_)
      (RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.CKr VG.Proof.Bignum.X86_64.ckP) (two_taint [.r12, .rbx, .r10] (pins_of (fun (p : ChecksPub) r =>
        if r = .r12 then BitVec.ofNat 64 p.wp else if r = .rbx then VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.ckP p) (VG.Proof.Bignum.X86_64.slot p.wp aChunk) else
        VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.ckP p) (VG.Proof.Bignum.X86_64.slot p.wp Public.aN)) fun p s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.2.1
          · exact h.2.2.1
          · exact h.2.2.2.1) (by taint_decide)) fun p s h => ?_)
      (RelCT.block_append (l₁ := ([.mov .rax (.mem (hdr sLink))] : List Instr)) (RelCT.seq
        (two_piece (Ψ := fun p t => t.gpr .rax = p.B) [.rdi] (VG.Proof.Bignum.X86_64.pins_ckr _) (by taint_decide) fun p s h => ?_)
        (two_taint [.rax] (pins_of (fun p _ => p.B) fun p s h r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h) (by taint_decide)))))
    · obtain ⟨hk, hdi⟩ := h
      have hF := hk.2.2.2.2.1
      exact WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.wp ∧
          t.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.ckP p) (VG.Proof.Bignum.X86_64.slot p.wp aChunk) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.ckP p) (VG.Proof.Bignum.X86_64.slot p.wp Public.aN) ∧
          t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧ t.mem = s.mem)
        (by xrun [State.ea, hdr, hdi, hdrOff, hk.ldP (i := sW) (by decide), hk.ldP (i := sArr aChunk) (by decide),
          hk.ldP (i := sArr Public.aN) (by decide), hF.2.1, hF.2.2 aChunk (by decide),
          hF.2.2 Public.aN (by decide)]) rfl)
        fun t ⟨⟨a, b, c, d, hm⟩, k⟩ => ⟨⟨hk.mem hm k, (k.gpr (by decide)).trans hdi⟩, a, b, c, d⟩
    · obtain ⟨⟨hk, hdi⟩, h12, hbx, h10, hbp⟩ := h
      obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, -⟩ := hk.bounds
      have := slot_le (w := p.wp) (show aChunk < 8 by decide)
      have := slot_le (w := p.wp) (show Public.aN < 8 by decide)
      exact WP.mono (cmpLoop_ok (hk.1.sub (o := p.op) (n := VG.Proof.Bignum.X86_64.slot p.wp 8) (by omega)
        (by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega)) hbx h10 h12 hbp (by omega) (by omega) (by omega) (by omega))
        fun t ⟨_, hm, k⟩ => ⟨hk.mem hm k, (k.gpr (by decide)).trans hdi⟩
    · obtain ⟨hk, hdi⟩ := h
      exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = p.B)
        (by xrun [State.ea, hdr, hdi, hdrOff, hk.ldP (i := sLink) (by decide), hk.2.2.2.2.1.1]) rfl)
        fun t h => h.1
  · obtain ⟨hk, hdi⟩ := h
    obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, -⟩ := hk.bounds
    obtain ⟨c, hM⟩ := hk.2.2.2.2.2.2.1
    have hF := hk.2.2.2.2.1
    exact WP.mono (qinvCheck_ok hk.1 hdi (hdr_any hF.2.1 hF.2.2) (by omega)
      (by unfold Public.sMask sFn; unfold VG.Proof.Bignum.X86_64.slot hdrBytes at hlo; omega) (by omega) (by omega) hF.1)
      fun t ⟨hM', ho, k⟩ => ⟨hk.newMask ho ⟨_, by rw [hM', hM, mask_and]⟩ k, (k.gpr (by decide)).trans hdi⟩

/-! ## The fixes -/

theorem pfRanges_le (wx : Nat) : ∀ r ∈ pfRanges wx, 8 * 7 ≤ r.1 ∧ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by
  have := hdr_lt_slot wx Public.aN (show 31 < 32 by decide)
  have := hdr_lt_slot wx Public.aOne (show 31 < 32 by decide)
  have := slot_le (w := wx) (show Public.aN < 8 by decide)
  have := slot_le (w := wx) (show Public.aOne < 8 by decide)
  intro r hr
  simp only [pfRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [sMaskX, sMinv, sFn] <;> omega

theorem CK.sub {p : ChecksPub} {s : State} {o wx : Nat} (hk : VG.Proof.Bignum.X86_64.CK p s) (hdi : s.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B o)
    (hF : WsF s.mem p.B o wx) (hlo : VG.Proof.Bignum.X86_64.slot p.w 8 ≤ o) (hhi : o + VG.Proof.Bignum.X86_64.slot wx 8 + tabBytes wx ≤ p.Z) :
    ∃ (minv : BitVec 64) (c : Bool), SubCtx s p.B p.Z o p.w wx minv ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * Public.sMask) = VG.Proof.Bignum.X86_64.mask c := by
  obtain ⟨hs, hH, -, -, -, -, ⟨c, hM⟩, -⟩ := hk
  exact ⟨_, c, ⟨hs, hdi, hdr_any hF.2.1 hF.2.2, hF.1, hH.hw, hH.harr, hlo, hhi⟩, hM⟩

theorem CK.pf {p : ChecksPub} {s : State} {o wx : Nat} (hk : VG.Proof.Bignum.X86_64.CK p s) (hdi : s.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B o)
    (hF : WsF s.mem p.B o wx) (hlo : VG.Proof.Bignum.X86_64.slot p.w 8 ≤ o) (hhi : o + VG.Proof.Bignum.X86_64.slot wx 8 + tabBytes wx ≤ p.Z) (h2 : 2 ≤ wx) (hwx : wx ≤ p.w) :
    PF ⟨p.B, p.Z, o, p.w, wx⟩ s := by
  have := hk.bounds
  obtain ⟨m, c, hc, hM⟩ := hk.sub hdi hF hlo hhi
  exact ⟨m, c, hc, hM, h2, by simp only; omega⟩

theorem fixP_ct : RelCT isa (Two (VG.Proof.Bignum.X86_64.CKr VG.Proof.Bignum.X86_64.ckP)) (seqs primeFix) (Two (VG.Proof.Bignum.X86_64.CKr VG.Proof.Bignum.X86_64.ckP)) := by
  refine two_post (two_map (fun p : ChecksPub => (⟨p.B, p.Z, p.op, p.w, p.wp⟩ : XPub)) (fun p s ⟨hk, hdi⟩ => by
    obtain ⟨-, -, h28, hlo, hop, hoq, a1, a2, -⟩ := hk.bounds
    exact hk.pf hdi hk.2.2.2.2.1 hlo (by omega) a1 a2) primeFix_ct) fun p s ⟨hk, hdi⟩ => ?_
  obtain ⟨hn, -, h28, hlo, hop, hoq, a1, a2, -⟩ := hk.bounds
  obtain ⟨_, c, hc, hM⟩ := hk.sub hdi hk.2.2.2.2.1 hlo (by omega)
  have h8 := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have h8q := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  have h8w := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hr := VG.Proof.Bignum.X86_64.pfRanges_le p.wp
  refine WP.mono (primeFix_frm hc hM (by omega) (by omega)) fun t ⟨_, hc', f, k⟩ => ?_
  have f' := f.rebase (by omega) fun r hr' => by have := hr r hr'; omega
  have hr' : ∀ r ∈ shiftRanges p.op (pfRanges p.wp), p.op + 8 * 7 ≤ r.1 ∧ r.1 + r.2 ≤ p.op + VG.Proof.Bignum.X86_64.slot p.wp 8 :=
    fun r hr'' => by
      obtain ⟨r₀, h₀, rfl⟩ := List.mem_map.mp hr''
      have := hr r₀ h₀; simp only; omega
  exact ⟨hk.frm f' (fun r h => by have := hr' r h; omega) ⟨hc'.link, hc'.hdr.hw, hc'.hdr.harr⟩
    (hk.2.2.2.2.2.1.frm f' (fun r h => Or.inr (by have := hr' r h; omega)) (by omega)) k, hc'.rdi⟩

theorem fixQ_ct : RelCT isa (Two (VG.Proof.Bignum.X86_64.CKr VG.Proof.Bignum.X86_64.ckQ)) (seqs primeFix) (Two (VG.Proof.Bignum.X86_64.CKr VG.Proof.Bignum.X86_64.ckQ)) := by
  refine two_post (two_map (fun p : ChecksPub => (⟨p.B, p.Z, p.oq, p.w, p.wq⟩ : XPub)) (fun p s ⟨hk, hdi⟩ => by
    obtain ⟨-, -, h28, hlo, hop, hoq, -, -, a3, a4⟩ := hk.bounds
    exact hk.pf hdi hk.2.2.2.2.2.1 (by omega) hoq a3 a4) primeFix_ct) fun p s ⟨hk, hdi⟩ => ?_
  obtain ⟨hn, -, h28, hlo, hop, hoq, -, -, a3, a4⟩ := hk.bounds
  obtain ⟨_, c, hc, hM⟩ := hk.sub hdi hk.2.2.2.2.2.1 (by omega) hoq
  have h8 := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have h8q := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  have h8w := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hr := VG.Proof.Bignum.X86_64.pfRanges_le p.wq
  refine WP.mono (primeFix_frm hc hM (by omega) (by omega)) fun t ⟨_, hc', f, k⟩ => ?_
  have f' := f.rebase (by omega) fun r hr' => by have := hr r hr'; omega
  have hr' : ∀ r ∈ shiftRanges p.oq (pfRanges p.wq), p.oq + 8 * 7 ≤ r.1 ∧ r.1 + r.2 ≤ p.oq + VG.Proof.Bignum.X86_64.slot p.wq 8 :=
    fun r hr'' => by
      obtain ⟨r₀, h₀, rfl⟩ := List.mem_map.mp hr''
      have := hr r₀ h₀; simp only; omega
  exact ⟨hk.frm f' (fun r h => by have := hr' r h; omega)
    (hk.2.2.2.2.1.frm f' (fun r h => Or.inl (by have := hr' r h; omega)) (by omega))
    ⟨hc'.link, hc'.hdr.hw, hc'.hdr.harr⟩ k, hc'.rdi⟩

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup`. -/
section

/-!
# RSA with the CRT on x86-64: constant time of the setup and the checks

The claims of `CrtCTDefs.lean` for the primes' setup: the loads
(`loadArr_ct_pN`, `loadArr_ct_pI`, `loadArr_ct_qN`, in `CrtCTSetupLoad.lean`),
`primesSetup` (`setup_ct`, in `CrtCTSetupWs.lean`), and `checks`
(`checks_ct`), from its pieces (`CrtCTSetupChk.lean`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

theorem leaveEnterQ_ck : RelCT isa (Two (VG.Proof.Bignum.X86_64.CKr VG.Proof.Bignum.X86_64.ckP)) (.block [leave, enterQ]) (Two (VG.Proof.Bignum.X86_64.CKr VG.Proof.Bignum.X86_64.ckQ)) :=
  RelCT.block_append (l₁ := ([leave] : List Instr))
    (RelCT.seq (two_piece (Ψ := VG.Proof.Bignum.X86_64.CKr (·.B)) [.rdi] (VG.Proof.Bignum.X86_64.pins_ckr _) (by taint_decide) fun p s h => VG.Proof.Bignum.X86_64.leaveP_ck h)
      (two_piece [.rdi] (VG.Proof.Bignum.X86_64.pins_ckr _) (by taint_decide) fun p s h => VG.Proof.Bignum.X86_64.enterQ_ck h))

theorem checks_ct : ChecksCT := by
  unfold ChecksCT checks
  simp only [List.append_assoc]
  refine two_map id (fun _ _ h => h.ck) ?_
  refine RelCT.seqs_append (by simp [pqProduct, zeroAccs]) (by simp [eqCheck]) (RelCT.seq VG.Proof.Bignum.X86_64.pq_ct ?_)
  refine RelCT.seqs_append (by simp [eqCheck]) (by simp) (RelCT.seq VG.Proof.Bignum.X86_64.eq_ct ?_)
  refine RelCT.seqs_append (by simp) (by simp [qinvCheck]) (RelCT.seq (two_piece [.rdi] (VG.Proof.Bignum.X86_64.pins_ckr _)
    (by taint_decide) fun p s h => VG.Proof.Bignum.X86_64.enterP_ck h) ?_)
  refine RelCT.seqs_append (by simp [qinvCheck]) (by simp [primeFix]) (RelCT.seq VG.Proof.Bignum.X86_64.qinv_ct ?_)
  refine RelCT.seqs_append (by simp [primeFix]) (by simp) (RelCT.seq VG.Proof.Bignum.X86_64.fixP_ct ?_)
  refine RelCT.seqs_append (by simp) (by simp [primeFix]) (RelCT.seq VG.Proof.Bignum.X86_64.leaveEnterQ_ck ?_)
  refine RelCT.seqs_append (by simp [primeFix]) (by simp) (RelCT.seq VG.Proof.Bignum.X86_64.fixQ_ct ?_)
  exact two_taint [.rdi] (VG.Proof.Bignum.X86_64.pins_ckr _) (by taint_decide)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtImplies`. -/
section

/-!
# RSA with the CRT on x86-64: the shared contract

`crtContract` states the shared contract on the registers and the stack
(`crt_implies`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64

theorem stackArgs_twelve (s : State) :
    List.map (stackArg s) (List.range 12) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11] := rfl

/-- A state meeting `crtContract.pre`: a 512-bit modulus, one-byte primes,
exponents and `qInv`, and the stack arguments at `0x6008`. -/
def crtSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 64
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6009 then 0x40 else if a = 0x6010 then 1 else if a = 0x6019 then 0x41
    else if a = 0x6020 then 1 else if a = 0x6029 then 0x42 else if a = 0x6030 then 1
    else if a = 0x6039 then 0x43 else if a = 0x6040 then 1 else if a = 0x6049 then 0x44
    else if a = 0x6050 then 1 else if a = 0x6059 then 0x80 else if a = 0x6061 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 64⟩, ⟨0x4000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x6008, 96⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

theorem crt_implies : crtContract.Implies (Spec.Rsa.privateCrtContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, crtContract, VG.Proof.Bignum.X86_64.stackArgs_twelve, List.append_eq] at h
    sig_pre [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, crtContract, VG.Proof.Bignum.X86_64.stackArgs_twelve, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, crtContract, VG.Proof.Bignum.X86_64.stackArgs_twelve, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, crtContract, VG.Proof.Bignum.X86_64.stackArgs_twelve, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, crtContract, VG.Proof.Bignum.X86_64.stackArgs_twelve, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
    refine ⟨?_, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
      List.map_injective_iff.2 (fun _ _ h => BitVec.toNat_inj.1 h) hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, crtContract, VG.Proof.Bignum.X86_64.stackArgs_twelve, List.append_eq] [crtSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Bignum.X86_64.crtSatState

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtVerified`. -/
section

/-!
# `vg_rsa_private_crt` on x86-64: verified against the shared contract

`main`'s parts are constant time (`setup_ct`, `checks_ct`, the phases from
`G`, `redc` and the exponentiation, `crtFinish_ct`), so the function is
(`crtCode_constantTime`); with correctness (`crtCode_correct`) and the
contract on the registers and the stack (`crt_implies`), `Crt.code` is
verified (`crt_verified`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt

/-- `vg_rsa_private_crt` is constant time but for `n`. -/
theorem crtCode_constantTime (M : Mont) : ConstantTime isa crtContract.pre crtContract.pub (Crt.code M.mm) :=
  VG.Proof.Bignum.X86_64.crtCode_constantTime_of M setup_ct VG.Proof.Bignum.X86_64.checks_ct
    (qPhase_ct M (unit_ct M (gPow_ct_Q M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M (redc_ct_Y M) (expLoop_ct_Q M) (by taint_decide)))
    (VG.Proof.Bignum.X86_64.pPhase_ct M (unit_ct M (gPow_ct_P M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M (redc_ct_Y M) (expLoop_ct_P M) (by taint_decide)) (redc_ct_X M) loadArr_ct_pI)
    VG.Proof.Bignum.X86_64.crtFinish_ct

/-- `vg_rsa_private_crt` with Montgomery multiplication `M`, given that its
code never loads MXCSR (which the registration file evaluates). -/
theorem crt_verified (M : Mont) (hmx : (Crt.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (Crt.code M.mm) (Spec.Rsa.privateCrtContract abi) :=
  Verified.of_correct (VG.Proof.Bignum.X86_64.crtCode_correct M hmx) (VG.Proof.Bignum.X86_64.crtCode_constantTime M) VG.Proof.Bignum.X86_64.crt_implies

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.IfmaPost`. -/
section

/-!
# RSA with AVX512_IFMA on x86-64: after the exponentiations

`post` is `p`'s phase after its exponentiation, in `p`'s workspace:
`R_p² mod p` from `n`'s `R_n² mod n` (`redc`), `m_q R_p mod p` from `q`'s
result, and `h = (m_p - m_q) qInv mod p` (`hTail_ok`, as `pPhase`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

theorem post_eq (mul : Nat → Nat → Nat → Prog isa) :
    CrtIfma.post mul = (([.block [.mov .rdi (.mem (hdr sWsP))]] : List (Prog isa)) ++ redc mul Public.aR2) ++
      (.block [.mov .rax (.mem (hdr sLink)), .mov .rax (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax sWsQ)),
          .mov .rsi (.mem (VG.Impl.Rsa.X86_64.Crt.ws .rax (sArr Public.aY))), .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aChunk)))] ::
        copyWords :: mul aChunk aChunk aXc :: (copyArr aXc aChunk ++
      ((subModArr aT Public.aY aXc ++ loadArr aChunk sQinv sPlen ++ maskArr aChunk ++
        ([mul Public.aY aT aChunk] : List (Prog isa))) ++ ([.block [leave]] : List (Prog isa))))) := by
  simp only [CrtIfma.post, enterP, List.append_assoc, List.cons_append, List.nil_append]

/-- `post`: with `q`'s result in its `aY`, `p`'s `aY := h` as `pPhase` leaves
it. Only `p`'s workspace changes. -/
theorem post_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx mq : BitVec 64}
    {N X oq op wx m1 : Nat} {qp : Addr} {qib : List Byte} {c : Bool}
    (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hN : NVals s B w minv N) (hw2 : w = 2 * wx)
    (hq : VG.Proof.Bignum.X86_64.word s.mem B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off B oq) (hwsq : WsAt s.mem B oq wx mq)
    (hhiq : oq + VG.Proof.Bignum.X86_64.slot wx 8 + tabBytes wx ≤ Z)
    (hlo : VG.Proof.Bignum.X86_64.slot w 8 ≤ op) (hhi : op + VG.Proof.Bignum.X86_64.slot wx 8 + tabBytes wx ≤ oq) (hwx2 : 2 ≤ wx)
    (hsp : VG.Proof.Bignum.X86_64.word s.mem B (8 * sWsP) = VG.Proof.Bignum.X86_64.off B op) (hws : WsAt s.mem B op wx mx) (hX : XVals s B op wx mx X)
    (hX1 : 1 < X) (hXodd : X % 2 = 1)
    (hyl : wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx < X)
    (hyc : X ∣ N → wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx % X = m1 * 2 ^ (64 * wx) % X)
    (hmask : VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B op) (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask c) (hc : c = true → X ∣ N)
    (hqp : VG.Proof.Bignum.X86_64.word s.mem B (8 * sQinv) = qp) (hql : VG.Proof.Bignum.X86_64.word s.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length)
    (hqs : Src s B Z qp qib) (hq1 : 1 ≤ qib.length) (hq2 : qib.length < 2 ^ 31) (hqw : (qib.length + 7) / 8 ≤ wx)
    (hqi : c = true → Spec.Rsa.os2ip qib < X) :
    WP isa (seqs (CrtIfma.post M.mm)) s fun t => Good t B Z w minv ∧ WsAt t.mem B op wx mx ∧
      XVals t B op wx mx X ∧ wv t.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx < X ∧
      (c = true → ∃ a b, a % X = m1 * 2 ^ (64 * wx) % X ∧
        b % X = wv s.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx * 2 ^ (64 * wx) % X ∧ b < X ∧
        wv t.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx * 2 ^ (64 * wx) % X = (a + X - b) % X * Spec.Rsa.os2ip qib % X) ∧
      Frm B (gRanges w ++ [(VG.Proof.Bignum.X86_64.slot w Public.aX, 8 * (w + 2)), xRange op wx]) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hz : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by omega
  have ho64 : op < 2 ^ 64 := by omega
  have hoL : op + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64 := by omega
  have hwx : wx ≤ w := by omega
  have hK := nChunks_two hw2 (by omega)
  have hRx : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
  have hRR : Nat.Coprime (2 ^ (64 * wx * 2)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
  have e2 : 2 ^ (64 * w) = 2 ^ (64 * wx * 2) := by rw [hw2]; congr 1; omega
  have lY := slot_le (w := wx) (show Public.aY < 8 by decide)
  have lC := slot_le (w := wx) (show aChunk < 8 by decide)
  have hC0 := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
  have hrm : ∀ r ∈ redcRanges wx, 8 * sMaskX + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMaskX := fun r hr => by
    simp only [redcRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [sMaskX, sSrc, sRem, sFn, VG.Proof.Bignum.X86_64.slot, hdrBytes] <;>
      omega
  have rY := redcRanges_arr wx (j := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  rw [VG.Proof.Bignum.X86_64.post_eq]
  -- `aXc := R_n² R_p^-2 = R_p²`.
  refine wp_seqs_append (by simp) (by simp [subModArr]) (WP.mono (enterRedc_ok M (j := Public.aR2) (by decide) hg
    hw28 hlo (by omega) hwx2 hwx (by decide) hsp hws hX hX1) fun s₁ ⟨hc₁, hX₁, hlt₁, hv₁, f₁, r₁, k₁⟩ => ?_)
  rw [hK] at hv₁
  have hb₁ : ∀ d, d + 8 ≤ op → VG.Proof.Bignum.X86_64.word s₁.mem B d = VG.Proof.Bignum.X86_64.word s.mem B d := fun d hd => f₁.x_below hd ho64
  have hab₁ : ∀ d, op + VG.Proof.Bignum.X86_64.slot wx 8 + tabBytes wx ≤ d → d + 8 ≤ 2 ^ 64 → VG.Proof.Bignum.X86_64.word s₁.mem B d = VG.Proof.Bignum.X86_64.word s.mem B d :=
    fun d hd hd' => f₁.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega) hd'
  have hs₁ := hs.congr k₁.2.2
  have hsP := hc₁.good.scr
  have hdi₁ := hc₁.rdi
  have hldq := (hs₁.sub (o := oq) (n := VG.Proof.Bignum.X86_64.slot wx 8) (by omega) (by omega)).ld (d := 8 * sArr Public.aY)
    (by unfold sArr Public.aY; omega)
  have hqa : VG.Proof.Bignum.X86_64.word s₁.mem (VG.Proof.Bignum.X86_64.off B oq) (8 * sArr Public.aY) = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot wx Public.aY) := by
    rw [word_off, hab₁ (oq + 8 * sArr Public.aY) (by omega) (by unfold sArr Public.aY; omega), ← word_off]
    exact hwsq.hdr.harr Public.aY (by decide)
  -- `m_q` into `aChunk`.
  refine WP.seq (WP.mono (WP.keep [.rax, .rsi, .r12, .rbx] (Q := fun t =>
      t.gpr .rsi = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot wx Public.aY) ∧ t.gpr .r12 = BitVec.ofNat 64 wx ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx aChunk) ∧ t.mem = s₁.mem)
    (by xrun [State.ea, hdr, VG.Impl.Rsa.X86_64.Crt.ws, hdi₁, hdrOff, hsP.ld (d := 8 * sLink) (by unfold sLink sFn; omega), hc₁.link,
      hs₁.ld (d := 8 * sWsQ) (by unfold sWsQ sFn; omega), hb₁ (8 * sWsQ) (by unfold sWsQ sFn; omega), hq,
      hldq, hqa, hsP.ld (d := 8 * sW) (by unfold sW; omega), hc₁.hdr.hw,
      hsP.ld (d := 8 * sArr aChunk) (by unfold sArr aChunk; omega), hc₁.hdr.harr aChunk (by decide)]) rfl)
    fun s₂ ⟨⟨hsi₂, h12₂, hbx₂, hm₂⟩, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  have hsP₂ := hsP.congr k₂.2.2
  have hsi₂' : s₂.gpr .rsi = VG.Proof.Bignum.X86_64.off B (oq + VG.Proof.Bignum.X86_64.slot wx Public.aY) := by rw [hsi₂, off_off]
  refine WP.seq (WP.mono (copyWords_ok (S := B) (eS := oq + VG.Proof.Bignum.X86_64.slot wx Public.aY) (D := VG.Proof.Bignum.X86_64.off B op) (eD := VG.Proof.Bignum.X86_64.slot wx aChunk)
    (w := wx) hsi₂' hbx₂ h12₂ (by omega) (by omega) (by omega) (fun j hj => hs₂.ld (by omega))
    (fun j hj => hsP₂.st (by omega)) (fun j hj b hb => Or.inr (by
      rw [show VG.Proof.Bignum.X86_64.off B (oq + VG.Proof.Bignum.X86_64.slot wx Public.aY + 8 * j) = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B op) (oq + VG.Proof.Bignum.X86_64.slot wx Public.aY + 8 * j - op) by
        rw [off_off]; congr 1; omega, VG.Proof.Bignum.X86_64.ofs_off (VG.Proof.Bignum.X86_64.off B op) (by omega)]; omega))) fun s₃ ⟨hv₃, _, ho₃, k₃⟩ => ?_)
  rw [hm₂] at ho₃
  have hz₁ : (VG.Proof.Bignum.X86_64.off B op).toNat + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64 := by have := hc₁.good.scr.nowrap; omega
  have hX₃ : XVals s₃ B op wx mx X := hX₁.of_outside ho₃ (by decide) (by decide) (by decide) (by omega) hz₁
  have fo₃ : Frm (VG.Proof.Bignum.X86_64.off B op) [(VG.Proof.Bignum.X86_64.slot wx aChunk, 8 * wx)] s₁.mem s₃.mem := Frm.of_outside ho₃ (by simp)
  have hc₃ : SubCtx s₃ B Z op w wx mx := hc₁.of_frm fo₃ (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega) (k₂.trans k₃).2.2 ((k₂.trans k₃).gpr (by decide))
  have fx₃ : Frm B [xRange op wx] s₁.mem s₃.mem :=
    fo₃.to_x (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) hoL (List.mem_singleton_self _)
  have hC₃ : wv s₃.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx aChunk) wx = wv s.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx := by
    rw [hv₃, hm₂, wv_off]
    exact wv_congr fun i hi => hab₁ _ (by omega) (by omega)
  have hxc₃ : wv s₃.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx aXc) wx = wv s₁.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx aXc) wx := by
    have := slot_sep (w := wx) (show aXc ≠ aChunk by decide)
    have := slot_le (w := wx) (show aXc < 8 by decide)
    exact ho₃.wv (by omega) (by omega)
  -- `aChunk := m_q R_p² R_p^-1 = m_q R_p`.
  refine WP.seq (WP.mono (M.mm_ok (o := aChunk) (a := aChunk) (b := aXc) hc₃.good (Nat.le_refl _) hwx2
    (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hX₃.inv
    (by rw [hX₃.n, hxc₃]; exact hlt₁)) fun s₄₀ ⟨_, hlt₄, hm₄, ha₄, k₄₀⟩ => ?_)
  rw [hX₃.n] at hlt₄ hm₄
  obtain ⟨hc₄₀, hX₄₀, fx₄₀⟩ := hc₃.of_arrays hX₃ ha₄ (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide) k₄₀.2.2 (k₄₀.gpr (by decide)) (by omega)
  have hz₄ : (VG.Proof.Bignum.X86_64.off B op).toNat + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64 := hz₁
  -- `aXc := aChunk`.
  refine wp_seqs_append (by simp [copyArr]) (by simp [subModArr]) (WP.mono (copyArr_ok hc₄₀.good (Nat.le_refl _)
    (by omega) (by omega) (o := aXc) (a := aChunk) (by decide) (by decide) (by decide))
    fun s₄ ⟨hv₄c, ho₄c, k₄c⟩ => ?_)
  have lX := slot_le (w := wx) (show aXc < 8 by decide)
  have hX0 := hdr_lt_slot wx aXc (show 31 < 32 by decide)
  have hc₄ := hc₄₀.of_frm (rs := [(VG.Proof.Bignum.X86_64.slot wx aXc, 8 * wx)]) (Frm.of_outside ho₄c (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega) k₄c.2.2 (k₄c.gpr (by decide))
  have hX₄ : XVals s₄ B op wx mx X := hX₄₀.of_outside ho₄c (by decide) (by decide) (by decide) (by omega) hz₄
  have fx₄ : Frm B [xRange op wx] s₃.mem s₄.mem := fx₄₀.trans
    ((ho₄c.mono (o' := VG.Proof.Bignum.X86_64.slot wx aXc) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega)).to_x
      (by decide) hoL (List.mem_singleton_self _))
  have k₄ := k₄₀.trans k₄c
  have hY₄ : wv s₄.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx = wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx := by
    have := slot_sep (w := wx) (show Public.aY ≠ aXc by decide)
    rw [ho₄c.wv (by omega) (by omega), ha₄.wv_of_not_mem (by decide) (by decide) hz₄]
    have := slot_sep (w := wx) (show Public.aY ≠ aChunk by decide)
    rw [ho₃.wv (by omega) (by omega), r₁.wv_eq (fun r hr => by have := rY r hr; omega) (by omega)]
  have hM₄ : VG.Proof.Bignum.X86_64.word s₄.mem (VG.Proof.Bignum.X86_64.off B op) (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask c := by
    have hmx : 8 * sMaskX + 8 ≤ 8 * 31 + 8 := by unfold sMaskX sFn; omega
    rw [ho₄c.word (.inl (by omega)) (by omega), ha₄.hslot (by decide), ho₃.word (.inl (by omega)) (by omega),
      r₁.word_eq hrm (by omega)]; exact hmask
  have hlt₄' : wv s₄.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx aXc) wx < X := by rw [hv₄c]; exact hlt₄
  have f04 : Frm B [xRange op wx] s.mem s₄.mem := (f₁.trans fx₃).trans fx₄
  have hb₄ : ∀ d, d + 8 ≤ op → VG.Proof.Bignum.X86_64.word s₄.mem B d = VG.Proof.Bignum.X86_64.word s.mem B d := fun d hd => f04.x_below hd ho64
  have i04 : InScr B Z s.mem s₄.mem :=
    InScr.of_frm f04 fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega
  -- `h`.
  refine wp_seqs_append (by simp [subModArr]) (by simp) (WP.mono (hTail_ok M hc₄ hX₄ hw28 hwx2 hwx
    (by rw [hY₄]; exact hyl) hlt₄' hM₄ (by rw [hb₄ _ (by unfold sQinv sFn; omega)]; exact hqp)
    (by rw [hb₄ _ (by unfold sPlen sFn; omega)]; exact hql)
    (hqs.congrK i04 (((k₁.trans k₂).trans k₃).trans k₄)) hq1 hq2 hqw hqi)
    fun s₅ ⟨hc₅, hX₅, hlt₅, hh₅, fx₅, k₅, _⟩ => ?_)
  refine WP.mono (leaveBack_ok hg hc₅ (f04.trans fx₅) hlo) fun t ⟨hg', hm', k'⟩ => ?_
  have kall := ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k'
  refine ⟨hg', by rw [hm']; exact hc₅.ws, ?_, by rw [hm']; exact hlt₅, fun hct => ?_,
    by rw [hm']; exact (f04.trans fx₅).mono fun r hr => by rw [List.mem_singleton.mp hr]; simp,
    ⟨fun r hr => ?_, kall.2⟩⟩
  · rw [show t = { t with mem := s₅.mem } by rw [← hm']]; exact ⟨hX₅.n, hX₅.inv, hX₅.one⟩
  · refine ⟨wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx, wv s₄.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx aXc) wx,
      hyc (hc hct), ?_, hlt₄', by rw [hm', hh₅ hct, hY₄]⟩
    -- `aXc₁ = R_p²`, so `aXc₄ R_p ≡ m_q R_p²`.
    have h1 : wv s₁.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx aXc) wx % X = 2 ^ (64 * wx * 2) % X :=
      VG.Proof.Bignum.mont_cancel hRR (by
        rw [hv₁, ← Nat.mod_mod_of_dvd _ (hc hct), hN.r2, Nat.mod_mod_of_dvd _ (hc hct), e2, ← Nat.pow_add])
    apply VG.Proof.Bignum.mont_cancel hRx
    rw [hv₄c, hm₄, hC₃, hxc₃, Nat.mul_mod, h1, ← Nat.mul_mod, Nat.mul_assoc _ (2 ^ (64 * wx)), ← Nat.pow_add]
    congr 3; omega
  · by_cases h : r = .rdi
    · subst h; rw [hg'.rdi, hg.rdi]
    · exact kall.1 r (by simp only [mmRegs, List.mem_cons, List.mem_append] at hr ⊢; simp_all)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.IfmaBranch`. -/
section

/-!
# RSA with AVX512_IFMA on x86-64: the IFMA branch

`ifmaBranch_ok`: from the checks (`CrtReady`) of a modulus of 32 words and
primes of 16, `pre`, `ifma` and `post` leave what `qPart` and `pPart` leave
(`PDone`), and MXCSR's bits 15:0.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma (D sIfma)

/-- Ranges that keep `n`'s values and header but `aAcc`, `aTmp`, `aY`, `aX`,
`sD` and `sCnt`: those of `gRanges`, `aX`, and anything above `n`'s arrays. -/
def NSafe (w : Nat) (rs : List (Nat × Nat)) : Prop :=
  ∀ r ∈ rs, r ∈ gRanges w ∨ r = (VG.Proof.Bignum.X86_64.slot w Public.aX, 8 * (w + 2)) ∨ VG.Proof.Bignum.X86_64.slot w 8 ≤ r.1

theorem NSafe.append {w : Nat} {rs rs' : List (Nat × Nat)} (h : VG.Proof.Bignum.X86_64.NSafe w rs) (h' : VG.Proof.Bignum.X86_64.NSafe w rs') :
    VG.Proof.Bignum.X86_64.NSafe w (rs ++ rs') := fun r hr => (List.mem_append.mp hr).elim (h r) (h' r)

theorem nsafe_wv {m m' : Mem} {B : Addr} {w : Nat} {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (hr : VG.Proof.Bignum.X86_64.NSafe w rs) {j : Nat} (hj : j < 8) (h1 : j ≠ Public.aAcc) (h2 : j ≠ Public.aTmp) (h3 : j ≠ Public.aY)
    (h4 : j ≠ Public.aX) (hz : VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64) : wv m' B (VG.Proof.Bignum.X86_64.slot w j) w = wv m B (VG.Proof.Bignum.X86_64.slot w j) w := by
  have := slot_le (w := w) hj
  refine hf.wv_eq (fun r hr' => ?_) (by omega)
  rcases hr r hr' with h | h | h
  · have := slot_sep (w := w) h1
    have := slot_sep (w := w) h2
    have := slot_sep (w := w) h3
    have := hdr_lt_slot w j (show Crt.sD < 32 by decide)
    have := hdr_lt_slot w j (show Public.sCnt < 32 by decide)
    simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] at * <;> omega
  · subst h; have := slot_sep (w := w) h4; simp only; omega
  · exact .inl (by omega)

theorem nsafe_word {m m' : Mem} {B : Addr} {w : Nat} {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (hr : VG.Proof.Bignum.X86_64.NSafe w rs) {i : Nat} (hi : i < 32) (h1 : i ≠ Crt.sD) (h2 : i ≠ Public.sCnt) :
    VG.Proof.Bignum.X86_64.word m' B (8 * i) = VG.Proof.Bignum.X86_64.word m B (8 * i) := by
  have := hdr_lt_slot w 8 hi
  refine hf.word_eq (fun r hr' => ?_) (by omega)
  rcases hr r hr' with h | h | h
  · have := hdr_lt_slot w Public.aAcc hi
    have := hdr_lt_slot w Public.aTmp hi
    have := hdr_lt_slot w Public.aY hi
    simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact .inl (by omega)
    · exact .inl (by omega)
    · exact .inl (by omega)
    · show 8 * i + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ 8 * i
      unfold Crt.sD sFn at h1 ⊢; omega
    · show 8 * i + 8 ≤ 8 * Public.sCnt ∨ 8 * Public.sCnt + 8 ≤ 8 * i
      unfold Public.sCnt sFn at h2 ⊢; omega
  · subst h; have := hdr_lt_slot w Public.aX hi; exact .inl (by simp only; omega)
  · exact .inl (by omega)

theorem NVals.of_nsafe {s t : State} {B : Addr} {w : Nat} {minv : BitVec 64} {N : Nat} (h : NVals s B w minv N)
    {rs : List (Nat × Nat)} (hf : Frm B rs s.mem t.mem) (hr : VG.Proof.Bignum.X86_64.NSafe w rs) (hz : VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64) (hw : 1 ≤ w) :
    NVals t B w minv N := by
  have lN := slot_le (w := w) (show Public.aN < 8 by decide)
  have hN0 := hdr_lt_slot w Public.aN (show 31 < 32 by decide)
  have e := fun {j} (hj : j < 8) h1 h2 h3 h4 => VG.Proof.Bignum.X86_64.nsafe_wv (j := j) hf hr hj h1 h2 h3 h4 hz
  refine ⟨by rw [e (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.n, ?_,
    by rw [e (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.r2,
    by rw [e (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.r2lt,
    by rw [e (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.one⟩
  have := (wv_mod64 t.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) (n := w) hw).symm
  rw [this, e (by decide) (by decide) (by decide) (by decide) (by decide), wv_mod64 s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) hw]
  exact h.inv

/-- After `pre` and `ifma`: `q`'s result `C^dq mod q` and `p`'s `C^dp R_p`. -/
structure IDone (s t : State) (B : Addr) (Z w op oq a : Nat) (minv mp mq : BitVec 64) (N C P Q : Nat)
    (dpp dqp qip : Addr) (pl ql : Nat) (dpb dqb : List Byte) (Mk : Bool) : Prop where
  good : Good t B Z w minv
  nv : NVals t B w minv N
  msk : VG.Proof.Bignum.X86_64.word t.mem B (8 * Public.sMask) = VG.Proof.Bignum.X86_64.mask Mk
  im : IMem t.mem B w op oq a minv mp mq (VG.Proof.Bignum.X86_64.mask Mk) (if Mk then P else 3) (if Mk then Q else 3) dpp dqp pl ql
  qlt : wv t.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 < if Mk then Q else 3
  qval : Mk = true → wv t.mem (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 = C ^ Spec.Rsa.os2ip dqb % Q
  plt : wv t.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 < if Mk then P else 3
  pval : Mk = true → wv t.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 % P = C ^ Spec.Rsa.os2ip dpb * 2 ^ (64 * 16) % P
  qi : VG.Proof.Bignum.X86_64.word t.mem B (8 * sQinv) = qip
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs s t

theorem preRanges_nsafe {w op wp oq wq : Nat} (hp : VG.Proof.Bignum.X86_64.slot w 8 ≤ op) (hq : VG.Proof.Bignum.X86_64.slot w 8 ≤ oq) :
    VG.Proof.Bignum.X86_64.NSafe w (preRanges w op wp oq wq) := fun r hr => by
  simp only [preRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | rfl | rfl | rfl
  · exact .inl hr
  · exact .inr (.inl rfl)
  · exact .inr (.inr (by simp only [xRange]; omega))
  · exact .inr (.inr (by simp only [xRange]; omega))

theorem above_nsafe {w L : Nat} {rs : List (Nat × Nat)} (hL : VG.Proof.Bignum.X86_64.slot w 8 ≤ L) (hr : ∀ r ∈ rs, L ≤ r.1) :
    VG.Proof.Bignum.X86_64.NSafe w rs := fun r h => .inr (.inr (by have := hr r h; omega))

theorem ifmaR_ge {op oq a : Nat} (hpq : op ≤ oq) (hqa : oq ≤ a) : ∀ r ∈ ifmaR op oq a, op ≤ r.1 := by
  simp only [ifmaR, shiftRanges, k1Ranges, resRanges, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only <;> omega

/-- What `pre` leaves (`pre_ok`), from `s`. -/
def APost (s t : State) (B : Addr) (Z w op oq wp : Nat) (minv mp mq : BitVec 64) (N P Q C : Nat) : Prop :=
  Good t B Z w minv ∧ NVals t B w minv N ∧ PrimeRdy t B op wp mp N P C ∧ PrimeRdy t B oq wp mq N Q C ∧
    Frm B (preRanges w op wp oq wp) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t ∧
    VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Bignum.X86_64.off B op) (8 * sMaskX) = VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off B op) (8 * sMaskX)

/-- `ifma`, after `pre`. -/
theorem branchA2_ok {s t₀ s₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : VG.Proof.Bignum.X86_64.CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : VG.Proof.Bignum.X86_64.CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 32) (hpl : wsWords pl = 16) (hql : wsWords ql = 16)
    (hZa : offQ ((k + 7) / 8) pl + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 + 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8 ≤ Z)
    (hA : VG.Proof.Bignum.X86_64.APost t₀ s₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) 16 minv mp mq
      (Spec.Rsa.os2ip nb) (if Mk then Spec.Rsa.os2ip pb else 3) (if Mk then Spec.Rsa.os2ip qb else 3)
      (Spec.Rsa.os2ip xb)) :
    WP isa (seqs CrtIfma.ifma) s₁ fun t =>
      VG.Proof.Bignum.X86_64.IDone s t B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl)
        (offQ ((k + 7) / 8) pl + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16) minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dpp dqp qip pl ql dpb dqb Mk ∧
      t.mxcsr = s₁.mxcsr &&& 0xFFFF := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := VG.Proof.Bignum.X86_64.crt_bounds h hv
  have hk1 := h.k1
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.z
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := VG.Proof.Bignum.X86_64.mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  have hpl' : pl ≤ 128 := by unfold wsWords at hpl; omega
  have hql' : ql ≤ 128 := by unfold wsWords at hql; omega
  have hop : offP ((k + 7) / 8) = VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 := rfl
  have hoq : offQ ((k + 7) / 8) pl = VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 := by
    unfold offQ; rw [hpl]
  rw [hql] at hZq
  have pws := hr.pws
  have pxv := hr.pxv
  have qws := hr.qws
  have qxv := hr.qxv
  rw [hpl] at pws pxv
  rw [hql] at qws qxv
  have hh₀ : ∀ i < 32, hFixed i = true → VG.Proof.Bignum.X86_64.word t₀.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := hr.hfix
  obtain ⟨hg₁, hN₁, rp, rq, f₁, k₁, mk₁⟩ := hA
  have ns₁ := VG.Proof.Bignum.X86_64.preRanges_nsafe (w := (k + 7) / 8) (wp := 16) (wq := 16) (le_refl (offP ((k + 7) / 8)))
    (show VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ offQ ((k + 7) / 8) pl by rw [hoq]; omega)
  have hz : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have hpr : ∀ r ∈ preRanges ((k + 7) / 8) (offP ((k + 7) / 8)) 16 (offQ ((k + 7) / 8) pl) 16,
      r.1 + r.2 ≤ offQ ((k + 7) / 8) pl + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 := fun r hr => by
    simp only [preRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | rfl | rfl | rfl
    · have := (gRanges_lt _ r hr).2; rw [hoq]; omega
    · have := slot_le (w := (k + 7) / 8) (show Public.aX < 8 by decide); rw [hoq]; simp only; omega
    · simp only [xRange]; omega
    · simp only [xRange]; rw [hoq, hop]; omega
  have i₀₁ : InScr B Z t₀.mem s₁.mem := InScr.of_frm f₁ fun r hr => by have := hpr r hr; omega
  have hb₁ : ∀ i < 32, i ≠ Crt.sD → i ≠ Public.sCnt → VG.Proof.Bignum.X86_64.word s₁.mem B (8 * i) = VG.Proof.Bignum.X86_64.word t₀.mem B (8 * i) :=
    fun i hi h1 h2 => VG.Proof.Bignum.X86_64.nsafe_word f₁ ns₁ hi h1 h2
  have hf₁ : ∀ i < 32, hFixed i = true → VG.Proof.Bignum.X86_64.word s₁.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi hf => by
    have h1 : i ≠ Crt.sD := by rintro rfl; revert hf; decide
    have h2 : i ≠ Public.sCnt := by rintro rfl; revert hf; decide
    rw [hb₁ i hi h1 h2, hh₀ i hi hf]
  have kk₁ := hr.keep.trans k₁
  have ip : IPre s₁.mem B ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) minv mp mq (VG.Proof.Bignum.X86_64.mask Mk)
      (if Mk then P else 3) (if Mk then Q else 3) dpp dqp dpb.length dqb.length :=
    ⟨hg₁.hdr, by rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsP,
      by rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsQ, rp.ws, rq.ws, rp.x.n, rp.x.inv, rp.x.one,
      rq.x.n, rq.x.inv, rq.x.one, mk₁.trans hr.pmask, by rw [hf₁ _ (by decide) (by decide)]; exact h.hDp,
      by rw [hf₁ _ (by decide) (by decide), h.dpl]; exact h.hPl, by rw [hf₁ _ (by decide) (by decide)]; exact h.hDq,
      by rw [hf₁ _ (by decide) (by decide), h.dql]; exact h.hQl⟩
  -- `ifma`.
  refine WP.mono (ifma_ok (K := (if Mk then P else 3) ∣ N ∧ (if Mk then Q else 3) ∣ N) (wp := 16) hg₁.scr hg₁.rdi
    ip (le_refl _) (by rw [hoq, hop]) rfl (by omega) rfl hP'.2 hQ'.2 rp.ylt rq.ylt rp.clt rq.clt
    (fun hK => rp.cv hK.1) (fun hK => rq.cv hK.2) (fun hK => rp.yv hK.1) (fun hK => rq.yv hK.2)
    (h.dp.congrK (hr.iscr.trans i₀₁) kk₁) (h.dq.congrK (hr.iscr.trans i₀₁) kk₁) (by rw [h.dpl]; exact hpl1)
    (by rw [h.dpl]; exact hpl') (by rw [h.dql]; exact hql1) (by rw [h.dql]; exact hql'))
    fun t ⟨m₂, qlt, qv, plt, pv, f₂, d₂, k₂, mx₂⟩ => ?_
  have hge : ∀ r ∈ [(offP ((k + 7) / 8) + 8 * sIfma, 8), (offQ ((k + 7) / 8) pl + 8 * sIfma, 8)] ++
      ifmaR (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) (offQ ((k + 7) / 8) pl + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16),
      offP ((k + 7) / 8) ≤ r.1 := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only; omega
      · simp only; rw [hoq, hop]; omega
    · exact VG.Proof.Bignum.X86_64.ifmaR_ge (by rw [hoq, hop]; omega) (by omega) r hr
  have hlZ : ∀ r ∈ [(offP ((k + 7) / 8) + 8 * sIfma, 8), (offQ ((k + 7) / 8) pl + 8 * sIfma, 8)] ++
      ifmaR (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) (offQ ((k + 7) / 8) pl + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16),
      r.1 + r.2 ≤ Z := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have hZa' := hZa
      rw [hoq] at hZa'
      rcases hr with rfl | rfl
      · simp only [sIfma, sFn]; rw [hop]; omega
      · simp only [sIfma, sFn]; rw [hoq]; omega
    · have := ifmaR_le (by rw [hoq, hop]) (le_refl _) r hr; omega
  have hb₂ : ∀ d, d + 8 ≤ offP ((k + 7) / 8) → VG.Proof.Bignum.X86_64.word t.mem B d = VG.Proof.Bignum.X86_64.word s₁.mem B d := fun d hd =>
    word_below_frm f₂ hge hd (by omega)
  have hMK : Mk = true → (if Mk then P else 3) ∣ N ∧ (if Mk then Q else 3) ∣ N := fun hm => by
    obtain ⟨_, hpq, _⟩ := hMk' hm
    simp only [hm, ↓reduceIte]
    exact ⟨⟨Q, hpq.symm⟩, ⟨P, by rw [← hpq, Nat.mul_comm]⟩⟩
  rw [h.dpl, h.dql] at m₂
  refine ⟨⟨⟨hg₁.scr.congr k₂.2.2, d₂, m₂.nh⟩, hN₁.of_nsafe f₂ (VG.Proof.Bignum.X86_64.above_nsafe (le_refl _) hge) hz (by omega),
    by rw [hb₂ _ (by unfold Public.sMask sFn; omega), hb₁ _ (by decide) (by decide) (by decide)]; exact hr.msk,
    m₂, qlt, fun hm => ?_, plt, fun hm => ?_,
    by rw [hb₂ _ (by unfold sQinv sFn; omega), hf₁ _ (by decide) (by decide)]; exact h.hQi,
    fun i hi hf => by rw [hb₂ _ (by have := hdr_lt_slot ((k + 7) / 8) 8 hi; omega), hf₁ i hi hf],
    (hr.iscr.trans i₀₁).trans (InScr.of_frm f₂ hlZ), (kk₁.trans k₂).mono (by simp [mmRegs])⟩,
    mx₂⟩
  · have := qv (hMK hm); simp only [hm, ↓reduceIte] at this; exact this
  · have := pv (hMK hm); simp only [hm, ↓reduceIte] at this; exact this


/-- `pre` and `ifma`, from the checks. -/
theorem branchA_ok (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : VG.Proof.Bignum.X86_64.CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : VG.Proof.Bignum.X86_64.CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 32) (hpl : wsWords pl = 16) (hql : wsWords ql = 16)
    (hZa : offQ ((k + 7) / 8) pl + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 + 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8 ≤ Z)
    (hpre : (seqs (CrtIfma.pre M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (seqs (CrtIfma.pre M.mm ++ CrtIfma.ifma)) t₀ fun t =>
      VG.Proof.Bignum.X86_64.IDone s t B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl)
        (offQ ((k + 7) / 8) pl + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16) minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dpp dqp qip pl ql dpb dqb Mk ∧
      t.mxcsr = t₀.mxcsr &&& 0xFFFF := by
  have hA2 := fun s₁ => VG.Proof.Bignum.X86_64.branchA2_ok (s₁ := s₁) h hv hr hMk hw32 hpl hql hZa
  obtain ⟨hodd, hN1, hPN, hQN⟩ := VG.Proof.Bignum.X86_64.crt_bounds h hv
  have hk1 := h.k1
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.z
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := VG.Proof.Bignum.X86_64.mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  have hpl' : pl ≤ 128 := by unfold wsWords at hpl; omega
  have hql' : ql ≤ 128 := by unfold wsWords at hql; omega
  have hop : offP ((k + 7) / 8) = VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 := rfl
  have hoq : offQ ((k + 7) / 8) pl = VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 := by
    unfold offQ; rw [hpl]
  rw [hql] at hZq
  have pws := hr.pws
  have pxv := hr.pxv
  have qws := hr.qws
  have qxv := hr.qxv
  rw [hpl] at pws pxv
  rw [hql] at qws qxv
  have hh₀ : ∀ i < 32, hFixed i = true → VG.Proof.Bignum.X86_64.word t₀.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := hr.hfix
  -- `pre`.
  refine wp_seqs_append (by simp [CrtIfma.pre, CrtIfma.prep]) (by simp [CrtIfma.ifma]) (WP.mono_mx hpre
    (pre_ok M (wp := 16) hr.good (by omega) (le_refl _) (by rw [hoq]) (by omega) (by decide)
      (by omega) hr.wsP hr.wsQ pws qws hr.nv hr.xm pxv hP'.1 hP'.2 qxv hQ'.1 hQ'.2)
    fun s₁ hA mx₁ => WP.mono (hA2 s₁ hA) fun t ⟨hd, mx⟩ =>
      ⟨hd, by rw [mx, mx₁]⟩)

/-- `x` with `x R ≡ X`, for `R` invertible modulo `N > 1`. -/
theorem exists_mont' {R N : Nat} (hR : Nat.Coprime R N) (hN1 : 1 < N) (X : Nat) :
    ∃ x, X % N = x * R % N := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hR hN1
  refine ⟨X * m, ?_⟩
  rw [Nat.mul_assoc, Nat.mul_mod, Nat.mul_comm m R, hm, Nat.mul_one, Nat.mod_mod]

/-- `post`, after `pre` and `ifma`: what `pPart` leaves. -/
theorem branchB_ok (M : Mont) {s t₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : VG.Proof.Bignum.X86_64.CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hd : VG.Proof.Bignum.X86_64.IDone s t₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl)
        (offQ ((k + 7) / 8) pl + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16) minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dpp dqp qip pl ql dpb dqb Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 32) (hpl : wsWords pl = 16) (hql : wsWords ql = 16)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (seqs (CrtIfma.post M.mm)) t₁ fun t => VG.Proof.Bignum.X86_64.PDone s t B Z ((k + 7) / 8) pl ql minv mp mq
      (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb Mk ∧
      t.mxcsr = t₁.mxcsr := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := VG.Proof.Bignum.X86_64.crt_bounds h hv
  have hk1 := h.k1
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.z
  have hqil := h.qil
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize hQIe : Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := VG.Proof.Bignum.X86_64.mask_facts hMk hodd hPN hQN
  have hn := hd.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hpl' : pl ≤ 128 := by unfold wsWords at hpl; omega
  have hop : offP ((k + 7) / 8) = VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 := rfl
  have hoq : offQ ((k + 7) / 8) pl = VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 + VG.Proof.Bignum.X86_64.slot (wsWords pl) 8 + tabBytes (wsWords pl) := rfl
  have hW8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords pl) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hm := hd.im
  -- The multiplier of `R_p` in `p`'s `aY`: `C^dp` for a key that passed the checks.
  obtain ⟨x0, hx0⟩ := VG.Proof.Bignum.X86_64.exists_mont' (VG.Proof.Bignum.coprime_pow2 hP'.2 (64 * wsWords pl)) hP'.1
    (wv t₁.mem (VG.Proof.Bignum.X86_64.off B (offP ((k + 7) / 8))) (VG.Proof.Bignum.X86_64.slot (wsWords pl) Public.aY) (wsWords pl))
  refine WP.mono_mx hpost (VG.Proof.Bignum.X86_64.post_ok M (wx := wsWords pl) (op := offP ((k + 7) / 8))
    (oq := offQ ((k + 7) / 8) pl) (mx := mp) (mq := mq) (X := if Mk then P else 3)
    (m1 := if Mk then C ^ Spec.Rsa.os2ip dpb else x0) (c := Mk) (qib := qib) hd.good (by omega) hd.nv
    (by rw [hpl]; omega) hm.wsQ (by rw [hpl]; exact hm.qws) (by have := hZq; rw [hql] at this; rw [hpl]; exact this)
    (le_refl _) (by rw [hoq, hop]) (by rw [hpl]; decide) hm.wsP
    (by rw [hpl]; exact hm.pws) (by rw [hpl]; exact ⟨hm.pn, hm.pinv, hm.pone⟩) hP'.1 hP'.2
    (by rw [hpl]; exact hd.plt) (fun _ => ?_) hm.pmk
    (fun hm' => by obtain ⟨_, hpq, _⟩ := hMk' hm'; simp only [hm', ↓reduceIte]; exact ⟨Q, hpq.symm⟩) hd.qi
    (by rw [hqil]; exact hm.pl) (h.qi.congrK hd.iscr hd.keep) (by rw [hqil]; exact hpl1) (by rw [hqil]; omega)
    (by rw [hqil, hpl]; omega)
    (fun hm' => by obtain ⟨_, _, hqi⟩ := hMk' hm'; simp only [hm', ↓reduceIte, hQIe]; exact hqi))
    fun t ⟨hg', hws', hX', hlt', hh', f', k'⟩ mx' => ?_
  · by_cases hmk : Mk
    · simp only [hmk, ↓reduceIte]
      rw [hpl]
      exact hd.pval hmk
    · simp only [hmk, Bool.false_eq_true, ↓reduceIte] at hx0 ⊢
      exact hx0
  have hz : VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have ns : VG.Proof.Bignum.X86_64.NSafe ((k + 7) / 8) (gRanges ((k + 7) / 8) ++
      [(VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) Public.aX, 8 * ((k + 7) / 8 + 2)), xRange (offP ((k + 7) / 8)) (wsWords pl)]) :=
    fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact .inl hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (.inl rfl)
        · exact .inr (.inr (by simp only [xRange]; omega))
  have hqZ : offQ ((k + 7) / 8) pl + VG.Proof.Bignum.X86_64.slot 16 8 ≤ 2 ^ 64 := by
    have := hZq; rw [hql] at this; omega
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hqk : ∀ d, offQ ((k + 7) / 8) pl ≤ d → d + 8 ≤ 2 ^ 64 → VG.Proof.Bignum.X86_64.word t.mem B d = VG.Proof.Bignum.X86_64.word t₁.mem B d :=
    fun d hd' hd'' => f'.word_eq (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact .inr (by have := (gRanges_lt _ r hr).2; rw [hoq] at hd'; omega)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · have := slot_le (w := (k + 7) / 8) (show Public.aX < 8 by decide); simp only; rw [hoq] at hd'; omega
        · simp only [xRange]; rw [hoq] at hd'; omega) hd''
  have hqv : ∀ d n, d + 8 * n ≤ VG.Proof.Bignum.X86_64.slot 16 8 → wv t.mem (VG.Proof.Bignum.X86_64.off B (offQ ((k + 7) / 8) pl)) d n =
      wv t₁.mem (VG.Proof.Bignum.X86_64.off B (offQ ((k + 7) / 8) pl)) d n := fun d n hdn => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hqk _ (by omega) (by omega)
  have hY8 := slot_le (w := 16) (show Public.aY < 8 by decide)
  have hN8 := slot_le (w := 16) (show Public.aN < 8 by decide)
  refine ⟨⟨hg', by rw [VG.Proof.Bignum.X86_64.nsafe_word f' ns (by decide) (by decide) (by decide)]; exact hd.msk,
    by rw [VG.Proof.Bignum.X86_64.nsafe_word f' ns (by decide) (by decide) (by decide)]; exact hm.wsP,
    by rw [VG.Proof.Bignum.X86_64.nsafe_word f' ns (by decide) (by decide) (by decide)]; exact hm.wsQ, hws',
    (show WsAt t₁.mem B (offQ ((k + 7) / 8) pl) (wsWords ql) mq by rw [hql]; exact hm.qws).of_words fun i hi => by
      rw [word_off, word_off]; exact hqk _ (by omega) (by omega),
    by rw [hql, hqv _ _ (by omega)]; exact hm.qn, by rw [hql, hqv _ _ (by omega)]; exact hd.qlt,
    fun hmk => by rw [hql, hqv _ _ (by omega)]; exact hd.qval hmk, hlt', fun hmk => ?_,
    hd.hfix.trans fun i hi hf => by
      have h1 : i ≠ Crt.sD := by rintro rfl; revert hf; decide
      have h2 : i ≠ Public.sCnt := by rintro rfl; revert hf; decide
      exact VG.Proof.Bignum.X86_64.nsafe_word f' ns hi h1 h2,
    hd.iscr.trans (InScr.of_frm f' fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · have := (gRanges_lt _ r hr).2; omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · have := slot_le (w := (k + 7) / 8) (show Public.aX < 8 by decide); simp only; omega
        · simp only [xRange]; rw [hoq] at hZq; rw [hop]; omega),
    (hd.keep.trans k').mono (by simp [mmRegs])⟩, mx'⟩
  obtain ⟨a, b, ha, hb, hbP, hh⟩ := hh' hmk
  simp only [hmk, ↓reduceIte] at ha hb hbP hh
  rw [show wv t₁.mem (VG.Proof.Bignum.X86_64.off B (offQ ((k + 7) / 8) pl)) (VG.Proof.Bignum.X86_64.slot (wsWords pl) Public.aY) (wsWords pl) =
    wv t₁.mem (VG.Proof.Bignum.X86_64.off B (offQ ((k + 7) / 8) pl)) (VG.Proof.Bignum.X86_64.slot 16 Public.aY) 16 by rw [hpl], hd.qval hmk] at hb
  exact ⟨a, b, ha, hb, hbP, by rw [hh, hQIe]⟩

end VG.Proof.Bignum.X86_64

end
