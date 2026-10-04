import VerifiedGarbage.Proof.Bignum.X86_64.CrtHdr

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
  scr : Scr s B Z
  rdi : s.gpr .rdi = B
  z : offQ ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes (wsWords ql) ≤ Z
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

theorem nSetup_eq (M : Mont) : nSetup M.mm =
    (loadSteps ++ restSteps) ++ (r2Steps M ++ [M.mm Public.aXm Public.aX Public.aR2]) := rfl

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
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega
  have hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have hZs : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, r.1 + r.2 ≤ slot ((k + 7) / 8) 8) → ∀ r ∈ rs, r.1 + r.2 ≤ Z :=
    fun h' r hr => (h' r hr).trans hZ
  rw [nSetup_eq]
  -- The modulus, the input, `-n⁻¹`, 1 and the mask of `c < n`.
  refine wp_seqs_append (by simp [loadSteps]) (by simp [r2Steps])
    (WP.mono (setup_ok h.scr h.rdi hZ (by omega) (by omega) h.hK h.hN h.hIn h.n h.x h.nl h.xl hodd)
      fun t₁ ⟨minv, so, f₁, k₁⟩ => ?_)
  -- `R² mod n`.
  refine wp_seqs_append (by simp [r2Steps]) (by simp)
    (WP.mono (r2_ok M so.good hZ (by omega) (by omega) so.n so.inv so.r12 so.r10 hodd hlo)
      fun t₂ ⟨hg₂, hlt₂, hr₂, f₂, k₂⟩ => ?_)
  have hX₂ : wv t₂.mem B (slot ((k + 7) / 8) Public.aX) ((k + 7) / 8) = Spec.Rsa.os2ip xb := by
    rw [f₂.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.x
  have hN₂ : wv t₂.mem B (slot ((k + 7) / 8) Public.aN) ((k + 7) / 8) = Spec.Rsa.os2ip nb := by
    rw [f₂.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.n
  have hI₂ : ((word t₂.mem B (slot ((k + 7) / 8) Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [f₂.r2_word hn' (by decide) (by decide) (by decide) (by decide)]; exact so.inv
  have hO₂ : wv t₂.mem B (slot ((k + 7) / 8) Public.aOne) ((k + 7) / 8) = 1 := by
    rw [f₂.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.one
  -- `c R mod n`.
  simp only [seqs]
  refine WP.mono (mmN_ok M hg₂ hZ (by omega) (by omega) (o := Public.aXm) (a := Public.aX) (b := Public.aR2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hN₂ hI₂ hlt₂)
    fun t₃ ⟨hg₃, hN₃, hI₃, hlt₃, hm₃, ha₃, k₃⟩ => ?_
  have hR : Nat.Coprime (2 ^ (64 * ((k + 7) / 8))) (Spec.Rsa.os2ip nb) := VG.Proof.Bignum.coprime_pow2 hodd _
  have hxm₃ : wv t₃.mem B (slot ((k + 7) / 8) Public.aXm) ((k + 7) / 8) % Spec.Rsa.os2ip nb =
      Spec.Rsa.os2ip xb * 2 ^ (64 * ((k + 7) / 8)) % Spec.Rsa.os2ip nb := by
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₃, hX₂, Nat.mul_mod, hr₂, ← Nat.mul_mod, Nat.mul_assoc]
  have g₃ : Frm B [(slot ((k + 7) / 8) Public.aAcc, 8 * ((k + 7) / 8 + 2)),
      (slot ((k + 7) / 8) Public.aTmp, 8 * ((k + 7) / 8 + 2)),
      (slot ((k + 7) / 8) Public.aXm, 8 * ((k + 7) / 8 + 2))] t₂.mem t₃.mem :=
    Frm.of_arrays ha₃ fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> simp
  have kg₃ : ∀ r ∈ [(slot ((k + 7) / 8) Public.aAcc, 8 * ((k + 7) / 8 + 2)),
      (slot ((k + 7) / 8) Public.aTmp, 8 * ((k + 7) / 8 + 2)),
      (slot ((k + 7) / 8) Public.aXm, 8 * ((k + 7) / 8 + 2))], KeepsHdr r ∧ r.1 + r.2 ≤ slot ((k + 7) / 8) 8 := by
    have := hdr_lt_slot ((k + 7) / 8) Public.aAcc (show 31 < 32 by decide)
    have := hdr_lt_slot ((k + 7) / 8) Public.aTmp (show 31 < 32 by decide)
    have := hdr_lt_slot ((k + 7) / 8) Public.aXm (show 31 < 32 by decide)
    have := slot_le (w := (k + 7) / 8) (show Public.aAcc < 8 by decide)
    have := slot_le (w := (k + 7) / 8) (show Public.aTmp < 8 by decide)
    have := slot_le (w := (k + 7) / 8) (show Public.aXm < 8 by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl) <;> exact ⟨keepsHdr_ge (by simp only; omega), by simp only; omega⟩
  have e2 : word t₂.mem B (8 * Public.sMask) = word t₁.mem B (8 * Public.sMask) :=
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
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega
  have hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hh₃ : ∀ i < 32, hFixed i = true → word t₃.mem B (8 * i) = word s.mem B (8 * i) := hr.hfix
  refine WP.mono (primesSetup_ok hr.good (by omega) (by omega) hZq
    (by rw [hh₃ _ (by decide) (by decide)]; exact h.hPl) (by rw [hh₃ _ (by decide) (by decide)]; exact h.hQl)
    (by rw [hh₃ _ (by decide) (by decide)]; exact h.hP) (by rw [hh₃ _ (by decide) (by decide)]; exact h.hQ)
    (by rw [hh₃ _ (by decide) (by decide)]; exact h.hQi) (h.p.congrK hr.iscr hr.keep) (h.q.congrK hr.iscr hr.keep)
    (h.qi.congrK hr.iscr hr.keep) h.pbl h.qbl h.qil h.pl1 (by have := h.pl2; omega) h.ql1 (by have := h.ql2; omega))
    fun t₄ ⟨hg₄, hsP₄, hsQ₄, ⟨mp, hwp₄⟩, ⟨mq, hwq₄⟩, hp₄, hc₄, hq₄, f₄, k₄⟩ => ?_
  have kf₄ : ∀ r ∈ [(8 * sWsP, 8), (8 * sWsQ, 8), (offP ((k + 7) / 8), slot (wsWords pl) 8 + tabBytes (wsWords pl) + slot (wsWords ql) 8)],
      KeepsHdr r ∧ r.1 + r.2 ≤ Z ∧ (slot ((k + 7) / 8) 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * 31) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl)
    · exact ⟨keepsHdr_slot (by decide) (by decide), by simp only [sWsP, sFn]; omega,
        Or.inr (by simp only [sWsP, sFn]; omega)⟩
    · exact ⟨keepsHdr_slot (by decide) (by decide), by simp only [sWsQ, sFn]; omega,
        Or.inr (by simp only [sWsQ, sFn]; omega)⟩
    · exact ⟨keepsHdr_ge (by simp only [offP]; omega), by simp only [offP]; unfold offQ at hZq; omega,
        Or.inl (by simp only [offP]; omega)⟩
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
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega
  have hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega
  have hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega
  refine WP.mono (checks_ok hr.n.good (by omega) (by omega) (le_refl _) (by unfold offQ; omega)
    (by unfold offQ at hZq ⊢; omega) hwp2 (wsWords_le (by have := h.pl2; omega) (by omega)) hwq2
    (wsWords_le (by have := h.ql2; omega) (by omega)) hr.wsP hr.wsQ hr.pws hr.qws hr.n.nv.n hr.n.msk hr.pv hr.qv
    hr.qiv hodd)
    fun t ⟨hg, hMt, hsPt, hsQt, ⟨mp', hwpt, hxpt, hmpt⟩, ⟨mq', hwqt, hxqt⟩, f₅, k₅⟩ => ?_
  have kf₅ : ∀ r ∈ [(slot ((k + 7) / 8) Public.aAcc, 8 * (2 * ((k + 7) / 8) + 2)), (8 * Public.sMask, 8),
      (offP ((k + 7) / 8), slot (wsWords pl) 8), (offQ ((k + 7) / 8) pl, slot (wsWords ql) 8)],
      KeepsHdr r ∧ r.1 + r.2 ≤ Z := by
    have := accs_le ((k + 7) / 8)
    have := hdr_lt_slot ((k + 7) / 8) Public.aAcc (show 31 < 32 by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl)
    · exact ⟨keepsHdr_ge (by simp only; omega), by simp only; omega⟩
    · exact ⟨keepsHdr_slot (by decide) (by decide), by simp only [Public.sMask, sFn]; omega⟩
    · exact ⟨keepsHdr_ge (by simp only [offP]; omega), by simp only [offP]; unfold offQ at hZq; omega⟩
    · exact ⟨keepsHdr_ge (by simp only [offQ]; omega), by simp only; omega⟩
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
      have : slot ((k + 7) / 8) Public.aN + 8 ≤ slot ((k + 7) / 8) Public.aAcc := by
        unfold slot Public.aN Public.aAcc; omega
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

end VG.Proof.Bignum.X86_64
