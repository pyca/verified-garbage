module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtBack
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtUnitPc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# `vg_rsa_private_crt_precomputed` on x86-64: the primes' phases

`q`'s and `p`'s phases taking `R_X mod X` from `pre` (`qPartPc_ok`,
`pPartPc_ok`): their results are right if `ok` and `pre` holds `R_X mod X`
for the true primes.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

theorem qPhase_pc (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) : qPhase mul ex true =
    (Crt.gPow mul sWsQ ++ ([.block [.mov .rdi (.mem (hdr sWsQ))]] : List (Prog isa)) ++
      Crt.loadPre Public.aY Crt.offQ ++ ([.block [leave]] : List (Prog isa))) ++
    ([mul Public.aY Public.aXm Public.aY] ++
      (powSteps mul ex sWsQ sDq sQlen ++ [mul Public.aY Public.aY Public.aOne, .block [leave]])) := by
  simp only [qPhase, unit, powSteps, enterQ, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append]

/-- `q`'s phase, from the checks, with `R_q mod q` from word `2 w + w_p` of
`pre`. -/
theorem qPartPc_ok (M : Mont) (E : CrtExpL M) {s t₀ : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    {minv mp mq : BitVec 64} {Mk : Bool} {ok : Prop} {P : Addr} {W : Nat}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk ok)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hpre : PreSrc s B Z P W) (hW : 2 * ((k + 7) / 8) + wsWords pl + wsWords ql ≤ W)
    (hY : ok → wv s.mem P (8 * (2 * ((k + 7) / 8) + wsWords pl)) (wsWords ql) =
      2 ^ (64 * wsWords ql) % Spec.Rsa.os2ip qb) :
    WP isa (seqs (qPhase M.mm E.code true)) t₀ fun t => QReady s t B Z ((k + 7) / 8) pl ql minv mp mq
      (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dqb Mk ok := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  obtain ⟨-, -, hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl1 := h.pl1
  have hpl2 := h.pl2
  have hql1 := h.ql1
  have hql2 := h.ql2
  have hZq := h.z
  have hn := hr.good.scr.nowrap
  have hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega
  have hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega
  have hwq := wsWords_le (len := ql) (w := (k + 7) / 8) (by omega) (by omega)
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega
  have hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hloq : slot ((k + 7) / 8) 8 ≤ offQ ((k + 7) / 8) pl := by unfold offQ; omega
  have hz : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by unfold offQ at hZq; omega
  have hp₀ := hpre.congrK hr.iscr hr.keep (by decide)
  have hl : ∀ d, d + 8 ≤ Z → InRegions (t₀.rd ++ t₀.wr) (off B d) 8 := fun d hd => hr.good.scr.ld hd
  rw [qPhase_pc]
  refine qPartWith_ok M E h hv hr hMk (by simp) (okY := wv t₀.mem P (8 * (2 * ((k + 7) / 8) + wsWords pl))
    (wsWords ql) = 2 ^ (64 * wsWords ql) % if Mk then Spec.Rsa.os2ip qb else 3) (fun hok hm => by
      rw [hpre.wv_eq hr.iscr (by omega), hY hok]; simp only [hm, ↓reduceIte]) ?_
  refine unitPhasePc_ok M hr.good (by omega) (by omega) hloq
    (by have := tabBytes_le_wsTab (wsWords ql); omega) hwq2 hwq (by decide) (by decide) (by decide) hr.wsQ hr.qws
    hr.nv hodd hN1 hr.qxv hQ'.1 hp₀ (by omega) fun t hdi hrd hwr hlk hf => ?_
  -- The offset, from `n`'s header and `p`'s.
  have hpk : word t.mem (off B (offP ((k + 7) / 8))) (8 * sW) = BitVec.ofNat 64 (wsWords pl) := by
    rw [word_off, hf.word_eq (fun r hr' => by
      rcases List.mem_append.mp hr' with hr' | hr'
      · exact .inr (by have := gRanges_le ((k + 7) / 8) r hr'; unfold offP; omega)
      · rw [List.mem_singleton.mp hr']; exact .inl (by simp only [xRange]; unfold offP offQ sW; omega))
      (by unfold offP offQ sW at *; omega), ← word_off]
    exact hr.pws.hdr.hw
  refine offQ_ok hdi (by rw [hrd, hwr, off_off]; exact hl _ (by unfold sLink sFn offQ at *; omega)) hlk
    (by rw [hrd, hwr]; exact hl _ (by unfold sW; omega))
    (by rw [hf.gx_hdr hloq (by decide) (by decide) (by decide)]; exact hr.good.hdr.hw)
    (by rw [hrd, hwr]; exact hl _ (by unfold sWsP sFn; omega))
    (by rw [hf.gx_hdr hloq (by decide) (by decide) (by decide)]; exact hr.wsP)
    (by rw [hrd, hwr, off_off]; exact hl _ (by unfold sW offP offQ at *; omega)) hpk

theorem pPhase_pc (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) : pPhase mul ex true =
    (Crt.gPow mul sWsP ++ ([.block [.mov .rdi (.mem (hdr sWsP))]] : List (Prog isa)) ++
      Crt.loadPre Public.aY Crt.offP ++ ([.block [leave]] : List (Prog isa))) ++
    (mqSteps mul ++ ([mul Public.aY Public.aXm Public.aY] ++
      (powSteps mul ex sWsP sDp sPlen ++ (([.block [leave]] : List (Prog isa)) ++ hSteps mul)))) := by
  simp only [pPhase, unit, powSteps, mqSteps, hSteps, enterP, ↓reduceIte, List.append_assoc, List.cons_append,
    List.nil_append]

/-- `p`'s phase, from `q`'s, with `R_p mod p` from word `2 w` of `pre`. -/
theorem pPartPc_ok (M : Mont) (E : CrtExpL M) {s t₁ : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    {minv mp mq : BitVec 64} {Mk : Bool} {ok : Prop} {P : Addr} {W : Nat}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : QReady s t₁ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dqb Mk ok)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hpre : PreSrc s B Z P W) (hW : 2 * ((k + 7) / 8) + wsWords pl ≤ W)
    (hY : ok → wv s.mem P (8 * (2 * ((k + 7) / 8))) (wsWords pl) = 2 ^ (64 * wsWords pl) % Spec.Rsa.os2ip pb) :
    WP isa (seqs (pPhase M.mm E.code true)) t₁ fun t => PDone s t B Z ((k + 7) / 8) pl ql minv mp mq
      (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb Mk ok := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  obtain ⟨-, hP', -⟩ := mask_facts hMk hodd hPN hQN
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl1 := h.pl1
  have hpl2 := h.pl2
  have hZq := h.z
  have hn := hr.good.scr.nowrap
  have hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega
  have hwp := wsWords_le (len := pl) (w := (k + 7) / 8) (by omega) (by omega)
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hlop : slot ((k + 7) / 8) 8 ≤ offP ((k + 7) / 8) := le_refl _
  have hp₁ := hpre.congrK hr.iscr hr.keep (by decide)
  have hl : ∀ d, d + 8 ≤ Z → InRegions (t₁.rd ++ t₁.wr) (off B d) 8 := fun d hd => hr.good.scr.ld hd
  rw [pPhase_pc]
  refine pPartWith_ok M E h hv hr hMk (by simp) (okY := wv t₁.mem P (8 * (2 * ((k + 7) / 8)))
    (wsWords pl) = 2 ^ (64 * wsWords pl) % if Mk then Spec.Rsa.os2ip pb else 3) (fun hok hm => by
      rw [hpre.wv_eq hr.iscr (by omega), hY hok]; simp only [hm, ↓reduceIte]) ?_
  refine unitPhasePc_ok M hr.good (by omega) (by omega) hlop
    (by have := tabBytes_le_wsTab (wsWords pl); unfold offQ offP at *; omega) hwp2 hwp (by decide) (by decide)
    (by decide) hr.wsP hr.pws hr.nv hodd hN1 hr.pxv hP'.1 hp₁ (by omega) fun t hdi hrd hwr hlk hf => ?_
  exact offP_ok hdi (by rw [hrd, hwr, off_off]; exact hl _ (by unfold sLink sFn offP offQ at *; omega)) hlk
    (by rw [hrd, hwr]; exact hl _ (by unfold sW offQ at *; omega))
    (by rw [hf.gx_hdr hlop (by decide) (by decide) (by decide)]; exact hr.good.hdr.hw)

end VG.Proof.Bignum.X86_64
