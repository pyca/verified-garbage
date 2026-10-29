module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Body
public import VerifiedGarbage.Impl.Ffdh.X86_64.Exchange
public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Arithmetic

import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Output
/-! # FFDH exchange on x86-64: correctness and ABI -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Exchange/Main.lean`, which only this module imported.
section

/-! # FFDH exchange on x86-64: compose the arithmetic and output -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Exchange

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)

theorem StepPost.trans {p : ExP} {s u t : State} {P Q : State → Prop}
    (h : StepPost p s P u) (h' : StepPost p u Q t) : StepPost p s Q t :=
  ⟨h'.1, h.2.1.trans h'.2.1, fun i hi => (h'.2.2.1 i hi).trans (h.2.2.1 i hi),
    keep_trans h.2.2.2 h'.2.2.2⟩

def RunFrame (p : ExP) (m m' : Mem) : Prop :=
  ∀ x, p.Z ≤ ofs p.B x → (∀ i < p.k, x ≠ p.op + BitVec.ofNat 64 i) → m' x = m x

def MainPost (p : ExP) (xb : List Byte) (s t : State) : Prop :=
  Spec.Rsa.bytesAt t.mem p.op p.k = Spec.Rsa.i2osp (if p.fl xb then p.z xb else 0) p.k ∧
    t.gpr .rax = bit (p.fl xb) ∧ t.gpr .rdi = p.B ∧ RunFrame p s.mem t.mem ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧
    Keep (.rdi :: mmRegs) s t

private theorem main_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.Exchange.main M.mm E.code (.seq (.block r2Head) R.code) =
      seqs ((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++
        (([.seq (.block r2Head) R.code] : List (Prog isa)) ++
          (pow M.mm E.code sY sK sX sXl ++ (range aY ++
            ([.block VG.Impl.Ffdh.X86_64.Domain.Exchange.finBlk, storeBE,
              .block [.mov .rax (.mem (hdr sF)), leave]] : List (Prog isa)))))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.Exchange.main, List.append_assoc]

theorem main_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {p : ExP} {xb : List Byte} {s : State}
    (hb : Base p xb s) (hdi : s.gpr .rdi = p.B) (hm : p.mv = true) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.Exchange.main M.mm E.code (.seq (.block r2Head) R.code)) s
      (MainPost p xb s) := by
  rw [main_eq]
  refine wp_seqs_append (by simp [pSetup]) (by simp) (WP.mono (setup_entered hb hdi hm) fun u₁ h₁ => ?_)
  refine wp_seqs_cons (by simp [pow]) (WP.mono (entered_ready M R h₁.1 hm) fun u₂ h₂ => ?_)
  refine wp_seqs_append (a := pow M.mm E.code sY sK sX sXl) (by simp [pow]) (by simp [range, gt1, ltArr, cmpArr])
    (WP.mono (ready_value M E h₂.1) fun u₃ h₃ => ?_)
  refine wp_seqs_append (a := range aY) (by simp [range, gt1, ltArr, cmpArr]) (by simp)
    (WP.mono (value_checked h₃.1) fun u₄ h₄ => ?_)
  have H := ((h₁.trans h₂).trans h₃).trans h₄
  exact WP.mono (output_ok h₄.1) fun t ⟨hb, ha, hd, hf, hs, k⟩ =>
    ⟨hb, ha, hd, fun x hx hi => (hf x hi).trans (H.2.1 x hx),
      fun i hi => (hs i hi).trans (H.2.2.1 i hi), keep_trans H.2.2.2 k⟩

end VG.Proof.Ffdh.X86_64.Exchange
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Exchange

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Spec.Ffdh

/-- Convert the arithmetic's range flag and encoding to the shared operation. -/
theorem main_post {s u t : State} (c : ExCtx s) (hb : Base (exOf s) (exX s) u)
    (hm : (exOf s).mv = true) (h : MainPost (exOf s) (exX s) u t) : exPost s t := by
  intro hd hpv
  have hpk : (domainOf (exOf s).k (exOf s).dom).p = (exOf s).P :=
    rfl
  have hp1 := valid_facts hm hb.k1
  have hlo : 256 ^ ((exOf s).k - 1) ≤ (exOf s).P := by
    have := hm
    unfold ExP.mv Spec.Rsa.modulusValid at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  have hhi : (exOf s).P < 256 ^ (exOf s).k := by
    have := os2ip_lt (exOf s).pb
    rw [hb.plen] at this
    exact this
  have hk := octets_bitLength (by have := hb.k1; omega) hlo hhi
  have hfl : (exOf s).fl (exX s) ↔ (1 < (exOf s).z (exX s) ∧ (exOf s).z (exX s) < (exOf s).P - 1) := by
    unfold ExP.fl
    rw [lt_pm1 hp1.1]
  change Spec.Rsa.written t.mem (exOf s).op (s.gpr .rsi).toNat ((t.gpr .rax).setWidth 32)
    (exchangeOp (domainOf (exOf s).k (exOf s).dom) (Spec.Rsa.os2ip (exX s)) (Spec.Rsa.os2ip (exOf s).yb))
  change publicValid ⟨domainOf (exOf s).k (exOf s).dom, Spec.Rsa.os2ip (exOf s).yb⟩ = true at hpv
  rw [c.ol]
  change Spec.Rsa.written t.mem (exOf s).op (exOf s).k ((t.gpr .rax).setWidth 32)
    (exchangeOp (domainOf (exOf s).k (exOf s).dom) (Spec.Rsa.os2ip (exX s)) (Spec.Rsa.os2ip (exOf s).yb))
  rw [exchangeOp_eq (k := (exOf s).k) hpv (by rw [hpk]; have := hp1.2.1; omega)
    (by rw [hpk]; exact hk), h.2.1]
  rw [hpk]
  by_cases hf : 1 < (exOf s).z (exX s) ∧ (exOf s).z (exX s) < (exOf s).P - 1
  · rw [ite_eq_left hf]
    exact ⟨by unfold bit; rw [ite_eq_left (hfl.mpr hf)]; rfl,
      by rw [h.1, ite_eq_left (hfl.mpr hf)]⟩
  · rw [ite_eq_right hf]
    exact ⟨by unfold bit; rw [ite_eq_right (mt hfl.mp hf)]; rfl,
      by rw [h.1, ite_eq_right (mt hfl.mp hf), i2osp_zero']⟩

/-- The body has not yet restored the six ABI registers. -/
theorem body_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {s : State} (hpre : exPre s) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.Exchange.body M.mm E.code (.seq (.block r2Head) R.code)) s fun t =>
      exPost s t ∧ t.gpr .rdi = (exOf s).B ∧ RunFrame (exOf s) s.mem t.mem ∧
      (∀ i < 6, word t.mem (exOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧ Keep (.rdi :: mmRegs) s t := by
  have c := exCtx_of hpre
  unfold VG.Impl.Ffdh.X86_64.Domain.Exchange.body
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (entry_base c) fun u ⟨hb, hdi, hi, hs, k⟩ => ?_
  refine WP.mono (dom_base hb hdi) fun v ⟨hb', hz, hd, hi', hs', k'⟩ => ?_
  have H := hi.trans hi'
  have K := keep_trans k k'
  have hS : ∀ i < 6, word v.mem (exOf s).B (8 * i) = s.gpr (saved.getD i .rax) :=
    fun i hi => (hs' i hi).trans (hs i hi)
  refine WP.ite (!(exOf s).mv) (by simp [eval, hz]) (fun hf => ?_) (fun hf => ?_)
  · have hm : (exOf s).mv = false := by simpa only [Bool.not_eq_true'] using hf
    refine WP.mono (ret_ok v (r := 0) (by decide)) fun t ⟨_, hmem, kk⟩ =>
      ⟨?_, (kk.gpr (by decide)).trans hd, (fun x hx _ => by rw [hmem]; exact H x hx),
        (fun i hi => by rw [hmem]; exact hS i hi), keep_trans K (kk.mono (by decide))⟩
    intro hv _
    have hm' := domainValid_mod hv
    have hp : (domainOf (exOf s).k (exOf s).dom).p = (exOf s).P := rfl
    change Spec.Rsa.modulusValid (domainOf (exOf s).k (exOf s).dom).p (exOf s).k = true at hm'
    rw [hp] at hm'
    change (exOf s).mv = true at hm'
    rw [hm] at hm'
    contradiction
  · have hm : (exOf s).mv = true := by simpa only [Bool.not_eq_false'] using hf
    exact WP.mono (main_ok M E R hb' hd hm) fun t hh =>
      ⟨main_post c hb' hm hh, hh.2.2.1, (fun x hx ho => (hh.2.2.2.1 x hx ho).trans (H x hx)),
        (fun i hi => (hh.2.2.2.2.1 i hi).trans (hS i hi)), keep_trans K hh.2.2.2.2.2⟩

/-- The full operation, including return-address protection and MXCSR. -/
theorem ex_correct (M : Mont) (E : CrtExpL M) (R : R2Impl M)
    (hmx : (VG.Impl.Ffdh.X86_64.Domain.Exchange.code M.mm E.code (.seq (.block r2Head) R.code)).allInstrs
      (fun i => !loadsMxcsr i) = true) (s : State) (h : exContract.pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.X86_64.Domain.Exchange.code M.mm E.code (.seq (.block r2Head) R.code)) s tr t ∧
      abiPreserved s t ∧ exContract.post s t := by
  have hpre := h
  have c := exCtx_of h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hRetOut, _, _, _, hRetScr, _⟩ := h
  suffices hw : WP isa (VG.Impl.Ffdh.X86_64.Domain.Exchange.code M.mm E.code (.seq (.block r2Head) R.code)) s
      fun t => gprPreserved s t ∧ exContract.post s t by
    obtain ⟨tr, t, he, hg, hp⟩ := hw
    exact ⟨tr, t, he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold VG.Impl.Ffdh.X86_64.Domain.Exchange.code
  refine WP.seq (WP.mono (body_ok M E R hpre) fun u ⟨hp, hd, hf, hs, k⟩ => ?_)
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (exit_ok (c.hs.congr k.2.2) hd (by omega) hs)
    fun t ⟨hRestore, hm, kk⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact (kk.gpr (by decide)).trans (k.gpr (by decide))
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
  · rw [hm]
    apply Mem.readW_congr
    intro i hi
    refine hf _ (out_scr hRetScr (contains_byte (s.gpr .rsp) hi (by decide))) ?_
    intro j hj he
    have hx := out_scr hRetOut (contains_byte (s.gpr .rsp) hi (by decide))
    rw [he] at hx
    change (s.gpr .rsi).toNat ≤ ofs (s.gpr .rdi) (s.gpr .rdi + BitVec.ofNat 64 j) at hx
    have hj64 : j < 2 ^ 64 := by
      have hk2 := c.k2
      change j < (s.gpr .r8).toNat at hj
      omega
    have ho : ofs (s.gpr .rdi) (s.gpr .rdi + BitVec.ofNat 64 j) = j := by
      change (s.gpr .rdi + BitVec.ofNat 64 j - s.gpr .rdi).toNat = j
      exact Mem.sub_ofNat_toNat _ hj64
    rw [ho] at hx
    have := c.ol
    dsimp only [exOf] at hj
    omega
  · intro hv hy
    change Spec.Rsa.written t.mem _ _ _ _
    rw [hm, kk.gpr (show .rax ∉ saved by decide)]
    exact hp hv hy

end VG.Proof.Ffdh.X86_64.Exchange
