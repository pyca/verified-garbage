module

public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Start
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Start
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.ArithmeticBridge
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.OutputBytes
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Outputs
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Output
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Math
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Math

/-! ### `Ffdh.X86_64.DerivePublic.Main`, which only this module used -/

section

/-! # FFDH public-value derivation on x86-64: the scalar test, the power and y -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.DerivePublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.CheckPrivate (KpP Base Work StepPost)

/-- 2 for a scalar out of range; else the power's range flag selects 1 or 3. -/
def dvStatus (p : KpP) (xb : List Byte) : Nat := if p.sv then if p.fl xb then 1 else 3 else 2

/-- Only scratch and y change. -/
def DvFrame (p : KpP) (m m' : Mem) : Prop :=
  ∀ a, p.Z ≤ ofs p.B a → (∀ i < p.k, a ≠ off p.yp i) → m' a = m a

theorem DvFrame.trans {p : KpP} {m₁ m₂ m₃ : Mem} (h₁ : DvFrame p m₁ m₂) (h₂ : DvFrame p m₂ m₃) :
    DvFrame p m₁ m₃ := fun a ha hy => (h₂ a ha hy).trans (h₁ a ha hy)

theorem DvFrame.of_scr {p : KpP} {m m' : Mem} (h : InScr p.B p.Z m m') : DvFrame p m m' :=
  fun a ha _ => h a ha

theorem DvFrame.of_y {p : KpP} {m m' : Mem} (h : ∀ a, (∀ i < p.k, a ≠ off p.yp i) → m' a = m a) :
    DvFrame p m m' := fun a _ hy => h a hy

def MainPost (p : KpP) (xb : List Byte) (s t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (dvStatus p xb) ∧ t.gpr .rdi = p.B ∧
    Spec.Rsa.bytesAt t.mem p.yp p.k = Spec.Rsa.i2osp (if dvStatus p xb = 1 then p.z xb else 0) p.k ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ DvFrame p s.mem t.mem ∧
    Keep (.rdi :: mmRegs) s t

theorem status_ok {s : State} {P : Prop} [Decidable P] (ha : s.gpr .rax = bit P) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.DerivePublic.status) s fun t =>
      (t.gpr .rax = BitVec.ofNat 64 (if P then 1 else 3) ∧ t.mem = s.mem) ∧ Keep [.rax, .rdx] s t := by
  rw [GenerateKey.bit_eq_bool] at ha
  refine WP.keep _ ?_ rfl
  unfold VG.Impl.Ffdh.X86_64.Domain.DerivePublic.status
  xrun [ha]
  by_cases h : P <;> simp only [h, decide_true, decide_false, ↓reduceIte] <;> rfl

/-- Key generation's public output, for private-key validation's power. -/
theorem public_ok {p : KpP} {xb : List Byte} {s : State} (h : CheckPrivate.Value p xb s) (ho : YOut p s) :
    WP isa (seqs GenerateKey.publicOutput) s fun t =>
      Spec.Rsa.bytesAt t.mem p.yp p.k = Spec.Rsa.i2osp (if p.fl xb then p.z xb else 0) p.k ∧
      t.gpr .rax = bit (p.fl xb) ∧ t.gpr .rdi = p.B ∧ DvFrame p s.mem t.mem ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ Keep (.rdi :: mmRegs) s t := by
  unfold GenerateKey.publicOutput
  refine wp_seqs_cons (by simp [range])
    (WP.mono (GenerateKey.value_bridge h ho) fun u ⟨hu, hi₁, hs₁, k₁⟩ => ?_)
  refine wp_seqs_append (a := range aY) (by simp [range]) (by simp)
    (WP.mono (Exchange.value_checked hu) fun v ⟨hv, hi₂, hs₂, k₂⟩ => ?_)
  refine WP.mono (Exchange.output_ok hv) fun t ⟨hy, hflag, hd, hf, hs₃, k₃⟩ => ?_
  refine ⟨hy, hflag, hd, fun a ha hn => ?_, fun i hi => ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [hf a hn, hi₂ a ha, hi₁ a ha]
  · have a₁ : word u.mem p.B (8 * i) = word s.mem p.B (8 * i) := hs₁ i hi
    have a₂ : word v.mem p.B (8 * i) = word u.mem p.B (8 * i) := hs₂ i hi
    have a₃ : word t.mem p.B (8 * i) = word v.mem p.B (8 * i) := hs₃ i hi
    rw [a₃, a₂, a₁]

/-- The checked generator's power over x, written as y with its status. -/
theorem tail_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {p : KpP} {xb : List Byte} {mi : BitVec 64}
    {s : State} (h : Work p xb mi s) (hd : s.gpr .rdi = off p.B (inner p.w)) (hm : p.mv = true)
    (ho : YOut p s) :
    WP isa (seqs (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.tail M.mm E.code (.seq (.block r2Head) R.code))) s
      fun t => t.gpr .rax = BitVec.ofNat 64 (if p.fl xb then 1 else 3) ∧ t.gpr .rdi = p.B ∧
        Spec.Rsa.bytesAt t.mem p.yp p.k = Spec.Rsa.i2osp (if p.fl xb then p.z xb else 0) p.k ∧
        (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ DvFrame p s.mem t.mem ∧
        Keep (.rdi :: mmRegs) s t := by
  unfold VG.Impl.Ffdh.X86_64.Domain.DerivePublic.tail
  simp only [List.append_assoc]
  refine wp_seqs_append (a := [.seq (.block r2Head) R.code]) (by simp) (by simp)
    (WP.mono (CheckPrivate.work_ready M R h hd hm) fun u ⟨hu, hi₁, hs₁, k₁⟩ => ?_)
  refine wp_seqs_append (a := pow M.mm E.code sG sK sX sXl)
    (b := GenerateKey.publicOutput ++ [.block VG.Impl.Ffdh.X86_64.Domain.DerivePublic.status])
    (by simp [pow]) (by simp)
    (WP.mono (CheckPrivate.ready_value M E hu) fun v ⟨hv, hi₂, hs₂, k₂⟩ => ?_)
  refine wp_seqs_append (a := GenerateKey.publicOutput) (by simp [GenerateKey.publicOutput]) (by simp)
    (WP.mono (public_ok hv ((ho.of_wr k₁.2.2).of_wr k₂.2.2)) fun z ⟨hy, hax, hdz, hf, hs₃, k₃⟩ => ?_)
  simp only [seqs]
  refine WP.mono (status_ok hax) fun t ⟨⟨ha, hmt⟩, k₄⟩ => ?_
  refine ⟨ha, (k₄.gpr (by decide)).trans hdz, by rw [hmt]; exact hy, fun i hi => ?_, ?_,
    (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  · have a₁ : word u.mem p.B (8 * i) = word s.mem p.B (8 * i) := hs₁ i hi
    have a₂ : word v.mem p.B (8 * i) = word u.mem p.B (8 * i) := hs₂ i hi
    rw [hmt, hs₃ i hi, a₂, a₁]
  · intro a ha hn
    rw [hmt, hf a ha hn, hi₂ a ha, hi₁ a ha]

theorem main_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.DerivePublic.main M.mm E.code (.seq (.block r2Head) R.code) =
      seqs (((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++
        VG.Impl.Rsa.X86_64.Crt.loadArr aXm sX sXl) ++
          (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange ++
            ([.block [.alu .test .rax (.reg .rax)], .ite .e (retInner 2)
              (seqs (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.tail M.mm E.code (.seq (.block r2Head) R.code)))] :
              List (Prog isa)))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.DerivePublic.main, List.append_assoc]

theorem main_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {p : KpP} {xb : List Byte} {s : State}
    (h : Base p xb s) (hy : YOut p s) (hyb : p.yb = List.replicate p.k 0) (hd : s.gpr .rdi = p.B)
    (hG : word s.mem p.B (8 * sG) = off p.dp p.k) (hQ : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k))
    (hm : p.mv = true) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.main M.mm E.code (.seq (.block r2Head) R.code)) s
      (MainPost p xb s) := by
  rw [main_eq]
  have hodd := (valid_facts hm h.k1).1
  refine wp_seqs_append (by simp [pSetup, VG.Impl.Rsa.X86_64.Crt.loadArr]) (by simp)
    (WP.mono (CheckPrivate.setup_work h hd hG hQ hm) fun u₁ S₁ => ?_)
  obtain ⟨mi, hw₁, hd₁⟩ := S₁.1
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange)
    (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange, isNonzero, geArr, cmpArr]) (by simp)
    (WP.mono (CheckPrivate.scalar_ok hw₁ hd₁ hodd) fun u₂ S₂ => ?_)
  have hw₂ := S₂.1.1
  have hd₂ := S₂.1.2.1
  simp only [seqs]
  refine WP.seq (WP.mono (test_bit_ok S₂.1.2.2) fun u₃ ⟨hz, hmem, k⟩ => ?_)
  have hw₃ := hw₂.keep hmem k
  have hd₃ := (k.gpr (by decide)).trans hd₂
  have S₃ : StepPost p u₂ (fun _ => True) u₃ := ⟨trivial, by rw [hmem]; exact InScr.refl _ _ _,
    (fun _ _ => by rw [hmem]), k.mono (by decide)⟩
  have H := (S₁.trans S₂).trans S₃
  have hy₃ : YOut p u₃ := hy.of_wr H.2.2.2.2.2
  refine WP.ite (!decide (p.sv = true)) (by simp [eval, hz]) (fun hs => ?_) (fun hs => ?_)
  · have hsv : p.sv = false := by cases h : p.sv <;> simp_all
    unfold retInner
    refine WP.seq (WP.mono (leave_ok (hw₃.mem.ctx hd₃)) fun u₄ ⟨hd₄, hm₄, k₄⟩ => ?_)
    refine WP.mono (ret_ok u₄ (r := 2) (by decide)) fun t ⟨ha, hm₅, k₅⟩ => ?_
    have hst : dvStatus p xb = 2 := by simp only [dvStatus, hsv, Bool.false_eq_true, ↓reduceIte]
    have hyt : Spec.Rsa.bytesAt t.mem p.yp p.k = List.replicate p.k 0 := by
      have hb := GenerateKey.bytes_src hw₃.base.y
      rw [hm₅, hm₄]
      rwa [hyb, List.length_replicate] at hb
    refine ⟨by rw [ha, hst], (k₅.gpr (by decide)).trans hd₄, ?_, fun i hi => ?_,
      fun a ha _ => ?_, keep_trans H.2.2.2 ((k₄.trans k₅).mono (by decide))⟩
    · rw [hyt, hst, ite_eq_right (by decide), i2osp_zero']
    · rw [hm₅, hm₄]; exact H.2.2.1 i hi
    · rw [hm₅, hm₄]; exact H.2.1 a ha
  · have hsv : p.sv = true := by cases h : p.sv <;> simp_all
    refine WP.mono (tail_ok M E R hw₃ hd₃ hm hy₃) fun t ⟨ha, hd', hyt, hs', hf', k'⟩ => ?_
    have hst : dvStatus p xb = if p.fl xb then 1 else 3 := by simp only [dvStatus, hsv, ↓reduceIte]
    refine ⟨by rw [hst]; exact ha, hd', ?_, fun i hi => (hs' i hi).trans (H.2.2.1 i hi),
      (DvFrame.of_scr H.2.1).trans hf', keep_trans H.2.2.2 k'⟩
    rw [hyt, hst]
    by_cases hf : p.fl xb
    · rw [ite_eq_left hf, ite_eq_left hf, ite_eq_left rfl]
    · rw [ite_eq_right hf, ite_eq_right hf, ite_eq_right (by decide)]

end VG.Proof.Ffdh.X86_64.DerivePublic

end

end


/-! # FFDH public-value derivation on x86-64: correctness and ABI -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.DerivePublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.CheckPrivate (KpP Base)
open VG.Spec.Ffdh

theorem dvStatus_eq {p : KpP} {xb : List Byte} {s : State} (h : Base p xb s)
    (hm : p.mv = true) (ha : parametersValid p.params = true) :
    dvStatus p xb = keyStatus p.params (Spec.Rsa.os2ip xb) := by
  cases hsv : p.sv with
  | false =>
    have hx : privateValid p.params (Spec.Rsa.os2ip xb) = false := h.valid.trans hsv
    have hr := (VG.Proof.Ffdh.keyStatus_scalar p.params (Spec.Rsa.os2ip xb)).mpr hx
    simpa only [dvStatus, hsv, Bool.false_eq_true, ↓reduceIte] using hr.symm
  | true =>
    have hx : privateValid p.params (Spec.Rsa.os2ip xb) = true := h.valid.trans hsv
    rw [VG.Proof.Ffdh.keyStatus_power ha _ hx]
    simp only [dvStatus, hsv, ↓reduceIte]
    congr 1
    apply propext
    change (1 < p.z xb ∧ 2 * (p.z xb / 2) + 1 < p.P) ↔ _
    rw [lt_pm1 (valid_facts hm h.k1).1]
    rfl

theorem dvStatus_lt (p : KpP) (xb : List Byte) : dvStatus p xb < 2 ^ 32 := by
  unfold dvStatus
  split
  · split <;> decide
  · decide

theorem main_spec {p : KpP} {xb : List Byte} {s u t : State} (hb : Base p xb u)
    (hm : p.mv = true) (ha : parametersValid p.params = true) (h : MainPost p xb s t) :
    ((t.gpr .rax).setWidth 32).toNat = keyStatus p.params (Spec.Rsa.os2ip xb) ∧
      if keyStatus p.params (Spec.Rsa.os2ip xb) = 1 then
        Spec.Rsa.bytesAt t.mem p.yp p.k =
          Spec.Rsa.i2osp (Spec.Rsa.powMod p.params.g (Spec.Rsa.os2ip xb) p.params.p) p.k
      else Spec.Rsa.bytesAt t.mem p.yp p.k = List.replicate p.k 0 := by
  obtain ⟨hr, _, hy, _⟩ := h
  have hst := dvStatus_eq hb hm ha
  have hlt := dvStatus_lt p xb
  refine ⟨?_, ?_⟩
  · rw [hr]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide)), Nat.mod_eq_of_lt hlt]
    exact hst
  · rw [← hst]
    by_cases hs : dvStatus p xb = 1
    · simp only [ite_eq_left hs] at hy ⊢
      rw [VG.Proof.Bignum.powMod_eq]
      exact hy
    · simp only [ite_eq_right hs] at hy ⊢
      rw [hy, i2osp_zero']

theorem body_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {s : State} (hpre : dvPre s) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.body M.mm E.code (.seq (.block r2Head) R.code)) s
      fun t => dvPost s t ∧ t.gpr .rdi = (dvOf s).B ∧ DvFrame (dvOf s) s.mem t.mem ∧
        (∀ i < 6, word t.mem (dvOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧ Keep (.rdi :: mmRegs) s t := by
  have c := dvCtx_of hpre
  unfold VG.Impl.Ffdh.X86_64.Domain.DerivePublic.body
  refine WP.seq (WP.mono (entry_pre0 c) fun u ⟨h0, hd, hi, hs, k⟩ => ?_)
  refine WP.seq (WP.mono (zero_base h0 hd) fun u' ⟨hb, hy, hd', hf', hs', k'⟩ => ?_)
  refine WP.seq (WP.mono (CheckPrivate.dom_base hb hd') fun v ⟨hb', hz, hd'', hG, hQ, hi'', hs'', k''⟩ => ?_)
  have H : DvFrame (dvOf s) s.mem v.mem :=
    ((DvFrame.of_scr hi).trans (DvFrame.of_y hf')).trans (DvFrame.of_scr hi'')
  have K := keep_trans (keep_trans k k') k''
  have hS : ∀ i < 6, word v.mem (dvOf s).B (8 * i) = s.gpr (saved.getD i .rax) :=
    fun i hi => (hs'' i hi).trans ((hs' i hi).trans (hs i hi))
  have hyv : YOut (dvOf s) v := hy.of_wr k''.2.2
  refine WP.ite (!(dvOf s).mv) (by simp [eval, hz]) (fun hf => ?_) (fun hf => ?_)
  · have hm : (dvOf s).mv = false := by simpa only [Bool.not_eq_true'] using hf
    refine WP.mono (ret_ok v (r := 0) (by decide)) fun t ⟨_, hmem, kk⟩ =>
      ⟨?_, (kk.gpr (by decide)).trans hd'', fun a ha hn => by rw [hmem]; exact H a ha hn,
        (fun i hi => by rw [hmem]; exact hS i hi), keep_trans K (kk.mono (by decide))⟩
    intro hv
    have hm' := domainValid_mod hv
    change (dvOf s).mv = true at hm'
    rw [hm] at hm'
    contradiction
  · have hm : (dvOf s).mv = true := by simpa only [Bool.not_eq_false'] using hf
    refine WP.mono (main_ok M E R hb' hyv rfl hd'' hG hQ hm) fun t hh => ?_
    have hmain := hh
    obtain ⟨_, hdt, _, hsave, hframe, kk⟩ := hh
    refine ⟨?_, hdt, H.trans hframe, (fun i hi => (hsave i hi).trans (hS i hi)), keep_trans K kk⟩
    intro hv
    have hp : parametersValid (dvOf s).params = true := by
      unfold domainValid at hv
      exact ((Bool.and_eq_true _ _).mp hv).1
    exact main_spec hb' hm hp hmain

theorem dv_correct (M : Mont) (E : CrtExpL M) (R : R2Impl M)
    (hmx : ctlOk (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.code M.mm E.code (.seq (.block r2Head) R.code)) = true) (s : State) (h : dvContract.pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.code M.mm E.code (.seq (.block r2Head) R.code)) s tr t ∧
      abiPreserved s t ∧ dvContract.post s t := by
  have hpre := h
  have c := dvCtx_of h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hRetY, _, _, hRetScr, _⟩ := h
  suffices hw : WP isa (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.code M.mm E.code (.seq (.block r2Head) R.code)) s
      fun t => gprPreserved s t ∧ dvContract.post s t by
    obtain ⟨tr, t, he, hg, hp⟩ := hw
    exact ⟨tr, t, he, abiPreserved_of_ctl hmx he hg, hp⟩
  unfold VG.Impl.Ffdh.X86_64.Domain.DerivePublic.code
  refine WP.seq (WP.mono (body_ok M E R hpre) fun u ⟨hp, hd, hf, hs, k⟩ => ?_)
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (exit_ok (c.hs.congr k.2.2) hd (by omega_arith) hs)
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
    have hbyte := contains_byte (s.gpr .rsp) hi (by decide)
    refine hf _ (out_scr hRetScr hbyte) ?_
    intro j hj he
    exact hRetY _ hbyte (by rw [he]; exact contains_byte _ (by rw [c.yl]; exact hj) (by have := c.k2; omega_arith))
  · change dvPost s t
    unfold dvPost
    rw [kk.gpr (show .rax ∉ saved by decide), hm]
    exact hp

end VG.Proof.Ffdh.X86_64.DerivePublic
