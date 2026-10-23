module

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
