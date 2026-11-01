module
public import VerifiedGarbage.Impl.Bignum.Arm.SharedR2
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.R2
import VerifiedGarbage.Proof.Bignum.Arm.R2Init
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Block

/-! The existing R-squared construction, with its squares called once shared. -/
@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)
theorem sharedR2Square_ok {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (s : State) {m k : Nat} (h : R2Sq base len w m k s) (hp : P s) :
    WP isa (K.op 4 4 4) s fun t => R2Sq base len w m (2 * k) t ∧
      P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.ready.width ▸ h.ready.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have odd : m % 2 = 1 := h.modulus ▸ numAt_odd_of_inverse s.mem _ (by omega) h.ready.inverse
  refine WP.mono (K.op_ok s 4 4 4 h.ready hp op4 op4 op4 (by decide) (by rw [h.modulus]; exact h.operand)) ?_
  rintro t ⟨ready, modulus, bound, value, keeps, pt, frame, rest⟩
  rw [h.modulus] at modulus bound value
  refine ⟨⟨ready, modulus, bound, r2_square_value odd h.value value, ?_, ?_⟩, pt, frame, rest⟩
  · have := keeps_array_word (d := 0) (bits := 32) keeps fits op7 (by decide) (by omega)
    simp only [Nat.add_zero] at this
    change (t.mem.readW (off (State.addr base) (arrAt w 7)) 32).toNat = 2
    rw [this]; exact h.two
  · rw [keeps_header_readW keeps size (d := 208) (bits := 32) (by decide)]; exact h.counter

/-- The six squarings. -/
theorem sharedR2Squares_ok {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (s : State) {m : Nat} (h : R2Sq base len w m w s) (hp : P s) :
    WP isa (SharedR2.squares K.op) s fun t => R2Sq base len w m (64 * w) t ∧
      P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  unfold SharedR2.squares
  refine WP.seq (WP.mono (sharedR2Square_ok K s h hp) fun s1 ⟨h1, p1, f1, r1⟩ => ?_)
  refine WP.seq (WP.mono (sharedR2Square_ok K s1 h1 p1) fun s2 ⟨h2, p2, f2, r2⟩ => ?_)
  refine WP.seq (WP.mono (sharedR2Square_ok K s2 h2 p2) fun s3 ⟨h3, p3, f3, r3⟩ => ?_)
  refine WP.seq (WP.mono (sharedR2Square_ok K s3 h3 p3) fun s4 ⟨h4, p4, f4, r4⟩ => ?_)
  refine WP.seq (WP.mono (sharedR2Square_ok K s4 h4 p4) fun s5 ⟨h5, p5, f5, r5⟩ => ?_)
  refine WP.mono (sharedR2Square_ok K s5 h5 p5) fun t ⟨h6, p6, f6, r6⟩ => ?_
  refine ⟨?_, p6, f1.trans (f2.trans (f3.trans (f4.trans (f5.trans f6)))),
    r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6))))⟩
  have e : 2 * (2 * (2 * (2 * (2 * (2 * w))))) = 64 * w := by omega
  rw [e] at h6
  exact h6

theorem sharedR2_ok {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (s : State)
    (h : ArithmeticReady base len w s) (hp : P s) (countFits : 128 * w < 2 ^ 32) :
    WP isa (SharedR2.r2 K.op) s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  rw [SharedR2.r2, WP.seq_iff]
  refine WP.mono (r2Init_ok s h) ?_
  rintro u ⟨ready, one, modulus, frame, rest⟩
  have pU := K.stable frame rest hp
  rw [WP.seq_iff]
  refine WP.mono (r2Loop_ok u ready one (by rw [modulus]; exact h.modulus) countFits) ?_
  rintro v ⟨sq, frameV, restV⟩
  rw [modulus] at sq
  have pV := K.stable frameV restV pU
  refine WP.mono (sharedR2Squares_ok K v sq pV) ?_
  rintro t ⟨fin, pT, frameT, restT⟩
  have exact : numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % numAt s.mem (State.addr base) w 0 := by
    rw [← Nat.mod_eq_of_lt fin.operand, fin.value, show 64 * w + 64 * w = 128 * w by omega]
  refine ⟨⟨fin.ready.workspace, fin.ready.layout, fin.ready.width, fin.ready.ptr, fin.ready.inverse,
      by rw [fin.modulus]; exact fin.operand, fin.two, fin.counter, fin.ready.stackRead,
      fin.ready.stackSep, fin.ready.saved⟩, exact, fin.modulus,
    pT, (Frame.mono (frame.trans frameV) (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact K.workspace)).trans frameT, rest.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm
