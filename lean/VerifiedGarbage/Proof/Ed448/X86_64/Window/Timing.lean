module

public import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Mask
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed448.X86_64.Window.SignedSelect
import VerifiedGarbage.Proof.Ed448.X86_64.Window.First
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Round
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Table
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Digit
import VerifiedGarbage.Proof.X448.X86_64.Inv
import VerifiedGarbage.Proof.Ed448.X86_64.PointSums
public import VerifiedGarbage.Proof.Ed448.Formulas
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Mask
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.SignedSelect
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.First
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Round
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Table
meta import VerifiedGarbage.Proof.Ed448.X86_64.Window.Digit
meta import VerifiedGarbage.Proof.X448.X86_64.Inv
meta import VerifiedGarbage.Proof.Ed448.X86_64.PointSums
meta import VerifiedGarbage.Proof.Ed448.Formulas
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-! Verification lookups reveal only public scalar digits. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window
open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window
open VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr E Keep)
open VG.Impl.X448.X86_64 (BITS)

/-- Compose timing proofs with the single-run facts established by correctness. -/
theorem seq_same {A B : State → Prop} {p q : Prog isa}
    (hp : RelCT isa (fun x y => A x ∧ A y) p (fun _ _ => True))
    (hw : ∀ s, A s → WP isa p s B)
    (hq : RelCT isa (fun x y => B x ∧ B y) q (fun _ _ => True)) :
    RelCT isa (fun x y => A x ∧ A y) (.seq p q) (fun _ _ => True) :=
  (hp.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)).seq
    (hq.mono (fun _ _ h => h.2) (fun _ _ h => h))

def KeyDigitPre (base : Addr) (k t : Nat) (s : State) : Prop :=
  Scr s base ∧ s.gpr .rbx = BitVec.ofNat 64 t ∧ Bits base KBITS k s

theorem selectKey_ct (base : Addr) (k t : Nat) (ht : t + 5 ≤ 460) :
    RelCT isa (fun s u => KeyDigitPre base k t s ∧ KeyDigitPre base k t u)
      (.block (selectKey KBITS)) (fun _ _ => True) := by
  have hd : RelCT isa (fun s u => KeyDigitPre base k t s ∧ KeyDigitPre base k t u)
      (.block (loadDigit KBITS)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rbx]) _ (by taint_decide)
    intro s u h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.rdi.trans h.2.1.rdi.symm
    · exact h.1.2.1.trans h.2.2.1.symm
  have hw (s : State) (h : KeyDigitPre base k t s) :
      WP isa (.block (loadDigit KBITS)) s fun u =>
        u.gpr .rdi = base ∧ u.gpr .r15 = BitVec.ofNat 64 (SignedWindow.magnitude k t) := by
    refine WP.mono (loadDigit_bits_ok h.1 (by decide) (by decide) ht h.2.1 h.2.2)
      fun u ⟨hu, ku⟩ => ⟨?_, hu⟩
    exact (ku.1 _ (by decide)).trans h.1.rdi
  have tail : RelCT isa (fun s u =>
      (s.gpr .rdi = base ∧ s.gpr .r15 = BitVec.ofNat 64 (SignedWindow.magnitude k t)) ∧
      (u.gpr .rdi = base ∧ u.gpr .r15 = BitVec.ofNat 64 (SignedWindow.magnitude k t)))
      (.block (keyAddress ++ directKeyCoord 0 ++ directKeyCoord 1 ++ directKeyCoord 2))
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .r15]) _ (by taint_decide)
    intro s u h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.trans h.2.1.symm
    · exact h.1.2.trans h.2.2.symm
  have hh := (seq_same hd hw tail).block_append
  simpa only [selectKey, List.append_assoc] using hh

/-- State information needed at a fixed window position. -/
structure TimingCtx (base : Addr) (S K t : Nat) (s : State) : Prop where
  scr : Scr s base
  rbx : s.gpr .rbx = BitVec.ofNat 64 t
  bs : Bits base BITS S s
  bk : Bits base KBITS K s
  d : E s.mem base 11 = Spec.Ed448.d

theorem TimingCtx.keep {base : Addr} {S K t : Nat} {s u : State}
    (h : TimingCtx base S K t s) (hk : Keep base s u)
    (hd : E u.mem base 11 = Spec.Ed448.d) : TimingCtx base S K t u :=
  ⟨hk.scr h.scr, (hk.gpr _ (by decide)).trans h.rbx,
    h.bs.keep (by decide) (by decide) hk, h.bk.keep (by decide) (by decide) hk, hd⟩

/-- The fixed-address part of a round, before public-key selection. -/
def roundHead (v : Impl.Ed448.X86_64.FieldVariant) : Prog isa :=
  .seq (.seq (.seq (dbl5 v.bodies) selectSignedBase) v.bodies.add) (.block accept)

theorem roundHead_ok (v : Impl.Ed448.X86_64.FieldVariant) {base : Addr} {S K t : Nat}
    {s : State} (h : TimingCtx base S K t s) (ht : t + 5 ≤ 460) :
    WP isa (roundHead v) s (TimingCtx base S K t) := by
  have hP := FieldVariant.bodies_ok v
  rw [roundHead]
  apply WP.assoc'
  apply WP.assoc'
  refine WP.seq (WP.mono (dbl5_ok hP h.scr) fun a ⟨ka, _, fa⟩ => ?_)
  have ha := h.keep ka (by rw [fa 11 (by decide) (by decide), h.d])
  refine WP.seq (WP.mono (selectSignedBase_ok ha.scr ht ha.rbx ha.bs) fun b ⟨kb, _, fb⟩ => ?_)
  have hb := ha.keep kb (by rw [fb 11 (by decide) (by decide) (by decide) (by decide), ha.d])
  refine WP.seq (WP.mono (hP.add hb.scr hb.d) fun c ⟨kc, ec⟩ => ?_)
  have hc := hb.keep kc (by rw [ec]; exact hb.d)
  refine WP.mono (accept_ok hc.scr) fun u ⟨ku, _, fu⟩ => ?_
  exact hc.keep ku (by rw [fu 11 (by decide), hc.d])


private theorem ctx_agree {base : Addr} {S K t : Nat} {s u : State}
    (h : TimingCtx base S K t s ∧ TimingCtx base S K t u) :
    X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rbx]) s u := by
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.scr.rdi.trans h.2.scr.rdi.symm
  · exact h.1.rbx.trans h.2.rbx.symm

theorem selectSignedKey_ct (base : Addr) (S K t : Nat) (ht : t + 5 ≤ 460) :
    RelCT isa (fun s u => TimingCtx base S K t s ∧ TimingCtx base S K t u)
      (selectSignedKey KBITS) (fun _ _ => True) := by
  have head := (selectKey_ct base K t ht).mono
    (fun s u (h : TimingCtx base S K t s ∧ TimingCtx base S K t u) =>
      ⟨⟨h.1.scr, h.1.rbx, h.1.bk⟩, ⟨h.2.scr, h.2.rbx, h.2.bk⟩⟩) (fun _ _ h => h)
  have hw (s : State) (h : TimingCtx base S K t s) :
      WP isa (.block (selectKey KBITS)) s (TimingCtx base S K t) := by
    refine WP.mono (selectKey_ok h.scr (by decide) (by decide) ht h.rbx h.bk)
      fun u ⟨ku, _, fu⟩ => ?_
    exact h.keep ku (by rw [fu 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.d])
  apply seq_same head hw
  exact RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rbx]) (fun _ _ h => ctx_agree h) (by taint_decide)

theorem round_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) (S K t : Nat) (ht : t + 5 ≤ 460) :
    RelCT isa (fun s u => TimingCtx base S K t s ∧ TimingCtx base S K t u)
      (round v.field v.bodies KBITS) (fun _ _ => True) := by
  have head : RelCT isa (fun s u => TimingCtx base S K t s ∧ TimingCtx base S K t u)
      (roundHead v) (fun _ _ => True) := by
    cases v <;> exact relCT_sum (Taint.ofRegs [.rdi, .rbx])
      (fun _ _ h => ctx_agree h) (by taint_decide_sum [dblSum, addSum, dblAdxSum, addAdxSum])
  have hw (s : State) (h : TimingCtx base S K t s) :
      WP isa (selectSignedKey KBITS) s (TimingCtx base S K t) := by
    refine WP.mono (selectSignedKey_ok h.scr (by decide) (by decide) ht h.rbx h.bk)
      fun u ⟨ku, _, fu⟩ => ?_
    exact h.keep ku (by rw [fu 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.d])
  have tail : RelCT isa (fun s u => TimingCtx base S K t s ∧ TimingCtx base S K t u)
      (.seq (Window.add v.field v.bodies) (.block (accept ++ [.alu .test .rbx (.reg .rbx)])))
      (fun _ _ => True) := by
    cases v <;> exact relCT_sum (Taint.ofRegs [.rdi, .rbx])
      (fun _ _ h => ctx_agree h) (by taint_decide_sum [dblSum, addSum, dblAdxSum, addAdxSum])
  have hh := seq_same head (fun s h => roundHead_ok v h ht)
    (seq_same (selectSignedKey_ct base S K t ht) hw tail)
  exact hh.assoc.assoc.assoc


/-- Initialization before the first public-key lookup. -/
def firstHead : Prog isa := .seq selectSignedBase
  (.block (Impl.X448.X86_64.copyOut (Impl.X448.X86_64.slot 0) (Impl.X448.X86_64.slot 8) ++
    Impl.X448.X86_64.copyOut (Impl.X448.X86_64.slot 1) (Impl.X448.X86_64.slot 9) ++ constSlot 2 1))

theorem firstHead_ok {base : Addr} {S K t : Nat} {s : State}
    (h : TimingCtx base S K t s) (ht : t + 5 ≤ 460) :
    WP isa firstHead s (TimingCtx base S K t) := by
  refine WP.seq (WP.mono (selectSignedBase_ok h.scr ht h.rbx h.bs) fun a ⟨ka, _, fa⟩ => ?_)
  have ha := h.keep ka (by rw [fa 11 (by decide) (by decide) (by decide) (by decide), h.d])
  refine WP.mono (takeBase_ok ha.scr) fun u ⟨ku, _, fu⟩ => ?_
  exact ha.keep ku (by rw [fu 11 (by decide), ha.d])

theorem first_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) (S K t : Nat) (ht : t + 5 ≤ 460) :
    RelCT isa (fun s u => TimingCtx base S K t s ∧ TimingCtx base S K t u)
      (first v.field v.bodies KBITS) (fun _ _ => True) := by
  have head : RelCT isa (fun s u => TimingCtx base S K t s ∧ TimingCtx base S K t u)
      firstHead (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rbx]) (fun _ _ h => ctx_agree h) (by taint_decide)
  have hw (s : State) (h : TimingCtx base S K t s) :
      WP isa (selectSignedKey KBITS) s (TimingCtx base S K t) := by
    refine WP.mono (selectSignedKey_ok h.scr (by decide) (by decide) ht h.rbx h.bk)
      fun u ⟨ku, _, fu⟩ => ?_
    exact h.keep ku (by rw [fu 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.d])
  have tail : RelCT isa (fun s u => TimingCtx base S K t s ∧ TimingCtx base S K t u)
      (.seq (Window.add v.field v.bodies) (.block accept)) (fun _ _ => True) := by
    cases v <;> exact relCT_sum (Taint.ofRegs [.rdi, .rbx])
      (fun _ _ h => ctx_agree h) (by taint_decide_sum [dblSum, addSum, dblAdxSum, addAdxSum])
  exact (seq_same head (fun _ h => firstHead_ok h ht)
    (seq_same (selectSignedKey_ct base S K t ht) hw tail)).assoc

theorem dec_ctx {base : Addr} {S K t : Nat} {s : State} (h : TimingCtx base S K (t + 5) s) :
    WP isa (.block [.alu .sub .rbx (.imm 5)]) s (TimingCtx base S K t) := by
  refine WP.mono (dec5_ok s h.rbx) fun u ⟨bu, gu, mu, ru, wu⟩ => ?_
  exact ⟨⟨(gu _ (by decide)).trans h.scr.rdi, wu ▸ h.scr.wr, h.scr.nowrap⟩,
    bu, (by intro i hi; rw [mu]; exact h.bs i hi), (by intro i hi; rw [mu]; exact h.bk i hi), (by rw [mu]; exact h.d)⟩

theorem step_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) (S K t : Nat) (ht : t + 5 ≤ 460) :
    RelCT isa (fun s u => TimingCtx base S K (t + 5) s ∧ TimingCtx base S K (t + 5) u)
      (step v.field v.bodies KBITS) (fun _ _ => True) := by
  apply seq_same (p := .block [.alu .sub .rbx (.imm 5)]) _ (fun _ h => dec_ctx h) (round_ct v base S K t ht)
  exact RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rbx]) (fun _ _ h => ctx_agree h) (by taint_decide)

theorem step_ctx (v : Impl.Ed448.X86_64.FieldVariant) {base : Addr} {S K t : Nat} {s : State}
    (h : TimingCtx base S K (t + 5) s) (ht : t + 5 ≤ 460) :
    WP isa (step v.field v.bodies KBITS) s fun u =>
      TimingCtx base S K t u ∧ u.zf = some (decide (t = 0)) := by
  refine WP.seq (WP.mono (dec_ctx h) fun a ha => ?_)
  refine WP.mono (round_ok (FieldVariant.field_ok v) (FieldVariant.bodies_ok v)
    ha.scr (by decide) (by decide) ht ha.rbx ha.bs ha.bk ha.d) fun u ⟨ku, zu, du, _⟩ => ?_
  exact ⟨ha.keep ku du, zu⟩

theorem loop_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) (S K : Nat) :
    RelCT isa (fun s u => TimingCtx base S K 455 s ∧ TimingCtx base S K 455 u)
      (.loop (step v.field v.bodies KBITS) .ne) (fun _ _ => True) := by
  let I (n : Nat) (s u : State) := 1 ≤ n ∧ n ≤ 91 ∧
    TimingCtx base S K (5 * n) s ∧ TimingCtx base S K (5 * n) u
  have hstep : ∀ n, RelCT isa (I n) (step v.field v.bodies KBITS) fun s u =>
      isa.eval .ne s = isa.eval .ne u ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m < n, I m s u) := by
    intro n s u tr1 tr2 s' u' hn ex1 ex2
    obtain ⟨hn0, hn1, hs, hu⟩ := hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have ht : 5 * m + 5 ≤ 460 := by omega
    have hm : 5 * (m + 1) = 5 * m + 5 := by omega
    rw [hm] at hs hu
    have hct := step_ct v base S K (5 * m) ht
    obtain ⟨he, _⟩ := hct s u tr1 tr2 s' u' ⟨hs, hu⟩ ex1 ex2
    obtain ⟨_, a, ea, ha⟩ := step_ctx v hs ht
    obtain ⟨_, b, eb, hb⟩ := step_ctx v hu ht
    obtain ⟨_, rfl⟩ := Exec.det ex1 ea
    obtain ⟨_, rfl⟩ := Exec.det ex2 eb
    have za : isa.eval .ne s' = some (!decide (5 * m = 0)) := by simp only [eval, ha.2, Option.map_some]
    have zb : isa.eval .ne u' = some (!decide (5 * m = 0)) := by simp only [eval, hb.2, Option.map_some]
    refine ⟨he, za.trans zb.symm, fun _ => trivial, fun hz => ?_⟩
    have hp : 0 < m := by rw [za] at hz; simp only [Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at hz; omega
    exact ⟨m, by omega, hp, by omega, ha.1, hb.1⟩
  exact (RelCT.loop I hstep 91).mono (fun _ _ h => ⟨by decide, by decide, h⟩) (fun _ _ h => h)


structure JointTimingCtx (base : Addr) (S K : Nat) (s : State) : Prop where
  scr : Scr s base
  bs : Bits base BITS S s
  bk : Bits base KBITS K s
  d : E s.mem base 11 = Spec.Ed448.d
  z : E s.mem base 10 = 1
  p : Proof.Ed448.pt (E s.mem base) 0 1 2 = Spec.Ed448.identity

def jointHead (v : Impl.Ed448.X86_64.FieldVariant) : Prog isa :=
  .seq (table v.bodies) (.block [.mov32 .rbx (.imm 455)])

theorem jointHead_ok (v : Impl.Ed448.X86_64.FieldVariant) {base : Addr} {S K : Nat} {s : State}
    (h : JointTimingCtx base S K s) : WP isa (jointHead v) s (TimingCtx base S K 455) := by
  refine WP.seq (WP.mono (table_ok (FieldVariant.bodies_ok v) h.scr h.d h.z h.p) fun a ⟨ka, da, _⟩ => ?_)
  refine WP.mono (VG.Proof.X448.X86_64.setRbx_ok a 455 (by decide)) fun u ⟨bu, gu, mu, ru, wu⟩ => ?_
  refine ⟨⟨(gu _ (by decide)).trans (ka.scr h.scr).rdi, wu ▸ (ka.scr h.scr).wr, h.scr.nowrap⟩,
    bu, ?_, ?_, ?_⟩
  · rw [Bits, mu]; exact h.bs.keepW (by decide) (by decide) ka
  · rw [Bits, mu]; exact h.bk.keepW (by decide) (by decide) ka
  · rw [mu]; exact da

theorem joint_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) (S K : Nat) :
    RelCT isa (fun s u => JointTimingCtx base S K s ∧ JointTimingCtx base S K u)
      (joint v.field v.bodies KBITS) (fun _ _ => True) := by
  have head : RelCT isa (fun s u => JointTimingCtx base S K s ∧ JointTimingCtx base S K u)
      (jointHead v) (fun _ _ => True) := by
    cases v <;> apply relCT_sum (Taint.ofRegs [.rdi]) _ (by taint_decide_sum [dblSum, addSum, dblAdxSum, addAdxSum])
    all_goals
      intro s u h
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h.1.scr.rdi.trans h.2.scr.rdi.symm
  have hw (s : State) (h : TimingCtx base S K 455 s) :
      WP isa (first v.field v.bodies KBITS) s (TimingCtx base S K 455) := by
    refine WP.mono (first_ok (FieldVariant.field_ok v) (FieldVariant.bodies_ok v)
      h.scr (by decide) (by decide) h.rbx h.bs h.bk h.d) fun u ⟨ku, du, _⟩ => ?_
    exact h.keep ku du
  exact (seq_same head (fun _ h => jointHead_ok v h)
    (seq_same (first_ct v base S K 455 (by decide)) hw (loop_ct v base S K))).assoc

end VG.Proof.Ed448.X86_64.Window
