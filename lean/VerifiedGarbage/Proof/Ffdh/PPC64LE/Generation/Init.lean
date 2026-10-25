module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Generation.Init
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.InitCommon
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Impl.Ffdh.PPC64LE.Generation.Init
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.InitCommon
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Spec.Ffdh.GenerationContract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RunR

/-! # Native FFDH parameter-generation initialization on PPC64LE: correctness, constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Proof.Ffdh.PPC64LE VG.Impl.Ffdh.PPC64LE.Generation

/-- Whether `init` accepts `bits` and the generator. -/
def initValid (bits g : Nat) : Prop := 512 ≤ bits ∧ bits ≤ 8192 ∧ (g = 2 ∨ g = 5)

instance (bits g : Nat) : Decidable (initValid bits g) := by unfold initValid; infer_instance

theorem high_ok (s : State) :
    WP isa (.block high) s fun t => t.gpr .r12 = s.gpr .r4 >>> 14 ∧ t.mem = s.mem := by
  unfold high
  crunr

theorem zext {g : Nat} (hg : g < 2 ^ 32) :
    (BitVec.ofNat 32 g >>> 0).setWidth 64 = BitVec.ofNat 64 g := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.ushiftRight_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `validate`: with `bits < 2^14`, `r12` is 1 exactly for valid parameters. -/
theorem validate_ok (s : State) {n g : Nat} (hx : s.gpr .r4 = BitVec.ofNat 64 n) (hn : n < 2 ^ 14)
    (hg : (s.gpr .r5).setWidth 32 = BitVec.ofNat 32 g) (hgl : g < 2 ^ 32) :
    WP isa (.block validate) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 (if initValid n g then 1 else 0) ∧ t.mem = s.mem := by
  unfold validate lt
  crunr [hx, hg, List.cons_append, List.nil_append]
  rw [zext hgl, lt_bit (by omega) (by decide), lt_bit (by omega) (by decide),
    lt_bit (by omega) (by decide), lt_bit (by omega) (by decide), lt_bit (by omega) (by decide),
    lt_bit (by omega) (by decide)]
  unfold initValid
  split_ifs <;> first | rfl | (exfalso; omega)

theorem clear_ok {s : State} (h : StateWr s) :
    WP isa (.block clear) s fun t => t.gpr .r3 = 0 ∧ t.mem = initWritten s.mem (s.gpr .r3) 0 0 0 0 := by
  unfold clear initWritten
  crunr [st0 h, st h 8 (by decide), st h 16 (by decide), st h 24 (by decide)]
  rfl

theorem shift_ofNat (n k : Nat) : (BitVec.ofNat 64 n) <<< k = BitVec.ofNat 64 (n * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_mod, Nat.mod_mod]

theorem initialize_ok {s : State} {bits : Nat} (h : StateWr s) (hx : s.gpr .r4 = BitVec.ofNat 64 bits)
    (hhi : bits ≤ 8192) :
    WP isa (.block initializeState) s fun t => t.gpr .r3 = 1 ∧
      t.mem = initWritten s.mem (s.gpr .r3) (BitVec.ofNat 64 (Spec.Ffdh.parameterAttempts bits))
        (BitVec.ofNat 64 ((bits + 7) / 8)) (BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy bits))
        (BitVec.ofNat 64 (512 * ((bits + 7) / 8))) := by
  have hw : (BitVec.ofNat 64 bits + 7#64) >>> 3 = BitVec.ofNat 64 ((bits + 7) / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  have hm : (BitVec.ofNat 64 bits * BitVec.ofNat 64 bits) <<< 6 =
      BitVec.ofNat 64 (Spec.Ffdh.parameterAttempts bits) := by
    rw [← BitVec.ofNat_mul, shift_ofNat]
    rfl
  have hc : BitVec.ofNat 64 ((bits + 7) / 8) <<< 15 + BitVec.ofNat 64 ((bits + 7) / 8) =
      BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy bits) := by
    rw [shift_ofNat, ← BitVec.ofNat_add]
    congr 1
    simp only [Spec.Ffdh.parameterEntropy, Nat.reducePow]
    omega
  have hr : BitVec.ofNat 64 ((bits + 7) / 8) <<< 9 = BitVec.ofNat 64 (512 * ((bits + 7) / 8)) := by
    rw [shift_ofNat]
    congr 1
    simp only [Nat.reducePow]
    omega
  unfold initializeState initWritten
  crunr [hx, hw, hm, hc, hr, st0 h, st h 8 (by decide), st h 16 (by decide), st h 24 (by decide)]
  rfl

def initPre (s : State) : Prop := s.rd = [] ∧ StateWr s

def initPost (s t : State) : Prop :=
  match Spec.Ffdh.parameterInit (s.gpr .r4).toNat ((s.gpr .r5).setWidth 32).toNat with
  | none => ((t.gpr .r3).setWidth 32).toNat = 0 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .r3) 4 = List.replicate 4 0
  | some values => ((t.gpr .r3).setWidth 32).toNat = 1 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .r3) 4 = values.map (BitVec.ofNat 64)

def initPub (s t : State) : Prop :=
  s.sp = t.sp ∧ s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4 ∧
    (s.gpr .r5).setWidth 32 = (t.gpr .r5).setWidth 32

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

theorem parameterInit_none {n g : Nat} (h : ¬initValid n g) : Spec.Ffdh.parameterInit n g = none := by
  simp only [Spec.Ffdh.parameterInit]
  refine ite_eq_right ?_
  simpa only [initValid, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] using h

theorem clear_post {s u : State} {rs : List Reg} (h : StateWr s) (k : Keep rs s u) (hr : .r3 ∉ rs)
    (hn : ¬initValid (s.gpr .r4).toNat ((s.gpr .r5).setWidth 32).toNat) (hm : u.mem = s.mem) :
    WP isa (.block clear) u (initPost s) := by
  have h3 : u.gpr .r3 = s.gpr .r3 := k.gpr hr
  have hu : StateWr u := by rw [StateWr, k.2.2, h3]; exact h
  refine WP.mono (clear_ok hu) fun t ⟨ht, hmt⟩ => ?_
  simp only [initPost, parameterInit_none hn]
  refine ⟨by rw [ht]; rfl, ?_⟩
  rw [hmt, hm, h3, initWritten_words]
  rfl

theorem init_ok {s : State} (h : StateWr s) : WP isa init s (initPost s) := by
  obtain ⟨n, hl, hx⟩ : ∃ n, n < 2 ^ 64 ∧ s.gpr .r4 = BitVec.ofNat 64 n :=
    ⟨_, (s.gpr .r4).isLt, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  have hxn : (s.gpr .r4).toNat = n := by rw [hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]
  obtain ⟨g, hgl, hg⟩ : ∃ g, g < 2 ^ 32 ∧ (s.gpr .r5).setWidth 32 = BitVec.ofNat 32 g :=
    ⟨_, ((s.gpr .r5).setWidth 32).isLt, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  have hgn : ((s.gpr .r5).setWidth 32).toNat = g := by rw [hg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hgl]
  unfold init
  refine WP.seq (WP.mono (WP.keep [.r12] (high_ok s) (by decide +kernel)) fun u ⟨⟨h12, hm⟩, k⟩ => ?_)
  by_cases hb : n < 2 ^ 14
  · refine WP.ite true (by simp only [VG.PPC64LE.eval, State.read, BitVec.setWidth_eq, h12, hx,
        shr_zero hl, decide_eq_true hb]) (fun _ => ?_) (by simp)
    have h4 : u.gpr .r4 = BitVec.ofNat 64 n := (k.gpr (by decide)).trans hx
    have h5 : (u.gpr .r5).setWidth 32 = BitVec.ofNat 32 g := by rw [k.gpr (by decide), hg]
    refine WP.seq (WP.mono (WP.keep [.r6, .r7, .r8, .r9, .r10, .r11, .r12] (validate_ok u h4 hb h5 hgl)
      (by decide +kernel)) fun v ⟨⟨h12', hm'⟩, k'⟩ => ?_)
    have kv := k.trans k'
    by_cases hv : initValid n g
    · rw [ite_eq_left hv] at h12'
      refine WP.ite false (by simp only [VG.PPC64LE.eval, State.read, BitVec.setWidth_eq, h12']; rfl)
        (by simp) (fun _ => ?_)
      have h3 : v.gpr .r3 = s.gpr .r3 := kv.gpr (by decide)
      have hv4 : v.gpr .r4 = BitVec.ofNat 64 n := (kv.gpr (by decide)).trans hx
      have hvw : StateWr v := by rw [StateWr, kv.2.2, h3]; exact h
      refine WP.mono (initialize_ok hvw hv4 hv.2.1) fun t ⟨ht, hmt⟩ => ?_
      have he : Spec.Ffdh.parameterInit (s.gpr .r4).toNat ((s.gpr .r5).setWidth 32).toNat =
          some [Spec.Ffdh.parameterAttempts n, (n + 7) / 8, Spec.Ffdh.parameterEntropy n,
            512 * ((n + 7) / 8)] := by
        rw [hxn, hgn]
        simp only [Spec.Ffdh.parameterInit]
        refine ite_eq_left ?_
        simpa only [initValid, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] using hv
      simp only [initPost, he]
      refine ⟨by rw [ht]; rfl, ?_⟩
      rw [hmt, hm', hm, h3, initWritten_words]
      rfl
    · rw [ite_eq_right hv] at h12'
      refine WP.ite true (by simp only [VG.PPC64LE.eval, State.read, BitVec.setWidth_eq, h12']; rfl)
        (fun _ => ?_) (by simp)
      exact clear_post h kv (by decide) (by rw [hxn, hgn]; exact hv) (hm'.trans hm)
  · refine WP.ite false (by simp only [VG.PPC64LE.eval, State.read, BitVec.setWidth_eq, h12, hx,
        shr_zero hl, decide_eq_false hb]) (by simp) (fun _ => ?_)
    exact clear_post h k (by decide) (by rw [hxn, hgn]; unfold initValid; omega) hm

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨tr, t, he, hp, k⟩ := WP.keep [.r3, .r6, .r7, .r8, .r9, .r10, .r11, .r12] (init_ok h.2)
    (by decide +kernel)
  exact ⟨tr, t, he, abiPreserved_of_keep he k (by decide) (by decide +kernel)
    (by rw [← Code.allInstrs_eq]; decide +kernel), hp⟩

private def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 512 | .r5 => 2 | _ => 0
  lr := 0
  sp := 0x3000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩]

/-- The public inputs: the state's address, `bits`, the generator's low word
and the stack pointer. -/
structure Inputs where
  B : Addr
  n : Nat
  g : Nat
  sp : Addr

def Input (p : Inputs) (s : State) : Prop :=
  s.gpr .r3 = p.B ∧ s.gpr .r4 = BitVec.ofNat 64 p.n ∧ (s.gpr .r5).setWidth 32 = BitVec.ofNat 32 p.g ∧
    s.sp = p.sp

/-- After `high`. -/
def High (p : Inputs) (s : State) : Prop := Input p s ∧ s.gpr .r12 = BitVec.ofNat 64 p.n >>> 14

/-- After `validate`. -/
def Valid (p : Inputs) (s : State) : Prop :=
  Input p s ∧ s.gpr .r12 = BitVec.ofNat 64 (if initValid p.n p.g then 1 else 0)

theorem WP.withSp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.sp = s.sp :=
  let ⟨_, _, he, hq⟩ := h
  ⟨_, _, he, hq, Exec.sp he⟩

theorem high_input {p : Inputs} {s : State} (h : Input p s) : WP isa (.block high) s (High p) :=
  WP.mono (WP.withSp (WP.keep [.r12] (high_ok s) (by decide +kernel))) fun _ ⟨⟨⟨h12, _⟩, k⟩, hsp⟩ =>
    ⟨⟨(k.gpr (by decide)).trans h.1, (k.gpr (by decide)).trans h.2.1,
      by rw [k.gpr (by decide)]; exact h.2.2.1, hsp.trans h.2.2.2⟩, by rw [h12, h.2.1]⟩

theorem validate_input {p : Inputs} {s : State} (h : High p s) (hn : p.n < 2 ^ 14) (hg : p.g < 2 ^ 32) :
    WP isa (.block validate) s (Valid p) :=
  WP.mono (WP.withSp (WP.keep [.r6, .r7, .r8, .r9, .r10, .r11, .r12]
      (validate_ok s h.1.2.1 hn h.1.2.2.1 hg) (by decide +kernel))) fun _ ⟨⟨⟨h12, _⟩, k⟩, hsp⟩ =>
    ⟨⟨(k.gpr (by decide)).trans h.1.1, (k.gpr (by decide)).trans h.1.2.1,
      by rw [k.gpr (by decide)]; exact h.1.2.2.1, hsp.trans h.1.2.2.2⟩, h12⟩

/-- Two runs from the same public inputs agree on `r3`, and on `r4` too. -/
theorem agree3 {p : Inputs} {s₁ s₂ : State} (h₁ : Input p s₁) (h₂ : Input p s₂) :
    taint.Agree (Taint.ofRegs [.r3, .r4]) s₁ s₂ := by
  refine ⟨h₁.2.2.2.trans h₂.2.2.2.symm, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h₁.1.trans h₂.1.symm
  · exact h₁.2.1.trans h₂.2.1.symm

theorem eval_eq {s₁ s₂ : State} (h : s₁.gpr .r12 = s₂.gpr .r12) :
    isa.eval (.zero .d .r12) s₁ = isa.eval (.zero .d .r12) s₂ := by
  simp only [VG.PPC64LE.eval, State.read, BitVec.setWidth_eq, h]

/-- A block that the taint analysis checks, from states with the same public
inputs, whose correctness gives `Ψ`. -/
theorem piece {p : Inputs} {Φ Ψ : Inputs → State → Prop} {c : Prog isa} (hi : ∀ s, Φ p s → Input p s)
    {hc : Taint.Hint taint.T} (ht : (taint.check (Taint.ofRegs [.r3, .r4]) c hc).isSome = true)
    (hw : ∀ s, Φ p s → WP isa c s (Ψ p)) :
    RelCT isa (fun s₁ s₂ => Φ p s₁ ∧ Φ p s₂) c fun s₁ s₂ => Ψ p s₁ ∧ Ψ p s₂ :=
  (RelCT.wp (RelCT.taint _ (fun _ _ h => agree3 (hi _ h.1) (hi _ h.2)) ht)
    (fun _ _ h => ⟨hw _ h.1, hw _ h.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem leaf {p : Inputs} {Φ : Inputs → State → Prop} {P : State → State → Prop} {c : Prog isa}
    (hi : ∀ s, Φ p s → Input p s) (hP : ∀ s₁ s₂, P s₁ s₂ → Φ p s₁ ∧ Φ p s₂)
    {hc : Taint.Hint taint.T} (ht : (taint.check (Taint.ofRegs [.r3, .r4]) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint _ (fun _ _ h => agree3 (hi _ (hP _ _ h).1) (hi _ (hP _ _ h).2)) ht

theorem init_relCT (p : Inputs) (hn : p.n < 2 ^ 64) (hg : p.g < 2 ^ 32) :
    RelCT isa (fun s₁ s₂ => Input p s₁ ∧ Input p s₂) init fun _ _ => True := by
  unfold init
  refine RelCT.seq (piece (Ψ := High) (fun _ h => h) (by taint_decide) (fun _ h => high_input h)) ?_
  refine RelCT.ite (fun _ _ h => eval_eq (h.1.2.trans h.2.2.symm)) ?_
    (leaf (Φ := High) (fun _ h => h.1) (fun _ _ h => h.1) (by taint_decide))
  by_cases hb : p.n < 2 ^ 14
  · refine RelCT.seq ((piece (Φ := High) (Ψ := Valid) (fun _ h => h.1) (by taint_decide)
      (fun _ h => validate_input h hb hg)).mono (fun _ _ h => h.1) fun _ _ h => h) ?_
    exact RelCT.ite (fun _ _ h => eval_eq (h.1.2.trans h.2.2.symm))
      (leaf (Φ := Valid) (fun _ h => h.1) (fun _ _ h => h.1) (by taint_decide))
      (leaf (Φ := Valid) (fun _ h => h.1) (fun _ _ h => h.1) (by taint_decide))
  · refine RelCT.of_false fun s₁ _ ⟨⟨h₁, _⟩, he⟩ => ?_
    simp only [VG.PPC64LE.eval, State.read, BitVec.setWidth_eq, h₁.2, shr_zero hn,
      decide_eq_false hb] at he
    cases he

theorem init_verified : Verified target init (Spec.Ffdh.parameterInitContract abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hp e₁ e₂
    obtain ⟨hsp, h3, h4, h5⟩ := hp
    let p : Inputs := ⟨s₁.gpr .r3, (s₁.gpr .r4).toNat, ((s₁.gpr .r5).setWidth 32).toNat, s₁.sp⟩
    have i₁ : Input p s₁ := ⟨rfl, by simp only [p, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by simp only [p, BitVec.ofNat_toNat, BitVec.setWidth_eq], rfl⟩
    have i₂ : Input p s₂ := ⟨h3.symm, by simp only [p, h4, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by simp only [p, h5, BitVec.ofNat_toNat, BitVec.setWidth_eq], hsp.symm⟩
    exact (init_relCT p (s₁.gpr .r4).isLt ((s₁.gpr .r5).setWidth 32).isLt _ _ _ _ _ _ ⟨i₁, i₂⟩ e₁ e₂).1
  · sig_implies [Spec.Ffdh.parameterInitContract, Spec.Ffdh.parameterInitSig,
      initContract, initPre, initPost, initPub, StateWr, abi, argRegs] [initSat] using initSat

end VG.Proof.Ffdh.PPC64LE.Generation
