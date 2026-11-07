module

public import VerifiedGarbage.Impl.Ffdh.RISCV64.Generation.Init
public import VerifiedGarbage.Proof.Ffdh.RISCV64.KeyGeneration.Init
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Impl.Ffdh.RISCV64.Generation.Init
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.KeyGeneration.Init
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Spec.Ffdh.GenerationContract
meta import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.EntropyRequest
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64

/-! # Native FFDH parameter-generation initialization on RISC-V: correctness, constant time

`zext_ok`: the generator's low word, zero-extended, in `a2`; `validate_ok`:
`t0` is zero exactly for valid parameters (`initValid`); `initialize_ok` and
`clear_ok`: the four public words (`initWritten`) and the result. The code
branches only on `bits` and the generator's low word, which are public, but
the generator's register is public only in its low word, so constant time is
relational (`init_relCT`): `zext` is checked by the taint analysis with `a2`
secret, and the rest with `a2`, now equal in both runs, public.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Generation

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Bignum VG.Impl.Ffdh.RISCV64.Generation
open VG.Proof.Ffdh.RISCV64.KeyGeneration (initWritten initWritten_words StateWr st al st0 al0)
open VG.Proof.Bignum.RISCV64 (add_ofNat_zero fin64_exec_li_lit fin64_exec_li_zero)

/-- Whether `init` accepts `bits` and the generator. -/
def initValid (bits g : Nat) : Prop := 512 ≤ bits ∧ bits ≤ 8192 ∧ (g = 2 ∨ g = 5)

instance (bits g : Nat) : Decidable (initValid bits g) := by unfold initValid; infer_instance

theorem zext32 (x : BitVec 64) : (x <<< 32) >>> 32 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  omega

theorem zext_ok (s : State) {g : Nat} (hg : (s.gpr .a2).setWidth 32 = BitVec.ofNat 32 g)
    (hgl : g < 2 ^ 32) :
    WP isa (.block zext) s fun t => (t.gpr .a2 = BitVec.ofNat 64 g ∧ t.mem = s.mem) ∧ Keep [.a2] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold zext
  brun []
  rw [zext32, hg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hgl]

theorem ofNat_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a < BitVec.ofNat 64 b ↔ a < b := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- `g == c` as `(g < c + 1) − (g < c)`. -/
theorem flag_eq {g c c' : Nat} (h : c' = c + 1) :
    ((if g < c' then 1 else 0 : BitVec 64) - if g < c then 1 else 0) = if g = c then 1 else 0 := by
  subst h
  by_cases h₁ : g < c
  · rw [ite_eq_left h₁, ite_eq_left (by omega), ite_eq_right (by omega)]; rfl
  · by_cases h₂ : g = c
    · rw [ite_eq_right h₁, ite_eq_left (by omega), ite_eq_left h₂]; rfl
    · rw [ite_eq_right h₁, ite_eq_right (by omega), ite_eq_right h₂]; rfl

theorem flags_zero (a b c d : Prop) [Decidable a] [Decidable b] [Decidable c] [Decidable d] :
    (((if a then 1 else 0 : BitVec 64) ||| if b then 1 else 0) |||
      (((if c then 1 else 0 : BitVec 64) ||| if d then 1 else 0) ^^^ 1#64) = 0) ↔ ¬a ∧ ¬b ∧ (c ∨ d) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases hd : d <;>
    simp only [ha, hb, hc, hd, ↓reduceIte] <;> decide

theorem lui2 : sext32 ((2 : BitVec 20) ++ (0 : BitVec 12)) = BitVec.ofNat 64 8192 := by decide

/-- `validate`: `t0` is zero exactly for valid parameters. -/
theorem validate_ok (s : State) {n g : Nat} (hx : s.gpr .a1 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64)
    (hg : s.gpr .a2 = BitVec.ofNat 64 g) (hgl : g < 2 ^ 32) :
    WP isa (.block validate) s fun t =>
      ((t.gpr .t0 = 0 ↔ initValid n g) ∧ t.mem = s.mem) ∧ Keep [.t0, .t1, .t2, .t3, .t4] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold validate lt
  brun [hx, hg, exec_lui, lui2, fin64_exec_li_lit (show 512 < 2048 by decide)]
  simp only [ofNat_lt hn (show 512 < 2 ^ 64 by decide), ofNat_lt (show 8192 < 2 ^ 64 by decide) hn,
    ofNat_lt (show g < 2 ^ 64 by omega) (show 2 < 2 ^ 64 by decide),
    ofNat_lt (show g < 2 ^ 64 by omega) (show 3 < 2 ^ 64 by decide),
    ofNat_lt (show g < 2 ^ 64 by omega) (show 5 < 2 ^ 64 by decide),
    ofNat_lt (show g < 2 ^ 64 by omega) (show 6 < 2 ^ 64 by decide),
    flag_eq (c := 2) (c' := 3) rfl, flag_eq (c := 5) (c' := 6) rfl, flags_zero]
  unfold initValid
  omega

theorem clear_ok {s : State} (h : StateWr s) :
    WP isa (.block clear) s fun t => (t.gpr .a0 = 0 ∧ t.mem = initWritten s.mem (s.gpr .a0) 0 0 0 0) ∧
      Keep [.a0, .t2] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold clear initWritten
  brun [st0 h, al0 h, st h 0 (by decide), st h 8 (by decide), st h 16 (by decide), st h 24 (by decide),
    al h 0 (by decide) (by decide), al h 8 (by decide) (by decide), al h 16 (by decide) (by decide),
    al h 24 (by decide) (by decide), fin64_exec_li_zero, add_ofNat_zero]
  all_goals rfl

theorem shift_ofNat (n k : Nat) : (BitVec.ofNat 64 n) <<< k = BitVec.ofNat 64 (n * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_mod, Nat.mod_mod]

theorem initialize_ok {s : State} {bits : Nat} (h : StateWr s) (hx : s.gpr .a1 = BitVec.ofNat 64 bits)
    (hhi : bits ≤ 8192) :
    WP isa (.block initializeState) s fun t => (t.gpr .a0 = 1 ∧
      t.mem = initWritten s.mem (s.gpr .a0) (BitVec.ofNat 64 (Spec.Ffdh.parameterAttempts bits))
        (BitVec.ofNat 64 ((bits + 7) / 8)) (BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy bits))
        (BitVec.ofNat 64 (512 * ((bits + 7) / 8)))) ∧ Keep [.a0, .t0, .t1, .t2, .t3] s t := by
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
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold initializeState initWritten
  brun [hx, hw, hm, hc, hr, st0 h, al0 h, st h 0 (by decide), st h 8 (by decide), st h 16 (by decide), st h 24 (by decide),
    al h 0 (by decide) (by decide), al h 8 (by decide) (by decide), al h 16 (by decide) (by decide),
    al h 24 (by decide) (by decide), fin64_exec_li_lit (show 1 < 2048 by decide), add_ofNat_zero]
  rfl

def initPre (s : State) : Prop := StateWr s

def initPost (s t : State) : Prop :=
  match Spec.Ffdh.parameterInit (s.gpr .a1).toNat ((s.gpr .a2).setWidth 32).toNat with
  | none => ((t.gpr .a0).setWidth 32).toNat = 0 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .a0) 4 = List.replicate 4 0
  | some values => ((t.gpr .a0).setWidth 32).toNat = 1 ∧ ∃ first,
      Spec.Rsa.wordsAt t.mem (s.gpr .a0) 4 = (values ++ [first]).map (BitVec.ofNat 64) ∧
      Spec.Entropy.RequestValid (Spec.Ffdh.parameterEntropy (s.gpr .a1).toNat) 0 first

def initPub (s t : State) : Prop :=
  s.sp = t.sp ∧ s.gpr .a0 = t.gpr .a0 ∧ s.gpr .a1 = t.gpr .a1 ∧
    (s.gpr .a2).setWidth 32 = (t.gpr .a2).setWidth 32

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

theorem parameterInit_eq (n g : Nat) : Spec.Ffdh.parameterInit n g = if initValid n g then
    some [Spec.Ffdh.parameterAttempts n, (n + 7) / 8, Spec.Ffdh.parameterEntropy n]
    else none := by
  simp only [Spec.Ffdh.parameterInit, initValid, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq, and_assoc]

theorem init_ok {s : State} (h : StateWr s) : WP isa init s (initPost s) := by
  obtain ⟨n, hl, hx⟩ : ∃ n, n < 2 ^ 64 ∧ s.gpr .a1 = BitVec.ofNat 64 n :=
    ⟨_, (s.gpr .a1).isLt, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  have hxn : (s.gpr .a1).toNat = n := by rw [hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]
  obtain ⟨g, hgl, hg⟩ : ∃ g, g < 2 ^ 32 ∧ (s.gpr .a2).setWidth 32 = BitVec.ofNat 32 g :=
    ⟨_, ((s.gpr .a2).setWidth 32).isLt, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  have hgn : ((s.gpr .a2).setWidth 32).toNat = g := by rw [hg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hgl]
  unfold init rest
  refine WP.seq (WP.mono (zext_ok s hg hgl) fun u ⟨⟨h2, hm₀⟩, k₀⟩ => ?_)
  have hu4 : u.gpr .a1 = BitVec.ofNat 64 n := (k₀.gpr (by decide)).trans hx
  refine WP.seq (WP.mono (validate_ok u hu4 hl h2 hgl) fun v ⟨⟨h0, hm⟩, k₁⟩ => ?_)
  have k := k₀.trans k₁
  have h3 : v.gpr .a0 = s.gpr .a0 := k.gpr (by decide)
  have hv4 : v.gpr .a1 = BitVec.ofNat 64 n := (k.gpr (by decide)).trans hx
  have hvw : StateWr v := by rw [StateWr, k.2.2, h3]; exact h
  have hmv : v.mem = s.mem := hm.trans hm₀
  refine WP.ite (v.gpr .t0 == 0) (Steps.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have hv : initValid n g := h0.1 (by simpa using hb)
    refine WP.mono (initialize_ok hvw hv4 hv.2.1) fun t ⟨⟨ht, hmt⟩, _⟩ => ?_
    simp only [initPost, hxn, hgn, parameterInit_eq, ite_eq_left hv]
    refine ⟨by rw [ht]; rfl, _, ?_, Proof.Ffdh.first_valid hv.1⟩
    rw [hmt, hmv, h3, initWritten_words]
    rfl
  · have hv : ¬initValid n g := fun hv => by simp [h0.2 hv] at hb
    refine WP.mono (clear_ok hvw) fun t ⟨⟨ht, hmt⟩, _⟩ => ?_
    simp only [initPost, hxn, hgn, parameterInit_eq, ite_eq_right hv]
    refine ⟨by rw [ht]; rfl, ?_⟩
    rw [hmt, hmv, h3, initWritten_words]
    rfl

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨tr, t, he, hp, k⟩ := WP.keep [.a0, .a2, .t0, .t1, .t2, .t3, .t4] (init_ok h) (by rfl)
  exact ⟨tr, t, he, abiPreserved_of_keep he k (by decide) (by decide), hp⟩

private def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 512 | .a2 => 2 | _ => 0
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
  s.gpr .a0 = p.B ∧ s.gpr .a1 = BitVec.ofNat 64 p.n ∧ (s.gpr .a2).setWidth 32 = BitVec.ofNat 32 p.g ∧
    s.sp = p.sp

/-- After `zext`: the generator zero-extended, the same in both runs. -/
def Zext (p : Inputs) (s : State) : Prop :=
  s.gpr .a0 = p.B ∧ s.gpr .a1 = BitVec.ofNat 64 p.n ∧ s.gpr .a2 = BitVec.ofNat 64 p.g ∧ s.sp = p.sp

theorem zext_input {p : Inputs} {s : State} (h : Input p s) (hg : p.g < 2 ^ 32) :
    WP isa (.block zext) s (Zext p) := by
  obtain ⟨_, _, he, ⟨⟨h2, _⟩, k⟩⟩ := zext_ok s h.2.2.1 hg
  exact ⟨_, _, he, (k.gpr (by decide)).trans h.1, (k.gpr (by decide)).trans h.2.1, h2,
    (Exec.sp he).trans h.2.2.2⟩

theorem init_relCT (p : Inputs) (hg : p.g < 2 ^ 32) :
    RelCT isa (fun s₁ s₂ => Input p s₁ ∧ Input p s₂) init fun _ _ => True := by
  unfold init
  refine RelCT.seq ((RelCT.wp (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1]) ?_ (by taint_decide))
    (fun _ _ h => ⟨zext_input h.1 hg, zext_input h.2 hg⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_
  · intro s₁ s₂ ⟨h₁, h₂⟩
    refine ⟨h₁.2.2.2.trans h₂.2.2.2.symm, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁.1.trans h₂.1.symm
    · exact h₁.2.1.trans h₂.2.1.symm
  · refine RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) ?_ (by taint_decide)
    intro s₁ s₂ ⟨h₁, h₂⟩
    refine ⟨h₁.2.2.2.trans h₂.2.2.2.symm, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h₁.1.trans h₂.1.symm
    · exact h₁.2.1.trans h₂.2.1.symm
    · exact h₁.2.2.1.trans h₂.2.2.1.symm

/-- `vg_ffdh_parameter_generation_init`. -/
theorem init_verified : Verified RISCV64.target init (Spec.Ffdh.parameterInitContract RISCV64.abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hp e₁ e₂
    obtain ⟨hsp, h3, h4, h5⟩ := hp
    let p : Inputs := ⟨s₁.gpr .a0, (s₁.gpr .a1).toNat, ((s₁.gpr .a2).setWidth 32).toNat, s₁.sp⟩
    have i₁ : Input p s₁ := ⟨rfl, by simp only [p, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by simp only [p, BitVec.ofNat_toNat, BitVec.setWidth_eq], rfl⟩
    have i₂ : Input p s₂ := ⟨h3.symm, by simp only [p, h4, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by simp only [p, h5, BitVec.ofNat_toNat, BitVec.setWidth_eq], hsp.symm⟩
    exact (init_relCT p ((s₁.gpr .a2).setWidth 32).isLt _ _ _ _ _ _ ⟨i₁, i₂⟩ e₁ e₂).1
  · sig_implies [Spec.Ffdh.parameterInitContract, Spec.Ffdh.parameterInitSig,
      initContract, initPre, initPost, initPub, StateWr, RISCV64.abi, RISCV64.argRegs] [initSat] using initSat

end VG.Proof.Ffdh.RISCV64.Generation
