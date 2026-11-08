module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTTests
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Main
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Trial.Loop
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Trial.Loop
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTTests
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Main

/-!
# An FFDH parameter candidate on PPC64LE: `main` in constant time

The public data are the arguments and tape, and the table's address
(`taintSym`: the contract makes it public). p's congruence branches on the
generator, pinned once loaded; the shape checks branch on `hBad`, which the
candidate decides (`MB`), as do whether q's and p's whole checks run;
trial division (`trialSieve_ct`, `trialSieveN_ct`) loops while the
entry tested, a function of the candidate and of how many are left, does
not divide it; the tests are `tests_ct`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)

/-- The candidate from the tape. -/
def candOf (q : PP) : Nat := Spec.Ffdh.candidateOf q.bits (Spec.Rsa.os2ip (q.r.take q.L))

/-- Code the taint analysis with the table's address public proves constant
time, from states a predicate relates. -/
theorem two_taint_sym {α : Type} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    (hsym : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ →
      s₁.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = s₂.syms VG.Impl.RsaKeyGen.TrialTable32.symbol)
    {hc : VG.Taint.Hint T}
    (h : (VG.Taint.check (taintSym [VG.Impl.RsaKeyGen.TrialTable32.symbol]) (ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taintSym [VG.Impl.RsaKeyGen.TrialTable32.symbol]) (ofRegs rs) (fun _ _ ⟨a, h₁, h₂, hsp⟩ =>
    ⟨⟨hsp, fun r hr => hpin a _ _ h₁ h₂ r (RegSet.mem_ofList.mp hr)⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsym a _ _ h₁ h₂⟩) h

/-- Before `main`: the arguments and tape, and the table's address. -/
def MnI (a : PP × Addr) (s : State) : Prop :=
  ∃ sv toc, St (a.1.with sv toc) s ∧ TabIn a.1.B a.1.Z a.2 s ∧ word s.mem a.1.B 152 = BitVec.ofNat 64 a.1.L ∧
    a.1.L ≤ a.1.r.length

/-- With p in array 0. -/
def MnA (a : PP × Addr) (t : State) : Prop :=
  (∃ sv toc, St (a.1.with sv toc) t ∧ TabIn a.1.B a.1.Z a.2 t ∧ Ph (a.1.with sv toc) a.1.bits
    (Spec.Ffdh.primeChecks a.1.bits) t ∧ word t.mem a.1.B 152 = BitVec.ofNat 64 a.1.L ∧
    wv t.mem a.1.B (slot (wOf a.1.bits) 0) (wOf a.1.bits) = candOf a.1) ∧ a.1.L ≤ a.1.r.length

/-- In p's working space, `hBad` zero iff `B q`. -/
def MnB (x : PP → Nat) (B : PP → Prop) (a : PP × Addr) (t : State) : Prop :=
  (∃ sv toc, MB (a.1.with sv toc) a.2 (x a.1) (B a.1) t) ∧ a.1.L ≤ a.1.r.length

theorem pins_MnB {x : PP → Nat} {B : PP → Prop} {Φ : PP × Addr → State → Prop}
    (h : ∀ a s, Φ a s → MnB x B a s) : Pins Φ [.r10, .r11, .r29, .r31] := by
  intro a s₁ s₂ h₁ h₂ r hr
  obtain ⟨⟨_, _, M₁⟩, _⟩ := h a s₁ h₁
  obtain ⟨⟨_, _, M₂⟩, _⟩ := h a s₂ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [M₁.ph.r10, M₂.ph.r10]; rfl
  · rw [M₁.ph.r11, M₂.ph.r11]; rfl
  · rw [M₁.ph.r29, M₂.ph.r29]; rfl
  · rw [M₁.st.r31, M₂.st.r31]; rfl

theorem mainA_ct : RelCT isa (Two MnI) (.seq (phase false) shapeP) (Two MnA) :=
  two_post (two_map Prod.fst (fun _ _ ⟨sv, toc, h, _⟩ => ⟨sv, toc, h⟩) (RelCT.seq (phasePA_ct false) shapeP_ct))
    fun _ _ ⟨sv, toc, h, ht, hU, hL⟩ => WP.mono_syms (mainA_ok h hU hL) fun _ ⟨a, b, c, d, hr, f, rd⟩ sy =>
      ⟨⟨sv, toc, a, ht.step sy f hr rd, b, c, d⟩, hL⟩

/-- After the congruence's first block. -/
def RH (a : PP × Addr) (t : State) : Prop :=
  (t.gpr .r3 = BitVec.ofNat 64 a.1.g - BitVec.ofNat 64 2 ∧ (a.1.g = 2 ∨ a.1.g = 5)) ∧
    t.gpr .r10 = off a.1.B (slot (wOf a.1.bits) 0) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * wOf a.1.bits) ∧
    t.gpr .r31 = a.1.B

theorem pins_RH {Φ : PP × Addr → State → Prop} (h : ∀ a s, Φ a s → RH a s) : Pins Φ [.r10, .r11, .r31] := by
  intro a s₁ s₂ h₁ h₂ r hr
  obtain ⟨_, a10, a11, a31⟩ := h a s₁ h₁
  obtain ⟨_, b10, b11, b31⟩ := h a s₂ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a31, b31]

theorem pins_MnA : Pins MnA [.r31] := by
  rintro a s₁ s₂ ⟨⟨_, _, h₁, _⟩, _⟩ ⟨⟨_, _, h₂, _⟩, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁.r31, h₂.r31]; rfl

theorem residue_ct :
    RelCT isa (Two MnA) residue (Two (MnB candOf fun q => goodRes q.g (candOf q))) := by
  refine two_post ?_ fun _ _ ⟨⟨sv, toc, h, ht, hp, hU, hn⟩, hL⟩ =>
    WP.mono (residue_mb h hp ht hU hn) fun _ M => ⟨⟨sv, toc, M⟩, hL⟩
  unfold residue
  refine RelCT.seq (two_post (two_taint _ pins_MnA (by taint_decide)) (Ψ := RH)
    fun a s ⟨⟨sv, toc, h, _, hp, _⟩, _⟩ => ?_) (two_ite' (fun a => decide (a.1.g = 2)) (fun a s h => ?_)
      (two_taint _ (pins_RH fun _ _ h => h.1) (by taint_decide))
      (two_taint _ (pins_RH fun _ _ h => h.1) (by taint_decide)))
  · refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 a.1.g - BitVec.ofNat 64 2) ?_
      (by decide)) fun t ⟨t3, k⟩ => ⟨⟨t3, h.dims.g⟩, (k.gpr _ (by decide)).trans hp.r10,
        (k.gpr _ (by decide)).trans hp.r11, (k.gpr _ (by decide)).trans h.r31⟩
    simp only [ldh, hGen]
    prun [h.r31, h.ld (d := 128) (by decide), h.args.gen', BitVec.add_zero]
    rfl
  · obtain ⟨⟨h3, hg⟩, _⟩ := h
    rw [eval_zero, h3]
    rcases hg with hg | hg <;> rw [hg] <;> decide

theorem badLoad_ct {x : PP → Nat} {B : PP → Prop} [∀ q, Decidable (B q)] :
    RelCT isa (Two (MnB x B)) (.block [ldh .r5 hBad])
      (Two fun a t => MnB x B a t ∧ isa.eval (.zero .d .r5) t = some (decide (B a.1))) :=
  two_post (two_taint _ (pins_MnB fun _ _ h => h) (by taint_decide)) fun _ _ ⟨⟨sv, toc, M⟩, hL⟩ =>
    WP.mono M.badLoad fun _ ⟨M', t5⟩ => ⟨⟨⟨sv, toc, M'⟩, hL⟩,
      (by rw [eval_zero, t5]; exact congrArg some (beq_zero_of_iff M.bad))⟩

theorem finMnB_ct {x : PP → Nat} {B : PP → Prop} {Φ : PP × Addr → State → Prop}
    (h : ∀ a s, Φ a s → MnB x B a s) : RelCT isa (Two Φ) (.block (finish 2)) fun _ _ => True :=
  two_map Prod.fst (fun a s hs => let ⟨⟨_, _, M⟩, _⟩ := h a s hs; M.st.fs) (finish_ct (.inr (.inr rfl)))

theorem halve_ct {x : PP → Nat} {B : PP → Prop} :
    RelCT isa (Two (MnB x B)) halveQ (Two (MnB (fun q => x q / 2) fun q => B q ∧ x q / 2 % 2 = 1)) :=
  two_post (two_taint _ (pins_MnB fun _ _ h => h) (by taint_decide)) fun _ _ ⟨⟨sv, toc, M⟩, hL⟩ =>
    WP.mono M.halve fun _ M' => ⟨⟨sv, toc, M'⟩, hL⟩

/-! ## Trial division

By the first `N q` entries: all of `trialN` (`trialSieve`), or the first
few (`trialSieveN`). -/

/-- With the count of entries in `hTrialN`. -/
def MnC (x : PP → Nat) (B : PP → Prop) (N : PP → Nat) (a : PP × Addr) (u : State) : Prop :=
  MnB x B a u ∧ u.mem.readW (a.1.B + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (N a.1)

/-- With the table's address and the count in `r23` and `r24`. -/
def MnT (x : PP → Nat) (B : PP → Prop) (N : PP → Nat) (a : PP × Addr) (v : State) : Prop :=
  ∃ u, MnC x B N a u ∧ (v.gpr .r23 = a.2 ∧ v.gpr .r24 = BitVec.ofNat 64 (N a.1) ∧ v.mem = u.mem) ∧
    (∀ r, r ∉ [Reg.r23, Reg.r24] → v.gpr r = u.gpr r) ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ v.sp = u.sp ∧
    v.syms = u.syms

/-- In the loop, `d.2` entries left. -/
def MnL (x : PP → Nat) (B : PP → Prop) (N : PP → Nat) (d : (PP × Addr) × Nat) (w : State) : Prop :=
  ∃ v, MnT x B N d.1 v ∧ VG.Proof.RsaKeyGen.PPC64LE.Trial.TInv v d.1.2 (x d.1.1) (N d.1.1) d.2 w

/-- After the loop. -/
def MnE (x : PP → Nat) (B : PP → Prop) (N : PP → Nat) (d : (PP × Addr) × Nat) (w : State) : Prop :=
  ∃ v, MnT x B N d.1 v ∧ Keep VG.Proof.RsaKeyGen.PPC64LE.Trial.entryRegs v w

theorem MnT.base {x : PP → Nat} {B : PP → Prop} {N : PP → Nat} {a : PP × Addr} {v : State} (h : MnT x B N a v) :
    v.gpr .r10 = off a.1.B (slot (wOf a.1.bits) 0) ∧ v.gpr .r11 = BitVec.ofNat 64 (2 * wOf a.1.bits) ∧
      v.gpr .r31 = a.1.B := by
  obtain ⟨u, ⟨⟨⟨_, _, M⟩, _⟩, _⟩, -, vg, -⟩ := h
  exact ⟨(vg _ (by decide)).trans M.ph.r10, (vg _ (by decide)).trans M.ph.r11, (vg _ (by decide)).trans M.st.r31⟩

theorem pins_MnL {x : PP → Nat} {B : PP → Prop} {N : PP → Nat} : Pins (MnL x B N) [.r10, .r11, .r23] := by
  rintro d s₁ s₂ ⟨v₁, hv₁, k₁, hm₁, hk₁, ⟨a23, -⟩, kv₁⟩ ⟨v₂, hv₂, k₂, hm₂, hk₂, ⟨b23, -⟩, kv₂⟩ r hr
  obtain ⟨a10, a11, -⟩ := hv₁.base
  obtain ⟨b10, b11, -⟩ := hv₂.base
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [kv₁.gpr _ (by decide), kv₂.gpr _ (by decide), a10, b10]
  · rw [kv₁.gpr _ (by decide), kv₂.gpr _ (by decide), a11, b11]
  · rw [a23, b23, show k₁ = k₂ by omega]

theorem pins_MnE {x : PP → Nat} {B : PP → Prop} {N : PP → Nat} : Pins (MnE x B N) [.r31] := by
  rintro d s₁ s₂ ⟨v₁, hv₁, kv₁⟩ ⟨v₂, hv₂, kv₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [kv₁.gpr _ (by decide), kv₂.gpr _ (by decide), hv₁.base.2.2, hv₂.base.2.2]

theorem MnT.init {x : PP → Nat} {B : PP → Prop} {N : PP → Nat} {a : PP × Addr} {v : State}
    (hN : ∀ q, 1 ≤ N q ∧ N q ≤ 1024) (h : MnT x B N a v) : MnL x B N (a, N a.1) v := by
  obtain ⟨u, -, ⟨v23, v24, -⟩, -⟩ := id h
  have hN1 := (hN a.1).1
  refine ⟨v, h, 0, ?_, ?_, ?_⟩
  · dsimp only; omega
  · dsimp only; omega
  exact ⟨⟨by rw [v23, Nat.mul_zero, BitVec.add_zero], by rw [v24, Nat.sub_zero], rfl, rfl⟩, Keep.refl _ _⟩

/-- The go-on condition of the loop, `d.2` entries left. -/
def trialGo (x : PP → Nat) (N : PP → Nat) (d : (PP × Addr) × Nat) : Bool :=
  decide (x d.1.1 % VG.Impl.RsaKeyGen.tabEntry (N d.1.1 - d.2) ≠ 0 ∧ N d.1.1 - d.2 + 1 ≠ N d.1.1)

theorem MnL.step {x : PP → Nat} {B : PP → Prop} {N : PP → Nat} (hN : ∀ q, 1 ≤ N q ∧ N q ≤ 1024)
    {d : (PP × Addr) × Nat} {w : State} (h : MnL x B N d w) :
    WP isa VG.Impl.RsaKeyGen.PPC64LE.Trial.entry w fun t =>
      isa.eval (.nonzero .d .r24) t = some (trialGo x N d) ∧ (trialGo x N d = false → MnE x B N d t) ∧
        (trialGo x N d = true → d.2 - 1 < d.2 ∧ MnL x B N (d.1, d.2 - 1) t) := by
  obtain ⟨v, hv, hI⟩ := h
  obtain ⟨u, ⟨⟨⟨sv, toc, M⟩, _⟩, _⟩, ⟨_, _, vm⟩, vg, vrd, vwr, -⟩ := id hv
  obtain ⟨vs, v10, v11, vc, w1, w2, hZ, _, n2, htab⟩ := M.loopArgs vm vg vrd vwr (hN d.1.1)
  refine WP.mono (VG.Proof.RsaKeyGen.PPC64LE.Trial.step_ok vs v10 v11 vc w1 w2 hZ n2 htab hI)
    fun t ⟨e, f, g⟩ => ⟨e, fun hg => ⟨v, hv, (f (by rw [e, ← hg]; rfl)).2⟩, fun hg => ?_⟩
  obtain ⟨hm, hI'⟩ := g (by rw [e, ← hg]; rfl)
  exact ⟨by omega, v, hv, hI'⟩

theorem trialLoop_ct {x : PP → Nat} {B : PP → Prop} {N : PP → Nat} (hN : ∀ q, 1 ≤ N q ∧ N q ≤ 1024) :
    RelCT isa (Two (MnT x B N)) VG.Impl.RsaKeyGen.PPC64LE.Trial.loop (Two (MnE x B N)) :=
  two_map (fun a => (a, N a.1)) (fun _ _ h => h.init hN)
    (two_loopD (Φ := MnL x B N) (Ψ := MnE x B N) Prod.snd (fun d => (d.1, d.2 - 1)) (trialGo x N)
      (two_taint _ pins_MnL (by taint_decide)) fun _ _ h => h.step hN)

/-- The table's address, the count and the loop, from the count in
`hTrialN`. -/
theorem trialRest_ct {x : PP → Nat} {B : PP → Prop} {N : PP → Nat} (hN : ∀ q, 1 ≤ N q ∧ N q ≤ 1024) :
    RelCT isa (Two (MnC x B N))
      (.seq (.seq (.block [.adrSym .r23 VG.Impl.RsaKeyGen.TrialTable32.symbol, ldh .r24 hTrialN]) VG.Impl.RsaKeyGen.PPC64LE.Trial.loop)
        (.block [ldh .r5 hBad, .logic .or .r5 .r5 .r22, sth .r5 hBad])) fun _ _ => True := by
  refine RelCT.seq (RelCT.seq (two_post (two_taint_sym _ (pins_MnB fun _ _ h => h.1)
      (fun _ _ _ ⟨⟨⟨_, _, M₁⟩, _⟩, _⟩ ⟨⟨⟨_, _, M₂⟩, _⟩, _⟩ => M₁.tab.sym.trans M₂.tab.sym.symm) (by taint_decide))
    (Ψ := MnT x B N) fun _ u hu => ?_) (trialLoop_ct hN)) (two_taint _ pins_MnE (by taint_decide))
  obtain ⟨⟨⟨sv, toc, M⟩, hL⟩, h208⟩ := hu
  exact WP.mono (M.trialA h208) fun v hv => ⟨u, ⟨⟨⟨sv, toc, M⟩, hL⟩, h208⟩, hv⟩

/-- Trial division leaks the same from the same candidate and table. -/
theorem trialSieve_ct {x : PP → Nat} {B : PP → Prop} :
    RelCT isa (Two (MnB x B)) trialSieve
      (Two (MnB x fun q => B q ∧ VG.Proof.RsaKeyGen.trialPrefix (x q) (trialN q.bits) = false)) := by
  refine two_post ?_ fun _ _ ⟨⟨sv, toc, M⟩, hL⟩ => WP.mono (trialSieve_ok M) fun _ M' => ⟨⟨sv, toc, M'⟩, hL⟩
  unfold trialSieve VG.Impl.RsaKeyGen.PPC64LE.Trial.trial
  exact RelCT.seq (two_post (two_taint _ (pins_MnB fun _ _ h => h) (by taint_decide))
    (Ψ := MnC x B fun q => trialN q.bits)
    fun _ _ ⟨⟨sv, toc, M⟩, hL⟩ => WP.mono M.count fun _ ⟨M', h208⟩ => ⟨⟨⟨sv, toc, M'⟩, hL⟩, h208⟩)
    (trialRest_ct fun _ => trialN_range)

/-- So does trial division by the first entries. -/
theorem trialSieveN_ct {x : PP → Nat} {B : PP → Prop} :
    RelCT isa (Two (MnB x B)) (trialSieveN firstEntries)
      (Two (MnB x fun q => B q ∧ VG.Proof.RsaKeyGen.trialPrefix (x q) firstEntries = false)) := by
  refine two_post ?_ fun _ _ ⟨⟨sv, toc, M⟩, hL⟩ =>
    WP.mono (trialSieveN_ok M (by decide) (by decide)) fun _ M' => ⟨⟨sv, toc, M'⟩, hL⟩
  unfold trialSieveN VG.Impl.RsaKeyGen.PPC64LE.Trial.trial
  exact RelCT.seq (two_post (two_taint _ (pins_MnB fun _ _ h => h) (by unfold firstEntries; taint_decide))
    (Ψ := MnC x B fun _ => firstEntries)
    fun _ _ ⟨⟨sv, toc, M⟩, hL⟩ => WP.mono (M.countN firstEntries (by decide)) fun _ ⟨M', h208⟩ =>
      ⟨⟨⟨sv, toc, M'⟩, hL⟩, h208⟩)
    (trialRest_ct fun _ => ⟨by decide, by decide⟩)

/-- p into array 0 again leaks the same. -/
theorem reshape_ct {x : PP → Nat} {B : PP → Prop} :
    RelCT isa (Two (MnB x B)) shapeP (Two (MnB candOf B)) :=
  two_post (two_map (fun a => a.1) (fun _ _ ⟨⟨sv, toc, M⟩, _⟩ => ⟨sv, toc, _, M.st, M.ph⟩) shapeP_ct)
    fun _ _ ⟨⟨sv, toc, M⟩, hL⟩ => WP.mono (M.reshape hL) fun _ M' => ⟨⟨sv, toc, M'⟩, hL⟩

/-! ## `main` -/

/-- The congruence and p's trial division by the first entries. -/
def pOk (q : PP) : Prop :=
  goodRes q.g (candOf q) ∧ VG.Proof.RsaKeyGen.trialPrefix (candOf q) firstEntries = false

instance (q : PP) : Decidable (pOk q) := by unfold pOk; infer_instance

/-- Then q's parity and trial division. -/
def qOk (q : PP) : Prop :=
  (pOk q ∧ candOf q / 2 % 2 = 1) ∧ VG.Proof.RsaKeyGen.trialPrefix (candOf q / 2) (trialN q.bits) = false

instance (q : PP) : Decidable (qOk q) := by unfold qOk; infer_instance

/-- The shape checks' conjunction, after p's whole trial division. -/
def allOk (q : PP) : Prop :=
  qOk q ∧ VG.Proof.RsaKeyGen.trialPrefix (candOf q) (trialN q.bits) = false

instance (q : PP) : Decidable (allOk q) := by unfold allOk; infer_instance

theorem ts_of {a : PP × Addr} {s : State} (h : MnB candOf allOk a s) (ha : allOk a.1) :
    TS ⟨a.1, candOf a.1, a.1.L⟩ s := by
  obtain ⟨⟨sv, toc, M⟩, hL⟩ := h
  have hb1 : 512 ≤ a.1.bits := M.st.dims.b1
  obtain ⟨ho, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := a.1.bits) (by omega)
    (Spec.Rsa.os2ip (a.1.r.take a.1.L))
  have hq : (candOf a.1 - 1) / 2 = candOf a.1 / 2 := by unfold candOf; omega
  exact ⟨⟨sv, toc, M.st, rfl, M.u, hL, hL⟩, by rw [hq]; exact ha.1.1.2⟩

/-- `mainP` leaks the same from the same arguments, tape and table. -/
theorem mainP_ct (R : RoundImpl) :
    RelCT isa (Two (MnB (fun q => candOf q / 2) qOk)) (mainP R.name R.code) fun _ _ => True := by
  unfold mainP
  refine RelCT.seq reshape_ct (RelCT.seq trialSieve_ct (RelCT.seq (badLoad_ct (B := allOk))
    (two_ite' (fun a => decide (allOk a.1)) (fun _ _ h => h.2) ?_ (finMnB_ct fun _ _ h => h.1.1))))
  exact two_map (fun a => (⟨a.1, candOf a.1, a.1.L⟩ : TQD))
    (fun _ _ ⟨⟨h, _⟩, ha⟩ => ts_of h (of_decide_eq_true ha)) (tests_ct R)

/-- `mainQ` leaks the same from the same arguments, tape and table. -/
theorem mainQ_ct (R : RoundImpl) : RelCT isa (Two (MnB candOf pOk)) (mainQ R.name R.code) fun _ _ => True := by
  unfold mainQ
  refine RelCT.seq halve_ct (RelCT.seq trialSieve_ct (RelCT.seq (badLoad_ct (B := qOk))
    (two_ite' (fun a => decide (qOk a.1)) (fun _ _ h => h.2) ?_ (finMnB_ct fun _ _ h => h.1.1))))
  exact two_map (fun a => a) (fun _ _ h => h.1.1) (mainP_ct R)

/-- `main` leaks the same from the same arguments, tape and table. -/
theorem main_ct (R : RoundImpl) : RelCT isa (Two MnI) (main R.name R.code) fun _ _ => True := by
  unfold main
  refine RelCT.assoc (RelCT.seq mainA_ct (RelCT.seq residue_ct (RelCT.seq badLoad_ct
    (two_ite' (fun a => decide (goodRes a.1.g (candOf a.1))) (fun _ _ h => h.2) ?_
      (finMnB_ct fun _ _ h => h.1.1)))))
  refine RelCT.seq (two_map (fun a => a) (fun _ _ h => h.1.1) trialSieveN_ct)
    (RelCT.seq (badLoad_ct (B := pOk))
      (two_ite' (fun a => decide (pOk a.1)) (fun _ _ h => h.2) ?_ (finMnB_ct fun _ _ h => h.1.1)))
  exact two_map (fun a => a) (fun _ _ h => h.1.1) (mainQ_ct R)

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
