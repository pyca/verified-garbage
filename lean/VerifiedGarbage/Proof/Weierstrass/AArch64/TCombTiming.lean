import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym

/-! The direct lookup address depends only on the public scalar and table. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- Instructions before the first load from a selected table entry. -/
def publicHead (K : TCombCfg) : List Instr :=
  [decCounter] ++ K.digit ++ K.selSetup ++ K.directAddress

/-- The selected entry address is a function of the scalar, iteration and
symbol address. No scratch contents other than the scalar's bits affect it. -/
theorem publicHead_ok {K : TCombCfg} {s : State} {base T : Addr} {size k j : Nat}
    (hL : TCombLay K size) (hs : Scr s base size) (hj : 1 ≤ j) (hjn : j ≤ K.J)
    (hx : s.gpr .x19 = BitVec.ofNat 64 j) (hT : s.syms K.tsym = T)
    (hb : ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block (publicHead K)) s fun t =>
      t.gpr .x0 = base ∧ t.gpr .x19 = BitVec.ofNat 64 (j - 1) ∧ t.sp = s.sp ∧
      t.gpr .x16 = T + BitVec.ofNat 64 ((j - 1) * K.tblBytes) +
        BitVec.ofNat 64 (16 * K.M.n * (magH K.H (combWin K.w k (j - 1)) - 1)) := by
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hw := hL.w
  have hbsize : K.bits + K.w * K.J ≤ size := by
    have := hL.bits
    have := hL.kbytes
    unfold TCombCfg.zw at *
    omega
  have hwi : K.w * (j - 1) + K.w ≤ K.w * K.J := by
    rw [← Nat.mul_succ, show (j - 1).succ = j by omega]
    exact Nat.mul_le_mul_left K.w hjn
  have hHle : K.H ≤ 128 := by
    unfold TCombCfg.H
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 7 by omega)) (by decide)
  have hmag : magH K.H (combWin K.w k (j - 1)) ≤ K.H := by
    apply magH_le
    have e : 2 ^ K.w = 2 * K.H := by
      unfold TCombCfg.H; rw [← Nat.pow_succ']; congr 1; omega
    rw [← e]; exact combWin_lt _ _ _
  rw [publicHead, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono_syms (decCounter_ok s hj (by omega) hx) fun a ⟨a19, ka⟩ sa => ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (digitW_ok K (hs.of_keeps ka (by decide)) (k := k)
    (N := K.w * K.J) (by omega) (by omega) hwi hbsize (by
      have := hL.bitsw
      have := Nat.mul_le_mul_left K.w (show 1 ≤ K.J by omega)
      omega) a19
    (fun t ht => by rw [ka.mem]; exact hb t ht)) fun b ⟨b2, kb⟩ sb => ?_
  rw [WP.block_append_iff]
  refine WP.mono (selSetup_ok K (j := j - 1) (T := T) (by rw [kb.gpr _ (by decide), a19])
    (by rw [sb, sa, hT]) hL.tbl.2) fun c ⟨c16, c7, c5, _, kc⟩ => ?_
  refine WP.mono (directAddress_ok K (a := magH K.H (combWin K.w k (j - 1))) (by omega) (by have := hL.n8; omega) c16
    (by rw [kc.gpr _ (by decide), b2]) c5 c7) fun t ⟨t16, _, kt⟩ => ?_
  refine ⟨?_, ?_, ?_, t16⟩
  · rw [kt.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide),
      ka.gpr _ (by decide)]; exact hs.x0
  · rw [kt.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide), a19]
  · rw [kt.sp, kc.sp, kb.sp, ka.sp]

/-- The remaining loads, selection and point arithmetic. -/
def publicLoads (K : TCombCfg) : List Instr :=
  TCombCfg.directWords 0 K.E.x 0 K.M.n ++
  TCombCfg.directWords (8 * K.M.n) K.E.y K.one K.M.n ++ K.selZ

def publicRest (K : TCombCfg) : Prog isa :=
  .seq (.block (negYW K.M K.w K.neg K.zero K.E.y K.bits)) <|
  .seq (fprogB K.M (rcb3 K.S K.A K.E K.D)) <|
  .block (copyPt K.M.n K.A K.D)

/-- Split the first block while preserving its continuation. -/
theorem block_append_seq_ct {P Q : State → State → Prop} {a b : List Instr} {rest : Prog isa}
    (h : RelCT isa P (.seq (.block a) (.seq (.block b) rest)) Q) :
    RelCT isa P (.seq (.block (a ++ b)) rest) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq ab₁ c₁ =>
    cases e₂ with
    | seq ab₂ c₂ =>
      rw [Exec.block_iff, execBlock_append] at ab₁ ab₂
      obtain ⟨⟨u₁, v₁⟩, ea₁, eb₁⟩ := Option.bind_eq_some_iff.mp ab₁
      obtain ⟨⟨w₁, z₁⟩, load₁, ee₁⟩ := Option.map_eq_some_iff.mp eb₁
      obtain ⟨⟨u₂, v₂⟩, ea₂, eb₂⟩ := Option.bind_eq_some_iff.mp ab₂
      obtain ⟨⟨w₂, z₂⟩, load₂, ee₂⟩ := Option.map_eq_some_iff.mp eb₂
      simp only [Prod.mk.injEq] at ee₁ ee₂
      obtain ⟨rfl, rfl⟩ := ee₁
      obtain ⟨rfl, rfl⟩ := ee₂
      obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp
        (.seq (.block ea₁) (.seq (.block load₁) c₁))
        (.seq (.block ea₂) (.seq (.block load₂) c₂))
      exact ⟨by simpa only [List.append_assoc] using ht, hq⟩

/-- Public scalar bits and pointers at the start of an iteration. -/
def PublicStepPre (K : TCombCfg) (base T : Addr) (size k j : Nat) (s : State) : Prop :=
  Scr s base size ∧ s.gpr .x19 = BitVec.ofNat 64 j ∧ s.syms K.tsym = T ∧
    ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0

/-- Taint checks for the parts separated at the public address. -/
structure PublicChecks (K : TCombCfg) : Prop where
  init : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (.block K.init)
  head : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0, .x19]))
    (.block (publicHead K))
  tail : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0, .x19, .x16]))
    (.seq (.block (publicLoads K)) (publicRest K))

/-- The iteration has identical timing for the same public scalar, even
when the other register and scratch values differ. -/
theorem publicStep_ct {K : TCombCfg} {base T : Addr} {size k j : Nat}
    (hL : TCombLay K size) (hj : 1 ≤ j) (hjn : j ≤ K.J) (hc : PublicChecks K) :
    RelCT isa (fun s₁ s₂ => PublicStepPre K base T size k j s₁ ∧
      PublicStepPre K base T size k j s₂ ∧ s₁.sp = s₂.sp) (K.step true) (fun _ _ => True) := by
  have hh : RelCT isa (fun s₁ s₂ => PublicStepPre K base T size k j s₁ ∧
      PublicStepPre K base T size k j s₂ ∧ s₁.sp = s₂.sp)
      (.block (publicHead K)) (fun _ _ => True) := by
    intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨p₁, p₂, hsp⟩ e₁ e₂
    refine ⟨hc.head _ _ _ _ _ _ trivial trivial ⟨hsp, ?_⟩ e₁ e₂, trivial⟩
    intro r hr
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact p₁.1.x0.trans p₂.1.x0.symm
    · exact p₁.2.1.trans p₂.2.1.symm
  have hh' := hh.wpDep (F := fun (s t : State) => t.gpr .x0 = base ∧
    t.gpr .x19 = BitVec.ofNat 64 (j - 1) ∧ t.sp = s.sp ∧
    t.gpr .x16 = T + BitVec.ofNat 64 ((j - 1) * K.tblBytes) +
      BitVec.ofNat 64 (16 * K.M.n * (magH K.H (combWin K.w k (j - 1)) - 1)))
    (fun s₁ s₂ ⟨p₁, p₂, _⟩ =>
      ⟨publicHead_ok hL p₁.1 hj hjn p₁.2.1 p₁.2.2.1 p₁.2.2.2,
       publicHead_ok hL p₂.1 hj hjn p₂.2.1 p₂.2.2.1 p₂.2.2.2⟩)
  have e : K.step true = .seq (.block (publicHead K ++ publicLoads K)) (publicRest K) := by
    simp only [TCombCfg.step, TCombCfg.selectPublic, publicHead, publicLoads, publicRest,
      ite_true, List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  apply block_append_seq_ct
  refine hh'.seq ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨_, a, b, ⟨_, _, hsp⟩, p₁, p₂⟩ e₁ e₂
  refine ⟨hc.tail _ _ _ _ _ _ trivial trivial ⟨p₁.2.2.1.trans (hsp.trans p₂.2.2.1.symm), ?_⟩ e₁ e₂,
    trivial⟩
  intro r hr
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact p₁.1.trans p₂.1.symm
  · exact p₁.2.1.trans p₂.2.1.symm
  · exact p₁.2.2.2.trans p₂.2.2.2.symm

/-- Relate the public comb's iterations using their correctness invariant. -/
theorem publicLoop_ct {K : TCombCfg} {C : Spec.Weierstrass.Curve} {base T : Addr} {size k : Nat}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hM3 : AM3 C) (hG : Spec.Weierstrass.onCurve C (Spec.Weierstrass.G C) = true)
    (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n)) (hc : PublicChecks K)
    {a₀ b₀ : State} (hsp : a₀.sp = b₀.sp)
    (hFa : TCombFixed K C base size a₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (hFb : TCombFixed K C base size b₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    RelCT isa (fun a b => TCombInv K C base size k T
      (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) a₀ a K.J ∧
      TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) b₀ b K.J)
      (.loop (K.step true) (.nonzero .x .x19)) (fun _ _ => True) := by
  let I := fun j a b => 1 ≤ j ∧ j ≤ K.J ∧
    TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) a₀ a j ∧
    TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) b₀ b j
  have hstep : ∀ j, RelCT isa (I j) (K.step true) fun a b =>
      eval (.nonzero .x .x19) a = eval (.nonzero .x .x19) b ∧
      (eval (.nonzero .x .x19) a = some false → True) ∧
      (eval (.nonzero .x .x19) a = some true → ∃ m < j, I m a b) := by
    intro j
    by_cases hj : 1 ≤ j
    · by_cases hjn : j ≤ K.J
      · have h := (publicStep_ct hL hj hjn hc).mono
          (P' := I j) (fun a b ⟨_, _, ia, ib⟩ =>
            ⟨⟨ia.scr, ia.x19, ia.tsym, ia.bits⟩, ⟨ib.scr, ib.x19, ib.tsym, ib.bits⟩,
              ia.keep.sp.trans (hsp.trans ib.keep.sp.symm)⟩) (fun _ _ h => h)
        have hw := h.wp (fun a b ⟨_, _, ia, ib⟩ =>
          ⟨tstep_ok (publicLookup := true) hL hA hC hM3 hG hV hpn hFa hj hjn ia,
           tstep_ok (publicLookup := true) hL hA hC hM3 hG hV hpn hFb hj hjn ib⟩)
        refine hw.mono (fun _ _ h => h) fun a b ⟨_, ⟨ia, xa⟩, ⟨ib, xb⟩⟩ => ?_
        refine ⟨by simp only [eval, State.read, xa, xb], fun _ => trivial, fun ht => ?_⟩
        have hz : j - 1 ≠ 0 := by
          intro hz
          simp only [eval, State.read, xa, hz] at ht
          cases ht
        exact ⟨j - 1, by omega, by omega, by omega, ia, ib⟩
      · exact RelCT.of_false fun _ _ h => hjn h.2.1
    · exact RelCT.of_false fun _ _ h => hj h.1
  exact (RelCT.loop I hstep K.J).mono
    (fun a b ⟨ia, ib⟩ => ⟨by simpa only [TCombCfg.toComb_J] using hL.comb.J.1, Nat.le_refl _, ia, ib⟩) (fun _ _ h => h)

/-- The whole public comb, from identical public scalar bits. -/
theorem publicComb_ct {K : TCombCfg} {C : Spec.Weierstrass.Curve} {base T : Addr} {size k : Nat}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hM3 : AM3 C) (hG : Spec.Weierstrass.onCurve C (Spec.Weierstrass.G C) = true)
    (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n)) (hc : PublicChecks K) :
    RelCT isa (fun a b => Scr a base size ∧ Scr b base size ∧ a.sp = b.sp ∧
      ModOkA K.M size C.p a.mem base ∧ ModOkA K.M size C.p b.mem base ∧
      TCombFixed K C base size a k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) ∧
      TCombFixed K C base size b k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
      (K.comb true) (fun _ _ => True) := by
  intro a b ta tb a' b' hp ea eb
  obtain ⟨ha, hb, hsp, ma, mb, fa, fb⟩ := hp
  obtain ⟨_, ia, eia, hia⟩ := tcomb_init_ok hL hA hV hpn ha ma fa
  obtain ⟨_, ib, eib, hib⟩ := tcomb_init_ok hL hA hV hpn hb mb fb
  cases ea with
  | seq ea₁ ea₂ =>
    cases eb with
    | seq eb₁ eb₂ =>
      obtain ⟨rfl, rfl⟩ := Exec.det ea₁ eia
      obtain ⟨rfl, rfl⟩ := Exec.det eb₁ eib
      have ht := hc.init _ _ _ _ _ _ trivial trivial ⟨hsp, fun r hr => by
        simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
        subst hr
        exact ha.x0.trans hb.x0.symm⟩ ea₁ eb₁
      obtain ⟨hu, _⟩ := publicLoop_ct hL hA hC hM3 hG hV hpn hc hsp fa fb
        _ _ _ _ _ _ ⟨hia, hib⟩ ea₂ eb₂
      exact ⟨by rw [ht, hu], trivial⟩

end VG.Proof.Weierstrass.AArch64
