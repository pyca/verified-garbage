import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.TaintSym

/-! Direct lookup addresses are determined by the public scalar and table. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

def publicHead (K : TCombCfg) : List Instr :=
  [.alu .sub .rbx (.imm 1)] ++ K.digit ++ K.publicAddress

theorem publicHead_ok {K : TCombCfg} {s : State} {base T : Addr} {size k j : Nat}
    (hL : TCombLay K size) (hs : Scr s base size) (hj : 1 ≤ j) (hjn : j ≤ K.J)
    (hx : s.gpr .rbx = BitVec.ofNat 64 j) (hT : s.syms K.tsym = T)
    (hb : ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block (publicHead K)) s fun t =>
      t.gpr .rdi = base ∧ t.gpr .rbx = BitVec.ofNat 64 (j - 1) ∧
      t.gpr .rdx = T + BitVec.ofNat 64 ((j - 1) * K.tblBytes +
        16 * K.M.n * (magH K.H (combWin K.w k (j - 1)) - 1)) := by
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
  rw [publicHead, List.append_assoc, WP.block_append_iff]
  refine WP.mono_syms (decRbx_ok s hj (by omega) hx) fun a ⟨a19,ka⟩ sa => ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (digit_ok K (hs.of_keeps ka (by decide)) (k := k)
    (N := K.w * K.J) (by omega) (by omega) hwi hbsize a19
    (fun t ht => by rw [ka.2.1]; exact hb t ht)) fun b ⟨_,b8,kb⟩ sb => ?_
  refine WP.mono (publicAddress_ok K b (j := j - 1) (T := T)
    ((kb.1 _ (by decide)).trans a19) b8 (by rw [sb,sa,hT]) (by omega) hL.n.2 hmag)
    fun t ⟨tdx,kt,_,_⟩ => ?_
  exact ⟨by rw [kt.1 _ (by decide),kb.1 _ (by decide),ka.1 _ (by decide)]; exact hs.rdi,
    by rw [kt.1 _ (by decide),kb.1 _ (by decide),a19], tdx⟩

def publicLoads (K : TCombCfg) : List Instr :=
  TCombCfg.publicMask ++ K.publicLoad ++ K.selOne

def publicRest (K : TCombCfg) : Prog isa :=
  .seq (.block K.negY) <|
  .seq (fprogB K.M (rcb3m K.S K.A K.E K.D)) <|
  .block (K.digit ++ eqMask 0 ++ selPt K.M.n K.A K.D K.A ++ [.alu .test .rbx (.reg .rbx)])

/-- Split a block while retaining its trace and continuation. -/
theorem block_append_seq_ct {P Q : State → State → Prop} {a b : List Instr} {rest : Prog isa}
    (h : RelCT isa P (.seq (.block a) (.seq (.block b) rest)) Q) :
    RelCT isa P (.seq (.block (a ++ b)) rest) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq ab₁ c₁ =>
    cases e₂ with
    | seq ab₂ c₂ =>
      rw [Exec.block_iff, execBlock_append] at ab₁ ab₂
      obtain ⟨⟨u₁,v₁⟩,ea₁,eb₁⟩ := Option.bind_eq_some_iff.mp ab₁
      obtain ⟨⟨w₁,z₁⟩,load₁,ee₁⟩ := Option.map_eq_some_iff.mp eb₁
      obtain ⟨⟨u₂,v₂⟩,ea₂,eb₂⟩ := Option.bind_eq_some_iff.mp ab₂
      obtain ⟨⟨w₂,z₂⟩,load₂,ee₂⟩ := Option.map_eq_some_iff.mp eb₂
      simp only [Prod.mk.injEq] at ee₁ ee₂
      obtain ⟨rfl,rfl⟩ := ee₁
      obtain ⟨rfl,rfl⟩ := ee₂
      obtain ⟨ht,hq⟩ := h _ _ _ _ _ _ hp
        (.seq (.block ea₁) (.seq (.block load₁) c₁))
        (.seq (.block ea₂) (.seq (.block load₂) c₂))
      exact ⟨by simpa only [List.append_assoc] using ht,hq⟩

def PublicStepPre (K : TCombCfg) (base T : Addr) (size k j : Nat) (s : State) : Prop :=
  Scr s base size ∧ s.gpr .rbx = BitVec.ofNat 64 j ∧ s.syms K.tsym = T ∧
    ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0

structure PublicChecks (K : TCombCfg) : Prop where
  init : ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi])) (.block K.init)
  head : ConstantTime isa (fun _ => True) (Taint.AgreeS [K.tsym] (Taint.ofRegs [.rdi,.rbx]))
    (.block (publicHead K))
  tail : ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rbx,.rdx]))
    (.seq (.block (publicLoads K)) (publicRest K))

theorem publicStep_ct {K : TCombCfg} {base T : Addr} {size k j : Nat}
    (hL : TCombLay K size) (hj : 1 ≤ j) (hjn : j ≤ K.J) (hc : PublicChecks K) :
    RelCT isa (fun s₁ s₂ => PublicStepPre K base T size k j s₁ ∧
      PublicStepPre K base T size k j s₂) (K.step true) (fun _ _ => True) := by
  have hh : RelCT isa (fun s₁ s₂ => PublicStepPre K base T size k j s₁ ∧
      PublicStepPre K base T size k j s₂) (.block (publicHead K)) (fun _ _ => True) := by
    intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨p₁,p₂⟩ e₁ e₂
    refine ⟨hc.head _ _ _ _ _ _ trivial trivial ⟨Taint.agree_ofRegs ?_, ?_⟩ e₁ e₂,trivial⟩
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact p₁.1.rdi.trans p₂.1.rdi.symm
      · exact p₁.2.1.trans p₂.2.1.symm
    · intro n hn
      rw [List.mem_singleton.mp hn]
      exact p₁.2.2.1.trans p₂.2.2.1.symm
  have hh' := hh.wpDep (F := fun (_ t : State) => t.gpr .rdi = base ∧
    t.gpr .rbx = BitVec.ofNat 64 (j - 1) ∧
    t.gpr .rdx = T + BitVec.ofNat 64 ((j - 1) * K.tblBytes +
      16 * K.M.n * (magH K.H (combWin K.w k (j - 1)) - 1)))
    (fun s₁ s₂ ⟨p₁,p₂⟩ =>
      ⟨publicHead_ok hL p₁.1 hj hjn p₁.2.1 p₁.2.2.1 p₁.2.2.2,
       publicHead_ok hL p₂.1 hj hjn p₂.2.1 p₂.2.2.1 p₂.2.2.2⟩)
  have e : K.step true = .seq (.block (publicHead K ++ publicLoads K)) (publicRest K) := by
    simp only [TCombCfg.step,TCombCfg.selectPublic,publicHead,publicLoads,publicRest,
      ite_true,List.append_assoc,List.cons_append,List.nil_append]
  rw [e]
  apply block_append_seq_ct
  refine hh'.seq ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨_,a,b,_,p₁,p₂⟩ e₁ e₂
  refine ⟨hc.tail _ _ _ _ _ _ trivial trivial (Taint.agree_ofRegs ?_) e₁ e₂,trivial⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact p₁.1.trans p₂.1.symm
  · exact p₁.2.1.trans p₂.2.1.symm
  · exact p₁.2.2.trans p₂.2.2.symm

theorem publicLoop_ct {K : TCombCfg} {C : Spec.Weierstrass.Curve} {base T : Addr} {size k : Nat}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C)
    (hM3 : AM3 C) (hG : Spec.Weierstrass.onCurve C (Spec.Weierstrass.G C) = true)
    (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n)) (hc : PublicChecks K)
    {a₀ b₀ : State}
    (hFa : TCombFixed K C base size a₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (hFb : TCombFixed K C base size b₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    RelCT isa (fun a b => TCombInv K C base size k T
      (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) a₀ a K.J ∧
      TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) b₀ b K.J)
      (.loop (K.step true) .ne) (fun _ _ => True) := by
  let I := fun j a b => 1 ≤ j ∧ j ≤ K.J ∧
    TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) a₀ a j ∧
    TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) b₀ b j
  have hstep : ∀ j, RelCT isa (I j) (K.step true) fun a b =>
      eval .ne a = eval .ne b ∧ (eval .ne a = some false → True) ∧
      (eval .ne a = some true → ∃ m < j, I m a b) := by
    intro j
    by_cases hj : 1 ≤ j
    · by_cases hjn : j ≤ K.J
      · have h := (publicStep_ct hL hj hjn hc).mono
          (P' := I j) (fun a b ⟨_,_,ia,ib⟩ =>
            ⟨⟨ia.scr,ia.rbx,ia.tsym,ia.bits⟩,⟨ib.scr,ib.rbx,ib.tsym,ib.bits⟩⟩) (fun _ _ h => h)
        have hw := h.wp (fun a b ⟨_,_,ia,ib⟩ =>
          ⟨tstep_ok hL hC hM3 hG hV hpn hFa hj hjn ia true,
           tstep_ok hL hC hM3 hG hV hpn hFb hj hjn ib true⟩)
        refine hw.mono (fun _ _ h => h) fun a b ⟨_,⟨ia,xa⟩,⟨ib,xb⟩⟩ => ?_
        refine ⟨by simp only [eval,xa,xb],fun _ => trivial,fun ht => ?_⟩
        have hz : j - 1 ≠ 0 := by
          intro hz
          simp only [eval,xa,hz] at ht
          cases ht
        exact ⟨j - 1,by omega,by omega,by omega,ia,ib⟩
      · exact RelCT.of_false fun _ _ h => hjn h.2.1
    · exact RelCT.of_false fun _ _ h => hj h.1
  exact (RelCT.loop I hstep K.J).mono
    (fun a b ⟨ia,ib⟩ => ⟨by simpa only [TCombCfg.toComb_J] using hL.comb.J.1,Nat.le_refl _,ia,ib⟩)
    (fun _ _ h => h)

theorem publicComb_ct {K : TCombCfg} {C : Spec.Weierstrass.Curve} {base T : Addr} {size k : Nat}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C)
    (hM3 : AM3 C) (hG : Spec.Weierstrass.onCurve C (Spec.Weierstrass.G C) = true)
    (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n)) (hc : PublicChecks K) :
    RelCT isa (fun a b => Scr a base size ∧ Scr b base size ∧
      ModOkW K.M size C.p a.mem base ∧ ModOkW K.M size C.p b.mem base ∧
      TCombFixed K C base size a k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) ∧
      TCombFixed K C base size b k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
      (K.comb true) (fun _ _ => True) := by
  intro a b ta tb a' b' hp ea eb
  obtain ⟨ha,hb,ma,mb,fa,fb⟩ := hp
  obtain ⟨_,ia,eia,hia⟩ := tcomb_init_ok hL hV hpn ha ma fa
  obtain ⟨_,ib,eib,hib⟩ := tcomb_init_ok hL hV hpn hb mb fb
  cases ea with
  | seq ea₁ ea₂ =>
    cases eb with
    | seq eb₁ eb₂ =>
      obtain ⟨rfl,rfl⟩ := Exec.det ea₁ eia
      obtain ⟨rfl,rfl⟩ := Exec.det eb₁ eib
      have ht := hc.init _ _ _ _ _ _ trivial trivial (Taint.agree_ofRegs fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact ha.rdi.trans hb.rdi.symm) ea₁ eb₁
      obtain ⟨hu,_⟩ := publicLoop_ct hL hC hM3 hG hV hpn hc fa fb
        _ _ _ _ _ _ ⟨hia,hib⟩ ea₂ eb₂
      exact ⟨by rw [ht,hu],trivial⟩

end VG.Proof.Weierstrass.X86_64
