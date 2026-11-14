module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Ecdh.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Scalars
public import VerifiedGarbage.Impl.NatPairs
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-! ### `Weierstrass.AArch64.TCombTiming`, which only this module used -/

section

/-! The direct lookup address depends only on the public scalar and table. -/

@[expose] public section

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
    omega_arith
  have hwi : K.w * (j - 1) + K.w ≤ K.w * K.J := by
    rw [← Nat.mul_succ, show (j - 1).succ = j by omega_using [hj]]
    exact Nat.mul_le_mul_left K.w hjn
  have hHle : K.H ≤ 128 := by
    unfold TCombCfg.H
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 7 by omega_using [hw])) (by decide)
  have hmag : magH K.H (combWin K.w k (j - 1)) ≤ K.H := by
    apply magH_le
    have e : 2 ^ K.w = 2 * K.H := by
      unfold TCombCfg.H; rw [← Nat.pow_succ']; congr 1; omega_using [hw]
    rw [← e]; exact combWin_lt _ _ _
  rw [publicHead, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono_syms (decCounter_ok s hj (by omega_using [hjn, hJ]) hx) fun a ⟨a19, ka⟩ sa => ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (digitW_ok K (hs.of_keeps ka (by decide)) (k := k)
    (N := K.w * K.J) (by omega_using [hw]) (by omega_using [hw]) hwi hbsize (by
      have := hL.bitsw
      have := Nat.mul_le_mul_left K.w (show 1 ≤ K.J by omega_using [hJ])
      omega_arith) a19
    (fun t ht => by rw [ka.mem]; exact hb t ht)) fun b ⟨b2, kb⟩ sb => ?_
  rw [WP.block_append_iff]
  refine WP.mono (selSetup_ok K (j := j - 1) (T := T) (by rw [kb.gpr _ (by decide), a19])
    (by rw [sb, sa, hT]) hL.tbl.2) fun c ⟨c16, c7, c5, _, kc⟩ => ?_
  refine WP.mono (directAddress_ok K (a := magH K.H (combWin K.w k (j - 1))) (by omega_using [hHle, hmag]) (by have := hL.n8; omega_using [this]) c16
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
    simp only [TCombCfg.step, TCombCfg.selectPublic, publicHead, publicLoads, publicRest, addP,
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
          ⟨tstep_ok (publicLookup := true) hL hA hC hM3 hG hV hpn hFa hj hjn ia (pa := none) trivial trivial trivial,
           tstep_ok (publicLookup := true) hL hA hC hM3 hG hV hpn hFb hj hjn ib (pa := none) trivial trivial trivial⟩)
        refine hw.mono (fun _ _ h => h) fun a b ⟨_, ⟨ia, xa⟩, ⟨ib, xb⟩⟩ => ?_
        refine ⟨by simp only [eval, State.read, xa, xb], fun _ => trivial, fun ht => ?_⟩
        have hz : j - 1 ≠ 0 := by
          intro hz
          simp only [eval, State.read, xa, hz] at ht
          cases ht
        exact ⟨j - 1, by omega_using [hj], by omega_using [hz], by omega_using [hjn], ia, ib⟩
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

end

end


/-! ## `Timing` -/

@[expose] public section

section

/-! Verification's table lookup uses only the public digest and signature. -/
namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 (U V)
variable {c : Cfg}

/-- The scalar is determined by the public digest and signature. -/
def publicU (c : Cfg) (s : State) : Nat :=
  (Fin.ofNat c.C.n (dig c s >>> c.sh) * Fin.ofNat c.C.n (sigS c s) ^ (c.C.n - 2)).val

/-- Equality of the digest and signature buffers implies equality of the
public lookup scalar, without reducing concrete curve arithmetic. -/
theorem publicU_congr {c : Cfg} {a b : State}
    (hd : Spec.Ecdsa.bytesAt a.mem (a.gpr .x1) c.C.len =
      Spec.Ecdsa.bytesAt b.mem (b.gpr .x1) c.C.len)
    (hs : Spec.Ecdsa.bytesAt a.mem (a.gpr .x2) (2 * c.C.len) =
      Spec.Ecdsa.bytesAt b.mem (b.gpr .x2) (2 * c.C.len)) : publicU c a = publicU c b := by
  rw [Nat.two_mul, bytesAt_add, bytesAt_add] at hs
  have hs' := (List.append_inj hs (by simp only [length_bytesAt])).2
  have hd' : dig c a = dig c b := congrArg Spec.Weierstrass.ofBytes hd
  have hss : sigS c a = sigS c b := congrArg Spec.Weierstrass.ofBytes hs'
  simp only [publicU, hd', hss]

theorem mid_publicU {c : Cfg} {s₀ s : State} {base : Addr} {g : Reg → BitVec 64}
    (h : Mid c s₀ base g s) : sv c base s U = publicU c s₀ := by
  have he := congrArg Fin.val h.u
  simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt h.u_lt, publicU] using he

/-- The state needed at the public comb boundary. -/
def CombReady (c : Cfg) (s₀ s : State) : Prop :=
  Scr s (s₀.gpr .x3) size ∧ ModOkA c.combCfg.M size c.C.p s.mem (s₀.gpr .x3) ∧
    TCombFixed c.combCfg c.C (s₀.gpr .x3) size s (publicU c s₀) (s₀.syms c.tsym) c.combWords

/-- Build the bit table and recover the fixed-base comb's precondition. -/
theorem bits_combReady (hc : CfgOk c) {s₀ s : State} {g : Reg → BitVec 64}
    (hM : Mid c s₀ (s₀.gpr .x3) g s) (hTP : TblPre c s₀ (s₀.syms c.tsym) (s₀.gpr .x3)) :
    WP isa (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) s (CombReady c s₀) := by
  let base := s₀.gpr .x3
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.scr.nowrap
  have hp3 := hc.p_ge
  have F := hM.fixed
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_using [hp3])
  refine WP.mono_syms (bits_ok hM.scr h0 (by omega_using [h7]) (sl_le c h7 (i := U) (by decide))
    (tbl_le h7) (sl_lt4096 h0 h7 (i := U) (by decide)) (by have := bitsAt0_le c h7; omega_using [this])
    (Or.inl (by have := sl_below_bits c (i := U) (by decide) 0 0; omega_using [this])))
    fun s₁ ⟨b₁, k₁, O₁⟩ sy₁ => ?_
  have hs₁ := hM.scr.of_keepRegs k₁ (by decide)
  have U₁ : Unch base [(bitsAt c.n 0, 64 * c.n)] s.mem s₁.mem := O₁.unch
  have F₁ := F.unch h7 hn (fixedOk_tbl 0) U₁
  obtain ⟨hTM, hout⟩ := tbl_of hTP hM.rd hM.unch
  have hTM₁ : TblMem s₁ (s₀.syms c.tsym) c.combWords :=
    TblMem.of_unch hTM (by rw [k₁.rd, k₁.wr]) U₁ (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact tbl_le h7) hout
  refine ⟨hs₁, modP_of hc F₁.mp, ?_⟩
  rw [← mid_publicU hM]
  refine ⟨?_, ?_, ?_, F₁.zero, ?_, wordsVal_lt _ _ _ _, by rw [sy₁, hM.syms]; rfl, hTM₁, hout⟩
  · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base (c.sl AP) c.n) = _
    rw [F₁.ap]; exact toM_cmont hc _
  · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base (c.sl BM) c.n) = _
    rw [F₁.bm]; exact toM_cmont hc _
  · intro x hx
    simp only [combRo, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · show wordsVal s₁.mem base (c.sl AP) c.n < _; rw [F₁.ap]; exact hmont _
    · show wordsVal s₁.mem base (c.sl BM) c.n < _; rw [F₁.bm]; exact hmont _
    · show wordsVal s₁.mem base (c.sl ZERO) c.n < _; rw [F₁.zero]; omega_using [hp3]
  · intro t ht
    show s₁.mem (off base (bitsAt c.n 0 + t)) = _
    rw [b₁ t ht]

/-- Everything up to the public comb, with an empty final block. -/
def verifyPrefix (c : Cfg) : Prog isa :=
  .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.args c)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.prefixWith c (some D)) <|
  .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.loadS c)) <|
  .seq (.block (Impl.Ecdh.AArch64.Cfg.peer c)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.validate c) <|
  .seq (Impl.Ecdsa.Verify.AArch64.Cfg.scalars c) <| .seq c.nPow <|
  .seq (Impl.Ecdsa.Verify.AArch64.Cfg.uv c) <|
  .seq (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) (.block [])

/-- After the public comb. -/
def verifySuffix (c : Cfg) : Prog isa :=
  .seq (.seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.save c))
    (.seq (c.winPrep (c.sl V)) (.seq (WinCfg.window (winQ c)) (Impl.Ecdsa.Verify.AArch64.Cfg.sum c))))
    (Impl.Ecdsa.Verify.AArch64.Cfg.tail c)

theorem verifyPrefix_ok (hc : CfgOk c) {s₀ : State} (hp : VPre c s₀) :
    WP isa (verifyPrefix c) s₀ (CombReady c s₀) := by
  refine front_ok hc hp fun g s₁ _ hF => mid_ok hc hF fun s₂ hM => ?_
  exact WP.seq (WP.mono (bits_combReady hc hM hp.tbl) fun _ h => WP.block_nil h)

/-- Splitting a full execution at the public lookup, preserving its trace. -/
theorem verify_cut {c : Cfg} {s s' : State} {t : List Leak}
    (he : Exec isa (Impl.Ecdsa.Verify.AArch64.Cfg.verify c) s t s') :
    ∃ a b tp tc ts, Exec isa (verifyPrefix c) s tp a ∧
      Exec isa (c.combCfg.comb true) a tc b ∧ Exec isa (verifySuffix c) b ts s' ∧
      t = tp ++ tc ++ ts := by
  cases he with
  | seq e0 h => cases h with
    | seq e1 h => cases h with
      | seq e2 h => cases h with
        | seq e3 h => cases h with
          | seq e4 h => cases h with
            | seq e5 h => cases h with
              | seq e6 h => cases h with
                | seq e7 h => cases h with
                  | seq ep h =>
                    cases ep with
                    | seq eb h => cases h with
                      | seq ec er =>
                        have nil : ∀ a : State, Exec isa (.block []) a [] a := fun _ => .block rfl
                        have epre := Exec.seq e0 (.seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5
                          (.seq e6 (.seq e7 (.seq eb (nil _)))))))))
                        refine ⟨_, _, _, _, _, epre, ec, .seq er h, ?_⟩
                        simp only [List.append_nil, List.append_assoc]

/-- The shared contract makes the scalar, pointers and table address public. -/
def VerifyPublic (c : Cfg) (a b : State) : Prop :=
  AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3]) a b ∧
    a.syms c.tsym = b.syms c.tsym ∧ publicU c a = publicU c b

structure VerifyChecks (c : Cfg) : Prop where
  comb : PublicChecks c.combCfg
  before : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3])) (verifyPrefix c)
  after : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (verifySuffix c)

/-- Timing of the entire verifier, allowing exactly its public inputs to
influence the selected addresses. -/
theorem verify_public_ct (hc : CfgOk c) (hC : Law c.C)
    (hT : CombOkW c.C Cfg.combW (Cfg.combJ c.n) c.tbl c.start)
    (checks : VerifyChecks c) :
    ConstantTime isa (VPre c) (VerifyPublic c) (Impl.Ecdsa.Verify.AArch64.Cfg.verify c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ ⟨pub, sym, scalar⟩ e₁ e₂
  obtain ⟨a₁, b₁, tp₁, tc₁, ts₁, ep₁, ec₁, es₁, et₁⟩ := verify_cut e₁
  obtain ⟨a₂, b₂, tp₂, tc₂, ts₂, ep₂, ec₂, es₂, et₂⟩ := verify_cut e₂
  have ht := checks.before _ _ _ _ _ _ trivial trivial pub ep₁ ep₂
  obtain ⟨_, _, wp₁, ready₁⟩ := verifyPrefix_ok hc pre₁
  obtain ⟨_, _, wp₂, ready₂⟩ := verifyPrefix_ok hc pre₂
  obtain ⟨_, rfl⟩ := Exec.det ep₁ wp₁
  obtain ⟨_, rfl⟩ := Exec.det ep₂ wp₂
  have base : s₁.gpr .x3 = s₂.gpr .x3 := pub.2 .x3 (by decide)
  have sp : a₁.sp = a₂.sp := (Exec.rdwr ep₁).2.2.trans (pub.1.trans (Exec.rdwr ep₂).2.2.symm)
  have second : Scr a₂ (s₁.gpr .x3) size ∧ ModOkA c.combCfg.M size c.C.p a₂.mem (s₁.gpr .x3) ∧
      TCombFixed c.combCfg c.C (s₁.gpr .x3) size a₂ (publicU c s₁) (s₁.syms c.tsym) c.combWords := by
    rw [base, scalar, sym]; exact ready₂
  have hh := publicComb_ct (tcombLay hc.toBaseCfgOk) (combA hc.toBaseCfgOk) hC hc.am3 hc.onG (tcombVals hc.toBaseCfgOk hC hT)
    hc.p_lt checks.comb _ _ _ _ _ _
    ⟨ready₁.1, second.1, sp, ready₁.2.1, second.2.1, ready₁.2.2, second.2.2⟩ ec₁ ec₂
  have wpComb := fun {s₀ a : State} (h : CombReady c s₀ a) =>
    tcomb_ok (publicLookup := true) (tcombLay hc.toBaseCfgOk) (combA hc.toBaseCfgOk) hC hc.am3 hc.onG
      (tcombVals hc.toBaseCfgOk hC hT) hc.p_lt h.1 h.2.1 h.2.2 (pa := none) trivial trivial trivial
  obtain ⟨_, _, wc₁, keep₁, _⟩ := wpComb ready₁
  obtain ⟨_, _, wc₂, keep₂, _⟩ := wpComb ready₂
  obtain ⟨_, rfl⟩ := Exec.det ec₁ wc₁
  obtain ⟨_, rfl⟩ := Exec.det ec₂ wc₂
  have ht' := checks.after _ _ _ _ _ _ trivial trivial
    ⟨keep₁.sp.trans (sp.trans keep₂.sp.symm), fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst hr
      rw [keep₁.gpr _ (x0_not_tcombClob hc.n10), keep₂.gpr _ (x0_not_tcombClob hc.n10),
        ready₁.1.x0, ready₂.1.x0, base]⟩ es₁ es₂
  rw [et₁, et₂, ht, hh.1, ht']

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JacPublic` -/

section

/-! The Jacobian branches depend on the public signature, digest and public key. -/
namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Mont
open VG.Impl.Ecdsa.Verify.AArch64 (U V)

/-- The variable-base multiplication scalar. -/
def publicV (c : Cfg) (s : State) : Nat :=
  (Fin.ofNat c.C.n (sigR c s) * Fin.ofNat c.C.n (sigS c s) ^ (c.C.n-2)).val

theorem mid_publicV {c : Cfg} {s₀ s : State} {base : Addr} {g : Reg → BitVec 64}
    (h : Mid c s₀ base g s) : VG.Proof.Ecdsa.AArch64.sv c base s V = publicV c s₀ := by
  have he := congrArg Fin.val h.v
  simpa only [Fin.val_ofNat,Nat.mod_eq_of_lt h.v_lt,publicV] using he

/-- Equal public-key buffers determine every input of key validation. -/
theorem publicKey_congr {c : Cfg} {s t : State}
    (h : Spec.Ecdsa.bytesAt s.mem (s.gpr .x0) (1+2*c.C.len) =
      Spec.Ecdsa.bytesAt t.mem (t.gpr .x0) (1+2*c.C.len)) :
    s.mem (s.gpr .x0) = t.mem (t.gpr .x0) ∧ keyX c s = keyX c t ∧ keyY c s = keyY c t := by
  rw [bytesAt_add,bytesAt_add] at h
  obtain ⟨htag,hxy⟩ := List.append_inj h (by simp only [length_bytesAt])
  have ht : s.mem (s.gpr .x0) = t.mem (t.gpr .x0) := by
    simpa [Spec.Ecdsa.bytesAt] using htag
  rw [Nat.two_mul,bytesAt_add,bytesAt_add] at hxy
  obtain ⟨hx,hy⟩ := List.append_inj hxy (by simp only [length_bytesAt])
  refine ⟨ht,congrArg Spec.Weierstrass.ofBytes hx,?_⟩
  have hy' := congrArg Spec.Weierstrass.ofBytes hy
  simpa only [keyY,BitVec.ofNat_add,BitVec.add_assoc] using hy'

/-- The stronger internal relation uses only bytes the existing specification makes public. -/
structure JacPublicT (c : Cfg) (tsym : String) (s t : State) : Prop where
  ptrs : AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3]) s t
  table : s.syms tsym = t.syms tsym
  key : Spec.Ecdsa.bytesAt s.mem (s.gpr .x0) (1+2*c.C.len) =
    Spec.Ecdsa.bytesAt t.mem (t.gpr .x0) (1+2*c.C.len)
  digest : Spec.Ecdsa.bytesAt s.mem (s.gpr .x1) c.C.len =
    Spec.Ecdsa.bytesAt t.mem (t.gpr .x1) c.C.len
  sig : Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (2*c.C.len) =
    Spec.Ecdsa.bytesAt t.mem (t.gpr .x2) (2*c.C.len)

/-- `JacPublicT` with the comb's tables at `c.tsym`. -/
abbrev JacPublic (c : Cfg) := JacPublicT c c.tsym

theorem JacPublicT.u {c : Cfg} {tsym : String} {s t : State} (h : JacPublicT c tsym s t) : publicU c s = publicU c t :=
  publicU_congr h.digest h.sig

theorem JacPublicT.signature {c : Cfg} {tsym : String} {s t : State} (h : JacPublicT c tsym s t) :
    sigR c s = sigR c t ∧ sigS c s = sigS c t := by
  have hs := h.sig
  rw [Nat.two_mul,bytesAt_add,bytesAt_add] at hs
  obtain ⟨hr,hs⟩ := List.append_inj hs (by simp only [length_bytesAt])
  exact ⟨congrArg Spec.Weierstrass.ofBytes hr,congrArg Spec.Weierstrass.ofBytes hs⟩

theorem JacPublicT.v {c : Cfg} {tsym : String} {s t : State} (h : JacPublicT c tsym s t) : publicV c s = publicV c t := by
  rw [publicV,publicV,h.signature.1,h.signature.2]

theorem JacPublicT.keyOk {c : Cfg} {tsym : String} {s t : State} (h : JacPublicT c tsym s t) : KeyOk c s ↔ KeyOk c t := by
  obtain ⟨tag,x,y⟩ := publicKey_congr h.key
  simp only [KeyOk,tag,x,y]

/-- The initialized peer coordinates are equal in the two executions. -/
theorem mid_peer_public {c : Cfg} {s₀ t₀ s t : State} {base : Addr}
    {g₁ g₂ : Reg → BitVec 64} {ts : String} (h : JacPublicT c ts s₀ t₀)
    (hs : Mid c s₀ base g₁ s) (ht : Mid c t₀ base g₂ t) :
    VG.Proof.Weierstrass.AArch64.tmv c.C c.n base s (c.sl VG.Impl.Ecdh.AArch64.PX) =
      VG.Proof.Weierstrass.AArch64.tmv c.C c.n base t (c.sl VG.Impl.Ecdh.AArch64.PX) ∧
    VG.Proof.Weierstrass.AArch64.tmv c.C c.n base s (c.sl VG.Impl.Ecdh.AArch64.PY) =
      VG.Proof.Weierstrass.AArch64.tmv c.C c.n base t (c.sl VG.Impl.Ecdh.AArch64.PY) := by
  obtain ⟨_,x,y⟩ := publicKey_congr h.key
  change toM _ _ _ = toM _ _ _ ∧ toM _ _ _ = toM _ _ _
  rw [hs.px,ht.px,hs.py,ht.py]
  simp only [h.keyOk,x,y]
  exact ⟨True.intro,True.intro⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JacPeer` -/

section

/-! The verifier's initialized peer point is determined by its public key buffer. -/
namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)

theorem Mid.peer_rep {c : Cfg} (hc : CfgOk c) (hC : Law c.C)
    {s₀ a : State} {base : Addr} {g : Reg → BitVec 64} (h : Mid c s₀ base g a) :
    Rep c.C (tmv c.C c.n base a (c.sl PX)) (tmv c.C c.n base a (c.sl PY))
      (tmv c.C c.n base a (c.sl ONEP))
      (peerPt c (s₀.mem (s₀.gpr .x0)=4) (keyX c s₀) (keyY c s₀)) := by
  rw [onep_tmv hc h.fixed]
  exact peerPt_rep hC _ _ _ h.px h.py

theorem JacPublicT.peerPoint {c : Cfg} {tsym : String} {s t : State} (h : JacPublicT c tsym s t) :
    peerPt c (s.mem (s.gpr .x0)=4) (keyX c s) (keyY c s) =
      peerPt c (t.mem (t.gpr .x0)=4) (keyX c t) (keyY c t) := by
  obtain ⟨tag,x,y⟩ := publicKey_congr h.key
  rw [tag,x,y]

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JacPrefix` -/

