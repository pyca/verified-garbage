import VerifiedGarbage.Proof.Weierstrass.AArch64.JacFinishTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombTiming

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)
open Spec.Weierstrass

/-- The initialized accumulator and fixed coefficients shared by two runs. -/
def jacCombLive (K : TCombCfg) : List Nat := combRo K.toComb ++ [K.A.x,K.A.y,K.A.z]

def CombShared (K : TCombCfg) (C : Curve) (base : Addr) (s t : State) : Prop :=
  ∀ x∈jacCombLive K, tmv C K.M.n base s x = tmv C K.M.n base t x

structure JacCombChecks (K : TCombCfg) : Prop where
  init : FieldCT (.block K.init)
  digit : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]))
    (.block (decCounter::K.digit))
  address : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]))
    (.block (K.selSetup ++ K.directAddress))
  entry : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19,.x16]))
    (.seq (.block (publicLoads K)) (.block (negYW K.M K.w K.neg K.zero K.E.y K.bits)))
  mixed : JacMixedChecks (Jacobian.combWinCfg K) K.A K.E K.D
  copy : FieldCT (.block (copyPt K.M.n K.A K.D))

/-- The direct address is determined entirely by the common public digit. -/
theorem jacComb_address_ok {K : TCombCfg} {s : State} {base T : Addr} {size k i : Nat}
    (hL : TCombLay K size) (hs : Scr s base size)
    (hx : s.gpr .x19 = BitVec.ofNat 64 i) (hT : s.syms K.tsym = T)
    (hm : s.gpr .x2 = BitVec.ofNat 64 (magH K.H (combWin K.w k i))) :
    WP isa (.block (K.selSetup ++ K.directAddress)) s fun t =>
      t.gpr .x0 = base ∧ t.gpr .x19 = BitVec.ofNat 64 i ∧ t.sp=s.sp ∧
      t.gpr .x16 = T + BitVec.ofNat 64 (i*K.tblBytes) +
        BitVec.ofNat 64 (16*K.M.n*(magH K.H (combWin K.w k i)-1)) := by
  have hw := hL.w
  have hHle : K.H≤128 := Nat.le_trans
    (Nat.pow_le_pow_right (by decide) (show K.w-1≤7 by omega)) (by decide)
  have hmag : magH K.H (combWin K.w k i)≤K.H := by
    apply magH_le
    have e : 2^K.w=2*K.H := by
      unfold TCombCfg.H; rw [←Nat.pow_succ']; congr 1; omega
    rw [←e]; exact combWin_lt _ _ _
  rw [WP.block_append_iff]
  refine WP.mono (selSetup_ok K hx hT hL.tbl.2) fun c ⟨c16,c7,c5,_,kc⟩ => ?_
  refine WP.mono (directAddress_ok K (a:=magH K.H (combWin K.w k i))
    (by omega) (by have := hL.n8; omega) c16 (by rw [kc.gpr _ (by decide),hm]) c5 c7)
    fun t ⟨t16,_,kt⟩ => ?_
  exact ⟨by rw [kt.gpr _ (by decide),kc.gpr _ (by decide),hs.x0],
    by rw [kt.gpr _ (by decide),kc.gpr _ (by decide),hx],kt.sp.trans kc.sp,t16⟩

/-- Table selection and conditional negation have equal traces for a public digit. -/
theorem jacComb_entry_ct {K : TCombCfg} {base T : Addr} {size k i : Nat}
    (hL : TCombLay K size) (hc : JacCombChecks K) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ s.sp=t.sp ∧
      s.gpr .x19=BitVec.ofNat 64 i ∧ t.gpr .x19=BitVec.ofNat 64 i ∧
      s.syms K.tsym=T ∧ t.syms K.tsym=T ∧
      s.gpr .x2=BitVec.ofNat 64 (magH K.H (combWin K.w k i)) ∧
      t.gpr .x2=BitVec.ofNat 64 (magH K.H (combWin K.w k i)))
      (.seq (.block K.selectPublic) (.block (negYW K.M K.w K.neg K.zero K.E.y K.bits)))
      (fun _ _ => True) := by
  have hd : RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ s.sp=t.sp ∧
      s.gpr .x19=BitVec.ofNat 64 i ∧ t.gpr .x19=BitVec.ofNat 64 i ∧
      s.syms K.tsym=T ∧ t.syms K.tsym=T ∧
      s.gpr .x2=BitVec.ofNat 64 (magH K.H (combWin K.w k i)) ∧
      t.gpr .x2=BitVec.ofNat 64 (magH K.H (combWin K.w k i)))
      (.block (K.selSetup++K.directAddress)) (fun _ _ => True) := by
    intro s t ts tt s' t' ⟨hs,ht,sp,xs,xt,_,_,_,_⟩ es et
    refine ⟨hc.address _ _ _ _ _ _ trivial trivial ⟨sp,?_⟩ es et,trivial⟩
    intro r hr
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.x0.trans ht.x0.symm
    · exact xs.trans xt.symm
  have hp := hd.wpDep (F:=fun (s t : State) => t.gpr .x0=base ∧ t.gpr .x19=BitVec.ofNat 64 i ∧
      t.sp=s.sp ∧ t.gpr .x16=T+BitVec.ofNat 64 (i*K.tblBytes)+
        BitVec.ofNat 64 (16*K.M.n*(magH K.H (combWin K.w k i)-1)))
    (fun s t ⟨hs,ht,_,xs,xt,ys,yt,ms,mt⟩ =>
      ⟨jacComb_address_ok hL hs xs ys ms,jacComb_address_ok hL ht xt yt mt⟩)
  have he : K.selectPublic = (K.selSetup++K.directAddress)++publicLoads K := by
    simp [TCombCfg.selectPublic,publicLoads,List.append_assoc]
  rw [he]
  apply block_append_seq_ct
  refine hp.seq ?_
  intro s t ts tt s' t' ⟨_,a,b,⟨_,_,sp,_,_,_,_,_,_⟩,hs,ht⟩ es et
  refine ⟨hc.entry _ _ _ _ _ _ trivial trivial ⟨hs.2.2.1.trans (sp.trans ht.2.2.1.symm),?_⟩ es et,trivial⟩
  intro r hr
  simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hs.1.trans ht.1.symm
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.2.2.2.trans ht.2.2.2.symm

/-- Affine representatives determine their coordinates uniquely. -/
theorem rep_one_unique {C : Curve} (hC : Law C) {X Y X' Y' : Fe C} {P : Point C}
    (h : Rep C X Y 1 P) (h' : Rep C X' Y' 1 P) : X=X' ∧ Y=Y' := by
  cases P with
  | infinity => exact False.elim (hC.one_ne_zero h.2.2)
  | affine x y => exact ⟨h.2.1.trans h'.2.1.symm,h.2.2.trans h'.2.2.symm⟩

/-- Mixed addition followed by the accumulator copy preserves public fields. -/
theorem jacComb_sum_relCT {K : TCombCfg} {base : Addr} {size m : Nat} [NeZero m]
    (hL : TCombLay K size) (hA : CombA K.toComb) (hm : UnitMod m (2^(64*K.M.n)))
    (hn : K.M.n=4) (hone : K.one<m) (hc : JacCombChecks K) {E : Nat → Fin m} :
    RelCT isa (FieldPair K.M base size m (·∈combSlots K.toComb)
      ([K.E.x,K.E.y,K.E.z]++jacCombLive K) E) (Jacobian.jacCombSum K)
      (fun s t => ∃ E',FieldPair K.M base size m (·∈combSlots K.toComb) (jacCombLive K) E' s t) := by
  have hSl : ∀ x∈rcbW K.S K.D++rcbR K.S K.A K.E, x∈combSlots K.toComb := by
    intro x hx
    simp only [rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with hx | hx
    · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem
    · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem
  have hv : ∀ x∈rcbR K.S K.A K.E, x∈[K.E.x,K.E.y,K.E.z]++jacCombLive K := by
    simp only [rcbR,jacCombLive,combRo,TCombCfg.toComb,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    intros; grind
  have hmix := jacMixedAdd_relCT (K:=Jacobian.combWinCfg K) (base:=base) (E:=E)
    hL.comb.lay ⟨hA.sl,hA.mod⟩ hm hL.comb.add hSl hv hone hc.mixed
  unfold Jacobian.jacCombSum
  refine hmix.seq (RelCT.exists_ fun E' => ?_)
  rw [←hn]
  have hcp := copyPoint_relCT (base:=base) (E:=E') hL.comb.lay ⟨hA.sl,hA.mod⟩
    (o:=K.A) (q:=K.D) (V:=[K.D.x,K.D.y,K.D.z]++([K.E.x,K.E.y,K.E.z]++jacCombLive K))
    (by intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl | rfl <;> tcomb_mem)
    (by intro x hx; exact List.mem_append_left _ hx) hc.copy
  exact hcp.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub (by intro x hx; exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hx)))⟩)

/-- The digit stage preserves memory and exposes the common branch condition. -/
theorem jacComb_digit_ok {K : TCombCfg} {base : Addr} {size k j : Nat}
    (hL : TCombLay K size) {s : State} (hs : Scr s base size)
    (hj : 1≤j) (hjn : j≤K.J) (hx : s.gpr .x19=BitVec.ofNat 64 j)
    (hb : ∀ q<K.w*K.J,s.mem (off base (K.bits+q))=if k.testBit q then 1 else 0) :
    WP isa (.block (decCounter::K.digit)) s fun t =>
      Keeps [.x19,.x2,.x3,.x4,.x9,.x16] s t ∧ t.syms=s.syms ∧
      t.gpr .x19=BitVec.ofNat 64 (j-1) ∧
      t.gpr .x2=BitVec.ofNat 64 (magH K.H (combWin K.w k (j-1))) := by
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  rw [←List.singleton_append,WP.block_append_iff]
  refine WP.mono_syms (decCounter_ok s hj (by omega) hx) fun d ⟨bd,kd⟩ syd => ?_
  have hwi : K.w*(j-1)+K.w≤K.w*K.J := by
    rw [←Nat.mul_succ,show (j-1).succ=j by omega]
    exact Nat.mul_le_mul_left K.w hjn
  have hbsize : K.bits+K.w*K.J≤size := by
    have := hL.bits; have := hL.kbytes; unfold TCombCfg.zw at *; omega
  refine WP.mono_syms (digitW_ok K (hs.of_keeps kd (by decide)) (k:=k)
    (j:=j-1) (N:=K.w*K.J) (by have := hL.w; omega) (by have := hL.w; omega)
    hwi hbsize (by have := hL.bitsw; omega) bd (fun q hq => by rw [kd.mem]; exact hb q hq))
    fun t ⟨mag,kt⟩ syt => ?_
  exact ⟨(kd.mono (by simp)).trans (kt.mono (by simp)),syt.trans syd,
    by rw [kt.gpr _ (by decide),bd],mag⟩

/-- Every initialized comb slot lies in its checked field layout. -/
theorem jacCombLive_slots {K : TCombCfg} {x : Nat} (hx : x∈jacCombLive K) :
    x∈combSlots K.toComb := by
  simp only [jacCombLive,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with hx | rfl | rfl | rfl
  · exact combRo_slots x hx
  all_goals tcomb_mem

/-- Selecting an entry does not change the accumulator or fixed coefficients. -/
theorem jacComb_entry_words {K : TCombCfg} {C : Curve} {base : Addr} {size k i : Nat}
    (hL : TCombLay K size) {s t : State} (h : TEntryPost K C base size k i s t)
    {x : Nat} (hx : x∈jacCombLive K) : wordsVal t.mem base x K.M.n=wordsVal s.mem base x K.M.n := by
  have hn := h.scr.nowrap
  have hsize : x+8*K.M.n≤size := hL.comb.lay.le x (jacCombLive_slots hx)
  apply h.unch.wordsVal _ (by omega)
  intro w hw
  rcases List.mem_append.mp hx with hx | hx
  · exact combW_ro hL.comb hx w (entryW_sub w hw)
  · have hnd := hL.comb.nodup
    dsimp only [TCombCfg.toComb] at hnd
    simp only [combWs,rcbW,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,
      List.not_mem_nil,or_false,not_or] at hnd
    have hxs : x∈combWs K.toComb := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl <;> tcomb_mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
    · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
    · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
    · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
    · exact hL.comb.lay.tmp x (combWs_slots _ x hxs)

/-- The entry's mathematical postcondition, with no continuation. -/
theorem jacComb_entry_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k i : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hV : TCombVals K C tbl) (hpn : C.p<2^(64*K.M.n)) {s : State}
    (hs : Scr s base size) (hm : ModOkA K.M size C.p s.mem base) (hi : i<K.J)
    (hx : s.gpr .x19=BitVec.ofNat 64 i)
    (hd : s.gpr .x2=BitVec.ofNat 64 (magH K.H (combWin K.w k i)))
    (hb : ∀ q<K.w*K.J,s.mem (off base (K.bits+q))=if k.testBit q then 1 else 0)
    (hz : wordsVal s.mem base K.zero K.M.n=0) (hT : s.syms K.tsym=T)
    (ht : TblMem s T (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl))
    (hout : ∀ q<(tcombWords K.M.n (2^(64*K.M.n)) C.p tbl).length,∀ b<8,
      size≤ofs base (T+BitVec.ofNat 64 (8*q)+BitVec.ofNat 64 b)) :
    WP isa (.seq (.block K.selectPublic) (.block (negYW K.M K.w K.neg K.zero K.E.y K.bits))) s
      (TEntryPost K C base size k i s) := by
  have he := tentry_after_digit_ok (publicLookup:=true) hL hA hC hV hpn hs hm hi hx hd hb hz hT ht hout
    (rest:=.block []) (fun _ h => (WP.block_nil_iff).mpr h)
  exact WP.seq (WP.mono he fun _ h => WP.mono (WP.seq_iff.mp h) fun _ h => WP.block_nil_iff.mp h)

structure CombEntryPre (K : TCombCfg) (C : Curve) (base T : Addr) (size k i : Nat)
    (ws : List (BitVec 64)) (s : State) : Prop where
  index : s.gpr .x19=BitVec.ofNat 64 i
  digit : s.gpr .x2=BitVec.ofNat 64 (magH K.H (combWin K.w k i))
  bits : ∀ q<K.w*K.J,s.mem (off base (K.bits+q))=if k.testBit q then 1 else 0
  zero : wordsVal s.mem base K.zero K.M.n=0
  symbol : s.syms K.tsym=T
  table : TblMem s T ws

/-- The selected affine entry supplies a common field environment. -/
theorem jacComb_entry_relCT {K : TCombCfg} {C : Curve} {base T : Addr} {size k i : Nat}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hV : TCombVals K C tbl) (hpn : C.p<2^(64*K.M.n)) (hc : JacCombChecks K)
    (hi : i<K.J) (hmag : 1≤magH K.H (combWin K.w k i))
    (hout : ∀ q<(tcombWords K.M.n (2^(64*K.M.n)) C.p tbl).length,∀ b<8,
      size≤ofs base (T+BitVec.ofNat 64 (8*q)+BitVec.ofNat 64 b)) {E : Nat → Fe C} :
    RelCT isa (fun s t =>
      FieldPair K.M base size C.p (·∈combSlots K.toComb) (jacCombLive K) E s t ∧
      CombEntryPre K C base T size k i (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl) s ∧
      CombEntryPre K C base T size k i (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl) t)
      (.block (K.selectPublic++negYW K.M K.w K.neg K.zero K.E.y K.bits))
      (fun s t => ∃ E',FieldPair K.M base size C.p (·∈combSlots K.toComb)
        ([K.E.x,K.E.y,K.E.z]++jacCombLive K) E' s t) := by
  apply RelCT.block_append
  have he := (jacComb_entry_ct (k:=k) (i:=i) (base:=base) (T:=T) hL hc).mono
    (P':=fun s t => FieldPair K.M base size C.p (·∈combSlots K.toComb) (jacCombLive K) E s t ∧
      CombEntryPre K C base T size k i (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl) s ∧
      CombEntryPre K C base T size k i (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl) t)
    (fun _ _ ⟨p,a,b⟩ => ⟨p.left.scr,p.right.scr,p.sp,a.index,b.index,a.symbol,b.symbol,a.digit,b.digit⟩)
    (fun _ _ h => h)
  have hw := he.wpDep (F:=TEntryPost K C base size k i) (fun s t ⟨p,a,b⟩ =>
    ⟨jacComb_entry_ok hL hA hC hV hpn p.left.scr p.left.mod hi a.index a.digit a.bits a.zero a.symbol a.table hout,
     jacComb_entry_ok hL hA hC hV hpn p.right.scr p.right.mod hi b.index b.digit b.bits b.zero b.symbol b.table hout⟩)
  refine hw.mono (fun _ _ h => h) ?_
  intro s t ⟨_,a,b,⟨p,_,_⟩,hs,ht⟩
  have modS := p.left.mod.unch hs.unch
    (fun w hw => combW_mo hL.comb p.left.mod w (entryW_sub w hw)) hs.scr.nowrap
  have modT := p.right.mod.unch ht.unch
    (fun w hw => combW_mo hL.comb p.right.mod w (entryW_sub w hw)) ht.scr.nowrap
  have zs : tmv C K.M.n base s K.E.z=1 := by
    change toM _ _ _=1; rw [hs.z,ite_eq_left hmag,hV.one]
  have zt : tmv C K.M.n base t K.E.z=1 := by
    change toM _ _ _=1; rw [ht.z,ite_eq_left hmag,hV.one]
  have xy := rep_one_unique hC (zs ▸ hs.rep) (zt ▸ ht.rep)
  have same : ∀ x∈[K.E.x,K.E.y,K.E.z]++jacCombLive K,
      tmv C K.M.n base s x=tmv C K.M.n base t x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact xy.1
      · exact xy.2
      · exact zs.trans zt.symm
    · change toM _ _ _=toM _ _ _
      rw [jacComb_entry_words hL hs hx,jacComb_entry_words hL ht hx]
      exact (p.left.val x hx).trans (p.right.val x hx).symm
  have slots : ∀ x∈[K.E.x,K.E.y,K.E.z]++jacCombLive K,x∈combSlots K.toComb := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl <;> tcomb_mem
    · exact jacCombLive_slots hx
  refine ⟨tmv C K.M.n base s,⟨hs.scr,modS,slots,?_,fun _ _ => rfl⟩,
    ⟨ht.scr,modT,slots,?_,fun x hx => (same x hx).symm⟩,
    hs.keep.sp.trans (p.sp.trans ht.keep.sp.symm)⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hs.lt x hx
    · rw [jacComb_entry_words hL hs hx]; exact p.left.lt x hx
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ht.lt x hx
    · rw [jacComb_entry_words hL ht hx]; exact p.right.lt x hx

/-- The correctness invariant supplies all live canonical field slots. -/
theorem JacCombInv.field {K : TCombCfg} {C : Curve} {base T : Addr} {size k j : Nat}
    {ws : List (BitVec 64)} (hL : TCombLay K size) {s₀ s : State}
    (hf : TCombFixed K C base size s₀ k T ws) (hi : JacCombInv K C base size k T ws s₀ s j) :
    Inv K.M base size C.p (·∈combSlots K.toComb) (jacCombLive K) (tmv C K.M.n base s) s := by
  refine ⟨hi.scr,hi.mod,fun _ hx => jacCombLive_slots hx,?_,fun _ _ => rfl⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · have hb : x+8*K.M.n≤size := hL.comb.lay.le x (combRo_slots x hx)
    rw [hi.unch.wordsVal (tcombW_ro hL hx) (by have := hi.scr.nowrap; omega)]
    exact hf.ro_lt x hx
  · exact hi.lt x hx

/-- Public field equality implies the shared comb relation. -/
theorem FieldPair.combShared {K : TCombCfg} {C : Curve} {base : Addr} {size : Nat}
    {E : Nat → Fe C} {s t : State}
    (h : FieldPair K.M base size C.p (·∈combSlots K.toComb) (jacCombLive K) E s t) :
    CombShared K C base s t := fun x hx => (h.left.val x hx).trans (h.right.val x hx).symm

/-- A digit read changes no field values. -/
theorem Inv.of_keeps_mem {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {s t : State} {rs : List Reg}
    (h : Inv M base size m Sl V E s) (hk : Keeps rs s t) (h0 : Reg.x0∉rs) :
    Inv M base size m Sl V E t := by
  refine ⟨h.scr.of_keeps hk h0,?_,h.sl,?_,?_⟩
  · rw [hk.mem]; exact h.mod
  · rw [hk.mem]; exact h.lt
  · rw [hk.mem]; exact h.val

/-- One zero-skipping iteration preserves the public accumulator. -/
theorem jacComb_step_relCT {K : TCombCfg} {C : Curve} {base T : Addr} {size k j : Nat}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hV : TCombVals K C tbl) (hpn : C.p<2^(64*K.M.n)) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hn : K.M.n=4) (hc : JacCombChecks K) (hj : 1≤j) (hjn : j≤K.J) {s₀ t₀ : State}
    (hfs : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl))
    (hft : TCombFixed K C base size t₀ k T (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl)) :
    RelCT isa (fun s t =>
      JacCombInv K C base size k T (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl) s₀ s j ∧
      JacCombInv K C base size k T (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl) t₀ t j ∧
      s.sp=t.sp ∧ CombShared K C base s t) (Jacobian.jacCombStep K) (CombShared K C base) := by
  let Pre := fun s t =>
    JacCombInv K C base size k T (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl) s₀ s j ∧
    JacCombInv K C base size k T (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl) t₀ t j ∧
    s.sp=t.sp ∧ CombShared K C base s t
  let Entry := CombEntryPre K C base T size k (j-1) (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl)
  let Pair := fun s t => ∃ E, FieldPair K.M base size C.p (·∈combSlots K.toComb) (jacCombLive K) E s t ∧ Entry s ∧ Entry t
  have hd : RelCT isa Pre (.block (decCounter::K.digit)) (fun _ _ => True) := by
    intro s t ts tt s' t' ⟨a,b,sp,_⟩ es et
    refine ⟨hc.digit _ _ _ _ _ _ trivial trivial ⟨sp,?_⟩ es et,trivial⟩
    intro r hr
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact a.scr.x0.trans b.scr.x0.symm
    · exact a.x19.trans b.x19.symm
  have hdw := hd.wpDep (F:=fun (s t : State) =>
      Keeps [.x19,.x2,.x3,.x4,.x9,.x16] s t ∧ t.syms=s.syms ∧
      t.gpr .x19=BitVec.ofNat 64 (j-1) ∧ t.gpr .x2=BitVec.ofNat 64 (magH K.H (combWin K.w k (j-1))))
    (fun s t ⟨a,b,_,_⟩ => ⟨jacComb_digit_ok hL a.scr hj hjn a.x19 a.bits,
      jacComb_digit_ok hL b.scr hj hjn b.x19 b.bits⟩)
  have hd' : RelCT isa Pre (.block (decCounter::K.digit)) Pair := hdw.mono (fun _ _ h => h) (by
    intro s t ⟨_,a,b,⟨ia,ib,sp,same⟩,⟨ka,sa,xa,ma⟩,⟨kb,sb,xb,mb⟩⟩
    have fa := (ia.field hL hfs).of_keeps_mem ka (by decide)
    have fb := ((ib.field hL hft).congr_env (fun x hx => (same x hx).symm)).of_keeps_mem kb (by decide)
    refine ⟨_,⟨fa,fb,ka.sp.trans (sp.trans kb.sp.symm)⟩,?_,?_⟩
    · refine ⟨xa,ma,fun q hq => by rw [ka.mem]; exact ia.bits q hq,?_,by rw [sa]; exact ia.tsym,?_⟩
      · have hb : K.zero+8*K.M.n≤size := hL.comb.lay.le _ (by tcomb_mem)
        rw [ka.mem,ia.unch.wordsVal (tcombW_ro hL (by simp [combRo,TCombCfg.toComb]))
          (by have := ia.scr.nowrap; omega),hfs.zero]
      · exact ia.tbl.unch (by rw [ka.rd,ka.wr]) (fun _ _ _ _ => by rw [ka.mem])
    · refine ⟨xb,mb,fun q hq => by rw [kb.mem]; exact ib.bits q hq,?_,by rw [sb]; exact ib.tsym,?_⟩
      · have hb : K.zero+8*K.M.n≤size := hL.comb.lay.le _ (by tcomb_mem)
        rw [kb.mem,ib.unch.wordsVal (tcombW_ro hL (by simp [combRo,TCombCfg.toComb]))
          (by have := ib.scr.nowrap; omega),hft.zero]
      · exact ib.tbl.unch (by rw [kb.rd,kb.wr]) (fun _ _ _ _ => by rw [kb.mem]))
  unfold Jacobian.jacCombStep
  apply hd'.seq
  apply RelCT.ite
  · intro s t ⟨_,_,a,b⟩
    simp only [eval,State.read,a.digit,b.digit]
  · intro s t ts tt s' t' ⟨⟨E,p,a,b⟩,hb⟩ es et
    have hmag : 1≤magH K.H (combWin K.w k (j-1)) := by
      by_contra h
      have hz : magH K.H (combWin K.w k (j-1))=0 := by omega
      simp only [eval,State.read,a.digit,hz] at hb
      cases hb
    have he := jacComb_entry_relCT (E:=E) hL hA hC hV hpn hc (by omega) hmag hfs.out
    have hsum := RelCT.exists_ (fun E' => jacComb_sum_relCT (base:=base) (E:=E') hL hA hm hn hV.one_lt hc)
    have hall := he.seq hsum
    obtain ⟨htrace,_,hp⟩ := hall _ _ _ _ _ _ ⟨p,a,b⟩ es et
    exact ⟨htrace,hp.combShared⟩
  · exact RelCT.block_nil (fun _ _ ⟨⟨_,p,_,_⟩,_⟩ => p.combShared)

/-- Relate every public comb iteration and retain the final field values. -/
theorem jacComb_countLoop_relCT {K : TCombCfg} {C : Curve} {base T : Addr} {size k : Nat}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hG : onCurve C (G C)=true) (hV : TCombVals K C tbl) (hpn : C.p<2^(64*K.M.n))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hn : K.M.n=4) (hc : JacCombChecks K)
    (hSum : JacCombSumCorrect K C base size) {s₀ t₀ : State} (hsp : s₀.sp=t₀.sp)
    (hfs : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl))
    (hft : TCombFixed K C base size t₀ k T (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl)) :
    RelCT isa (fun s t =>
      JacCombInv K C base size k T (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl) s₀ s K.J ∧
      JacCombInv K C base size k T (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl) t₀ t K.J ∧
      CombShared K C base s t)
      (.loop (Jacobian.jacCombStep K) (.nonzero .x .x19))
      (fun s t => ∃ E,FieldPair K.M base size C.p (·∈combSlots K.toComb) (jacCombLive K) E s t ∧ E K.zero=0) := by
  let I := fun j s t => 1≤j ∧ j≤K.J ∧
    JacCombInv K C base size k T (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl) s₀ s j ∧
    JacCombInv K C base size k T (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl) t₀ t j ∧ CombShared K C base s t
  have step : ∀ j,RelCT isa (I j) (Jacobian.jacCombStep K) (fun s t =>
      eval (.nonzero .x .x19) s=eval (.nonzero .x .x19) t ∧
      (eval (.nonzero .x .x19) s=some false → ∃ E,FieldPair K.M base size C.p (·∈combSlots K.toComb) (jacCombLive K) E s t ∧ E K.zero=0) ∧
      (eval (.nonzero .x .x19) s=some true → ∃ m<j,I m s t)) := by
    intro j
    by_cases hj : 1≤j
    · by_cases hjn : j≤K.J
      · have hs := (jacComb_step_relCT hL hA hC hV hpn hm hn hc hj hjn hfs hft).mono
          (P':=I j) (fun _ _ ⟨_,_,a,b,same⟩ => ⟨a,b,a.keep.sp.trans (hsp.trans b.keep.sp.symm),same⟩)
          (fun _ _ h => h)
        have hw := hs.wp (fun _ _ ⟨_,_,a,b,_⟩ =>
          ⟨jacComb_step_ok hL hA hC hG hV hpn hSum hfs hj hjn a,
           jacComb_step_ok hL hA hC hG hV hpn hSum hft hj hjn b⟩)
        refine hw.mono (fun _ _ h => h) ?_
        intro s t ⟨same,⟨a,xa⟩,⟨b,xb⟩⟩
        refine ⟨by simp only [eval,State.read,xa,xb],fun _ => ?_,fun he => ?_⟩
        · refine ⟨_,⟨a.field hL hfs,(b.field hL hft).congr_env (fun x hx => (same x hx).symm),
            a.keep.sp.trans (hsp.trans b.keep.sp.symm)⟩,?_⟩
          have hb : K.zero+8*K.M.n≤size := hL.comb.lay.le _ (by tcomb_mem)
          change toM _ _ _=0
          rw [a.unch.wordsVal (tcombW_ro hL (by simp [combRo,TCombCfg.toComb]))
            (by have := a.scr.nowrap; omega),hfs.zero,toM_zero]
        · have hz : j-1≠0 := by
            intro hz; simp only [eval,State.read,xa,hz] at he; cases he
          exact ⟨j-1,by omega,by omega,by omega,a,b,same⟩
      · exact RelCT.of_false (fun _ _ h => hjn h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  exact (RelCT.loop I step K.J).mono (fun _ _ ⟨a,b,same⟩ =>
    ⟨by simpa only [TCombCfg.toComb_J] using hL.comb.J.1,Nat.le_refl _,a,b,same⟩) (fun _ _ h => h)

/-- Initialization fixes the accumulator and constants independently of scratch. -/
theorem jacComb_init_shared {K : TCombCfg} {C : Curve} {base T : Addr} {size k : Nat}
    {ws : List (BitVec 64)} (hL : TCombLay K size) {s₀ t₀ s t : State}
    (hfs : TCombFixed K C base size s₀ k T ws) (hft : TCombFixed K C base size t₀ k T ws)
    (hs : JacCombInv K C base size k T ws s₀ s K.J)
    (ht : JacCombInv K C base size k T ws t₀ t K.J)
    (sx : wordsVal s.mem base K.A.x K.M.n=K.start.1)
    (sy : wordsVal s.mem base K.A.y K.M.n=K.start.2)
    (sz : wordsVal s.mem base K.A.z K.M.n=K.one)
    (tx : wordsVal t.mem base K.A.x K.M.n=K.start.1)
    (ty : wordsVal t.mem base K.A.y K.M.n=K.start.2)
    (tz : wordsVal t.mem base K.A.z K.M.n=K.one) : CombShared K C base s t := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · have hb : x+8*K.M.n≤size := hL.comb.lay.le x (combRo_slots x hx)
    change toM _ _ _=toM _ _ _
    rw [hs.unch.wordsVal (tcombW_ro hL hx) (by have := hs.scr.nowrap; omega),
      ht.unch.wordsVal (tcombW_ro hL hx) (by have := ht.scr.nowrap; omega)]
    simp only [combRo,TCombCfg.toComb,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hfs.a.trans hft.a.symm
    · exact hfs.b.trans hft.b.symm
    · rw [hfs.zero,hft.zero]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    change toM _ _ _=toM _ _ _
    rcases hx with rfl | rfl | rfl
    · rw [sx,tx]
    · rw [sy,ty]
    · rw [sz,tz]

/-- The initialized public comb loop, including zero digits and exceptional sums. -/
theorem jacCombLoop_relCT {K : TCombCfg} {C : Curve} {base T : Addr} {size k : Nat}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hG : onCurve C (G C)=true) (hV : TCombVals K C tbl) (hpn : C.p<2^(64*K.M.n))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hn : K.M.n=4) (hc : JacCombChecks K)
    (hSum : JacCombSumCorrect K C base size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ s.sp=t.sp ∧
      ModOkA K.M size C.p s.mem base ∧ ModOkA K.M size C.p t.mem base ∧
      TCombFixed K C base size s k T (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl) ∧
      TCombFixed K C base size t k T (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl))
      (Jacobian.jacCombLoop K)
      (fun s t => ∃ E,FieldPair K.M base size C.p (·∈combSlots K.toComb) (jacCombLive K) E s t ∧ E K.zero=0) := by
  intro s t ts tt s' t' ⟨hs,ht,sp,ms,mt,fs,ft⟩ es et
  obtain ⟨_,a,ea,ia,ax,ay,az⟩ := jacComb_init_values_ok hL hA hV hpn hs ms fs
  obtain ⟨_,b,eb,ib,bx,byv,bz⟩ := jacComb_init_values_ok hL hA hV hpn ht mt ft
  cases es with
  | seq es1 es2 =>
    cases et with
    | seq et1 et2 =>
      obtain ⟨_,rfl⟩ := Exec.det es1 ea
      obtain ⟨_,rfl⟩ := Exec.det et1 eb
      have hi := hc.init _ _ _ _ _ _ trivial trivial ⟨sp,fun r hr => by
        simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
        subst hr; exact hs.x0.trans ht.x0.symm⟩ es1 et1
      have same := jacComb_init_shared hL fs ft ia ib ax ay az bx byv bz
      obtain ⟨hl,post⟩ := jacComb_countLoop_relCT hL hA hC hG hV hpn hm hn hc hSum sp fs ft
        _ _ _ _ _ _ ⟨ia,ib,same⟩ es2 et2
      exact ⟨by rw [hi,hl],post⟩

/-- Full Jacobian comb timing, including conversion to homogeneous coordinates. -/
theorem jacComb_relCT {K : TCombCfg} {C : Curve} {base T : Addr} {size k : Nat}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hG : onCurve C (G C)=true) (hV : TCombVals K C tbl) (hpn : C.p<2^(64*K.M.n))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hn : K.M.n=4) (hc : JacCombChecks K)
    (hSum : JacCombSumCorrect K C base size) (hfinish : FieldCT (Jacobian.jacCombFinish K)) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ s.sp=t.sp ∧
      ModOkA K.M size C.p s.mem base ∧ ModOkA K.M size C.p t.mem base ∧
      TCombFixed K C base size s k T (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl) ∧
      TCombFixed K C base size t k T (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl))
      (Jacobian.jacComb K)
      (fun s t => ∃ E,FieldPair K.M base size C.p (·∈combSlots K.toComb) (jacCombLive K) E s t) := by
  apply (jacCombLoop_relCT hL hA hC hG hV hpn hm hn hc hSum).seq
  intro s t ts tt s' t' ⟨E,p,hz⟩ es et
  exact jacCombFinish_relCT hL.comb hA hC hm hn hV.one_lt hV.one hpn hfinish hz _ _ _ _ _ _ p es et

end VG.Proof.Weierstrass.AArch64
