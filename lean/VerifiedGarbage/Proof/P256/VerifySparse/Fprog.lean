module

public import VerifiedGarbage.Impl.P256.VerifySparse
public import VerifiedGarbage.Proof.Mont.AArch64.Ops
public import VerifiedGarbage.Proof.P256.VerifySparse.Arithmetic
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
public import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Core
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Mont.AArch64.Row
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `P256.VerifySparse.Correct`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.VerifySparse
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Proof.Ed25519

private theorem first_value (a : BitVec 64) :
    (Word64.addCarry a 1 false).toNat+(2^64-1)=
      a.toNat+2^64*(!Word64.carryOut a 1 false).toNat := by
  have h := Word64.addCarry_value a 1 false
  cases hc : Word64.carryOut a 1 false <;>
    simp only [hc,Bool.not_false,Bool.not_true,Bool.toNat_true,Bool.toNat_false,
      show (1 : BitVec 64).toNat=1 from rfl] at h ⊢ <;> omega_arith

private theorem first_ok (s : State) (r : Reg) (hr : r≠.x2) :
    WP isa (.block [.movz .x .x2 1 0,.adds .x .x1 r .x2]) s fun t =>
      (t.gpr .x1).toNat+(2^64-1)=(s.gpr r).toNat+2^64*(!t.c).toNat ∧
      Keeps [.x1,.x2] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    show 16*0<64 by decide,ite_true,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,
    RegUpd.c_addWithCarry,BitVec.setWidth_eq,hr,ite_false,reduceCtorEq,
    Option.some.injEq,exists_eq_left']
  refine ⟨first_value _,fun q hq => ?_,rfl,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
  simp only [RegUpd.gpr_write,RegUpd.gpr_addWithCarry,hq.1,hq.2,ite_false]

private def diffs (a b c d : Reg) : List Instr :=
  [.movz .x .x2 1 0,.adds .x .x1 a .x2,
   ld .x2 (Impl.P256.VerifySparse.M.mo+8),.sbcs .x .x3 b .x2,
   .sbcs .x .x4 c .x7,ld .x2 (Impl.P256.VerifySparse.M.mo+24),.sbcs .x .x5 d .x2]

private theorem diffs_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (a b c d : Reg) (hf : Fresh [a,b,c,d])
    (hmo : Impl.P256.VerifySparse.M.mo+32≤size) (hz : s.gpr .x7=0)
    (h0 : word s.mem base Impl.P256.VerifySparse.M.mo = -1)
    (h2 : word s.mem base (Impl.P256.VerifySparse.M.mo+16)=0) :
    WP isa (.block (diffs a b c d)) s fun t =>
      regsVal t (dRegs 4)+wordsVal s.mem base Impl.P256.VerifySparse.M.mo 4=
        regsVal s [a,b,c,d]+2^256*(!t.c).toNat ∧ Keeps [.x1,.x2,.x3,.x4,.x5] s t := by
  have na := hf.2 a (by simp)
  have nb := hf.2 b (by simp)
  have nc := hf.2 c (by simp)
  have nd := hf.2 d (by simp)
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at na nb nc nd
  change WP isa (.block (([.movz .x .x2 1 0,.adds .x .x1 a .x2] : List Instr)++
    ([ld .x2 (Impl.P256.VerifySparse.M.mo+8),.sbcs .x .x3 b .x2] : List Instr)++
    ([.sbcs .x .x4 c .x7] : List Instr)++
    ([ld .x2 (Impl.P256.VerifySparse.M.mo+24),.sbcs .x .x5 d .x2] : List Instr))) s _
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (first_ok s a na.2.2.1) fun s1 ⟨e1,k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (diffR1_ok (hs.of_keeps k1 (by decide)) b .x3 nb.2.2.1 false
    (c:=s1.c) rfl (mo:=Impl.P256.VerifySparse.M.mo+8) (by omega_arith) (by decide)) fun s2 ⟨e2,k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subc_ok s2 .x4 c .x7 false (c:=s2.c) rfl) fun s3 ⟨v3,c3,k3⟩ => ?_
  have z2 : s2.gpr .x7=0 := by rw [k2.gpr _ (by decide),k1.gpr _ (by decide),hz]
  have e3 := sub_borrow (s2.gpr c) (s2.gpr .x7) s2.c
  rw [←v3,←c3,z2] at e3
  have hs3 := ((hs.of_keeps k1 (by decide)).of_keeps k2 (by decide)).of_keeps k3 (by decide)
  refine WP.mono (diffR1_ok hs3 d .x5 nd.2.2.1 false (c:=s3.c) rfl
    (mo:=Impl.P256.VerifySparse.M.mo+24) (by omega_arith) (by decide)) fun t ⟨e4,k4⟩ => ?_
  refine ⟨?_,(((k1.mono (by sub_regs)).trans (k2.mono (by sub_regs))).trans
    (k3.mono (by sub_regs))).trans (k4.mono (by sub_regs))⟩
  have ea : t.gpr .x1=s1.gpr .x1 := by rw [k4.gpr _ (by decide),k3.gpr _ (by decide),k2.gpr _ (by decide)]
  have eb : t.gpr .x3=s2.gpr .x3 := by rw [k4.gpr _ (by decide),k3.gpr _ (by decide)]
  have ec : t.gpr .x4=s3.gpr .x4 := k4.gpr _ (by decide)
  have rb : s1.gpr b=s.gpr b := k1.gpr b (by simp [nb.2.1,nb.2.2.1])
  have rc : s2.gpr c=s.gpr c := by rw [k2.gpr c (by simp [nc.2.2.1,nc.2.2.2.1]),k1.gpr c (by simp [nc.2.1,nc.2.2.1])]
  have rd : s3.gpr d=s.gpr d := by
    rw [k3.gpr d (by simp [nd.2.2.2.2.1]),k2.gpr d (by simp [nd.2.2.1,nd.2.2.2.1]),
      k1.gpr d (by simp [nd.2.1,nd.2.2.1])]
  rw [rb,k1.mem] at e2
  rw [rc] at e3
  change (s3.gpr .x4).toNat+0+(!s2.c).toNat=(s.gpr c).toNat+2^64*(!s3.c).toNat at e3
  rw [rd,k3.mem,k2.mem,k1.mem] at e4
  simp only [dRegs,List.take,regsVal,wordsVal,ea,eb,ec,Nat.mul_zero,Nat.add_zero]
  rw [h0,show Impl.P256.VerifySparse.M.mo+8+8=Impl.P256.VerifySparse.M.mo+16 by omega_arith,h2,
    show Impl.P256.VerifySparse.M.mo+16+8=Impl.P256.VerifySparse.M.mo+24 by omega_arith]
  change (s1.gpr .x1).toNat+2^64*((s2.gpr .x3).toNat+2^64*((s3.gpr .x4).toNat+2^64*(t.gpr .x5).toNat))+
    ((2^64-1)+2^64*((word s.mem base (Impl.P256.VerifySparse.M.mo+8)).toNat+
      2^64*(0+2^64*(word s.mem base (Impl.P256.VerifySparse.M.mo+24)).toNat)))=_
  omega_arith


/-- Sparse conditional subtraction has the ordinary canonical csub contract. -/
theorem correct_ok {s : State} {base : Addr} {size m : Nat} (hs : Scr s base size)
    {ts : List Reg} {top : Reg} (hlen : ts.length=4) (hf : Fresh (top::ts))
    (hmo : Impl.P256.VerifySparse.M.mo+32≤size) (hz : s.gpr .x7=0)
    (h0 : word s.mem base Impl.P256.VerifySparse.M.mo = -1)
    (h2 : word s.mem base (Impl.P256.VerifySparse.M.mo+16)=0)
    (hm : wordsVal s.mem base Impl.P256.VerifySparse.M.mo 4=m)
    (hV : regsVal s ts+2^256*(s.gpr top).toNat<2*m) :
    WP isa (.block (Impl.P256.VerifySparse.correct ts top)) s fun t =>
      regsVal t ts=(regsVal s ts+2^256*(s.gpr top).toNat)%m ∧
      Keeps (.x2::.x17::ts++dRegs 4) s t := by
  rcases ts with _ | ⟨a,ts⟩ <;> simp only [List.length_nil,List.length_cons] at hlen
  · omega_arith
  rcases ts with _ | ⟨b,ts⟩ <;> simp only [List.length_nil,List.length_cons] at hlen
  · omega_arith
  rcases ts with _ | ⟨c,ts⟩ <;> simp only [List.length_nil,List.length_cons] at hlen
  · omega_arith
  rcases ts with _ | ⟨d,ts⟩ <;> simp only [List.length_nil,List.length_cons] at hlen
  · omega_arith
  have ht : ts=[] := by
    cases ts with
    | nil => rfl
    | cons e es => simp only [List.length_cons] at hlen; omega_arith
  subst ts
  have ft := hf.tail
  have ne : ∀ q∈top::[a,b,c,d],q∉[Reg.x1,.x2,.x3,.x4,.x5] := by
    intro q hq hn
    have h := hf.2 q hq
    apply h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn ⊢
    grind
  have nt : top∉[Reg.x1,.x2,.x3,.x4,.x5] := ne top (by simp)
  have nn : ∀q∈[a,b,c,d],q∉[Reg.x2] := by
    intro q hq hn
    exact ne q (by simp [hq]) (by simp only [List.mem_singleton] at hn; simp [hn])
  have code : Impl.P256.VerifySparse.correct [a,b,c,d] top=
      diffs a b c d ++ ([.sbcs .x .x2 top .x7] : List Instr) ++ selectsR [a,b,c,d] (dRegs 4) := by
    simp only [Impl.P256.VerifySparse.correct,diffs,List.getElem!_cons_zero,List.getElem!_cons_succ,
      List.cons_append,List.nil_append]
  rw [code,List.append_assoc,WP.block_append_iff]
  refine WP.mono (diffs_ok hs a b c d ft hmo hz h0 h2) fun s1 ⟨e1,k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (flagR_ok s1 top (by rw [k1.gpr _ (by decide),hz])) fun s2 ⟨flag,k2⟩ => ?_
  have te : s1.gpr top=s.gpr top := k1.gpr _ nt
  rw [te] at flag
  refine WP.mono (selectsR_ok [a,b,c,d] (dRegs 4)
    (decide ((s.gpr top).toNat<(!s1.c).toNat)) rfl ft (dRegs_ok 4 (by decide)).1 flag)
    fun t ⟨et,kt,_⟩ => ?_
  have er : regsVal s2 [a,b,c,d]=regsVal s [a,b,c,d] := by
    exact (regsVal_congr (fun q hq => k2.gpr q (nn q hq))).trans
      (regsVal_congr fun q hq => k1.gpr q (ne q (List.mem_cons_of_mem _ hq)))
  have ed : regsVal s2 (dRegs 4)=regsVal s1 (dRegs 4) :=
    regsVal_congr fun q hq => k2.gpr q (by revert q; decide)
  change Keeps [.x1,.x2,.x3,.x4,.x5] s s1 at k1
  refine ⟨?_,((k1.mono (by unfold dRegs; simp only [List.take]; sub_regs)).trans (k2.mono (by sub_regs))).trans
    (kt.mono (by sub_regs))⟩
  rw [et,er,ed]
  simp only [decide_eq_true_eq]
  rw [hm] at e1
  have ml : m<2^256 := hm ▸ wordsVal_lt s.mem base Impl.P256.VerifySparse.M.mo 4
  have dl : regsVal s1 (dRegs 4)<2^256 := regsVal_lt s1 (dRegs 4)
  exact csub_arith (b:=!s1.c) ml dl hV e1

theorem modulus_words {mem : Mem} {base : Addr} {mo : Nat}
    (hm : wordsVal mem base mo 4=p) :
    word mem base mo = -1 ∧ word mem base (mo+16)=0 := by
  have h0 := (word mem base mo).isLt
  have h1 := (word mem base (mo+8)).isLt
  have h2 := (word mem base (mo+16)).isLt
  have h3 := (word mem base (mo+24)).isLt
  simp only [wordsVal,Nat.mul_zero,Nat.add_zero] at hm
  have e8 : mo+8+8=mo+16 := by omega_arith
  have e16 : mo+8+8+8=mo+24 := by omega_arith
  rw [e16,e8] at hm
  unfold p at hm
  constructor
  · apply BitVec.eq_of_toNat_eq
    change (word mem base mo).toNat=2^64-1
    omega_arith
  · apply BitVec.eq_of_toNat_eq
    change (word mem base (mo+16)).toNat=0
    omega_arith

/-- Fixed P-256 modulus wrapper with the generic csub premise order. -/
theorem correctP_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {M : Mod} (hM : M=Impl.P256.VerifySparse.M)
    {ts : List Reg} {top : Reg} (hlen : ts.length=M.n)
    (_hn : 0<M.n) (_h10 : M.n<10) (hf : Fresh (top::ts))
    (hmo : M.mo+8*M.n≤size) (_hmo8 : M.mo%8=0) (hz : s.gpr .x7=0)
    (hm : wordsVal s.mem base M.mo M.n=p)
    (hV : regsVal s ts+2^(64*M.n)*(s.gpr top).toNat<2*p) :
    WP isa (.block (Impl.P256.VerifySparse.correct ts top)) s fun t =>
      regsVal t ts=(regsVal s ts+2^(64*M.n)*(s.gpr top).toNat)%p ∧
      Keeps (.x2::.x17::ts++dRegs M.n) s t := by
  subst M
  exact correct_ok hs hlen hf hmo hz (modulus_words hm).1 (modulus_words hm).2 hm hV

end VG.Proof.P256.VerifySparse

end

end

/-! ### `P256.VerifySparse.Code`, which only this module used -/

section

/-! ### `P256.VerifySparse.Ops`, which only this module used -/

section

/-! The existing Montgomery setup/round and addition-chain proofs are reused here.
Only their final conditional subtraction is replaced with the sparse P-256 proof. -/

@[expose] public section

namespace VG.Proof.P256.VerifySparse
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

def sparseMul (M : Mod) (o a b : Nat) : List Instr :=
  mulSetup M .x0 b ++ ((List.range M.n).flatMap (round M .x0 .x0 a b) ++
    (Impl.P256.VerifySparse.correct ((List.range M.n).map (win M.n M.n)) (win M.n M.n M.n) ++
      stores ((List.range M.n).map (win M.n M.n)) o))

def sparseAdd (M : Mod) (o a b : Nat) : List Instr :=
  zero7 :: loads (low M.n) a ++ chain (.adds .x) (.adcs .x) (low M.n) b ++
    [.adc .x (top M.n) .x7 .x7] ++ Impl.P256.VerifySparse.correct (low M.n) (top M.n) ++ stores (low M.n) o

theorem mul_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} (hME : M=Impl.P256.VerifySparse.M)
    (hM : ModOkW M size p s.mem base) (h10 : M.n < 10) (hA : ModA M) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb8 : b % 8 = 0) (hB : wordsVal s.mem base b M.n < p) :
    WP isa (.block (sparseMul M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < p ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % p =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % p := by
  have h7 := h10
  rw [sparseMul, WP.block_append_iff]
  refine WP.mono (setup_ok h7 hs.ptr (ptrOk_x0 h7) hb hb8) fun s₁ ⟨z₁, hBR₁, h6₁, h0, k₁⟩ => ?_
  obtain hacc := acc_regs_lt _ h7
  obtain hs₁ := hs.of_keeps k₁ (fun h => by
    simp only [List.mem_cons] at h
    rcases h with h | h | h | h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (hacc _ h) (by simp))
  have hmem₁ : s₁.mem = s.mem := k₁.mem
  rw [WP.block_append_iff]
  refine WP.mono (rounds_ok h7 (ptrOk_x0 h7) (ptrOk_x0 h7) ha hb hM.mo ha8 hb8 hA.mo hM.inv hM.red M.n
    (Nat.le_refl _) hs₁ hs₁.ptr hs₁.ptr z₁
    (by rw [hmem₁]; exact hM.val) hBR₁ h6₁ (by rw [hmem₁]; exact hB) h0)
    fun s₂ ⟨⟨U, eU⟩, hT, k₂, _⟩ => ?_
  rw [accV_of_pos M s₂ hM.n0] at eU hT
  obtain nk : ∀ r ∈ [Reg.x0, .x7], r ∉ Reg.x1 :: Reg.x2 :: Reg.x3 :: acc M.n := by
    intro r hr h
    by_cases hr' : r ∈ acc M.n
    · have := hacc _ hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr h
    rcases hr with rfl | rfl <;> simp_all
  obtain hs₂ := hs₁.of_keeps k₂ (nk .x0 (by simp))
  obtain hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr .x7 (nk .x7 (by simp)), z₁]
  obtain hmem₂ : s₂.mem = s.mem := by rw [k₂.mem, hmem₁]
  rw [hmem₁] at eU
  -- The accumulator's value as `csub` sees it: its top word is zero.
  obtain hsplit := wins_split M.n M.n
  obtain hmX : p < 2 ^ (64 * M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  obtain hlowlen : ((List.range M.n).map (win M.n M.n)).length = M.n := by simp
  obtain hV : regsVal s₂ ((List.range M.n).map (win M.n M.n)) +
      2 ^ (64 * M.n) * (s₂.gpr (win M.n M.n M.n)).toNat = regsVal s₂ (wins M.n M.n) := by
    rw [hsplit, regsVal_append, hlowlen]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    have hT' := hT
    rw [hsplit, regsVal_append, hlowlen] at hT'
    simp only [regsVal, Nat.mul_zero, Nat.add_zero] at hT'
    have : (s₂.gpr (win M.n M.n (M.n + 1))).toNat = 0 := by
      by_contra hne
      have : 2 ^ (64 * M.n) * 2 ^ 64 ≤ 2 ^ (64 * M.n) * ((s₂.gpr (win M.n M.n M.n)).toNat +
          2 ^ 64 * (s₂.gpr (win M.n M.n (M.n + 1))).toNat) :=
        Nat.mul_le_mul_left _ (by omega_arith)
      omega_arith
    rw [this, Nat.mul_zero, Nat.add_zero]
  rw [WP.block_append_iff]
  obtain hlow_acc : ∀ r ∈ (List.range M.n).map (win M.n M.n), r ∈ acc M.n := fun r hr =>
    wins_sub_acc h7 M.n r (by rw [hsplit]; exact List.mem_append_left _ hr)
  refine WP.mono (correctP_ok hs₂ (M := M) hME hlowlen hM.n0 h7 (fresh_low M.n h7) hM.mo
    hA.mo hz₂ (by rw [hmem₂]; exact hM.val) (by rw [hV]; exact hT)) fun s₃ ⟨e₃, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (fun h => x0_not_clob M.n (csubR_keep h7 hlow_acc _ h))
  refine WP.mono (stores_ok _ hs₃ (o := o) (by rw [hlowlen]; omega_arith) ho8 (fresh_low' M.n h7).1)
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [hlowlen] at e₄ O₄
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_, ?_⟩
  · obtain ⟨hr₁, hr₂⟩ := not_mem_of_clob hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr₁
    rw [k₄.gpr r (by simp), k₃.gpr r (fun h => hr (csubR_keep h7 hlow_acc r h)),
      k₂.gpr r (by simp only [List.mem_cons, not_or]; exact ⟨hr₁.1, hr₁.2.1, hr₁.2.2.1, hr₂⟩),
      k₁.gpr r (by simp only [List.mem_cons, not_or]; exact ⟨hr₁.2.2.2.1, hr₁.2.2.2.2.1,
        hr₁.2.2.2.2.2.1, hr₁.2.2.2.2.2.2.1, hr₁.2.2.2.2.2.2.2.1, hr₁.2.2.2.2.2.2.2.2, hr₂⟩)]
  · rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd]
  · rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr]
  · rw [k₄.sp, k₃.sp, k₂.sp, k₁.sp]
  · rw [O₄ x hx, k₃.mem, hmem₂]
  · rw [e₄, e₃, hV]; exact Nat.mod_lt _ (m_pos hB)
  · rw [e₄, e₃, hV, Nat.mod_mul_mod, Nat.mul_comm, eU]
    simp only [Nat.add_mul_mod_self_right]

theorem add_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} (hME : M=Impl.P256.VerifySparse.M)
    (hM : ModOkW M size p s.mem base) (h10 : M.n < 10) (hA : ModA M) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb8 : b % 8 = 0)
    (hAB : wordsVal s.mem base a M.n + wordsVal s.mem base b M.n < 2 * p) :
    WP isa (.block (sparseAdd M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + wordsVal s.mem base b M.n) % p := by
  have hn := hs.nowrap
  have h7 := h10
  obtain hf := fresh_top_low_lt M.n h7
  obtain hl := low_len_lt M.n h7
  obtain ⟨t, ts, hts⟩ := low_ne_nil h7 hM.n0
  have nf : ∀ r ∈ top M.n :: low M.n, r ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17, .x24, .x25] :=
    hf.2
  obtain hsub : ∀ r ∈ top M.n :: low M.n, r ∈ acc M.n := low_sub_acc_lt _ h7
  rw [sparseAdd, show zero7 :: loads (low M.n) a = [zero7] ++ loads (low M.n) a from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s₀ ⟨z₀, k₀⟩ => ?_
  obtain hs₀ := hs.of_keeps k₀ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok (low M.n) hs₀ (a := a) (by omega_arith) ha8 hf.tail) fun s₁ ⟨e₁, k₁, _⟩ => ?_
  obtain hs₁ := hs₀.of_keeps k₁ (fun h => nf _ (List.mem_cons_of_mem _ h) (by simp))
  obtain hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (fun h => nf _ (List.mem_cons_of_mem _ h) (by simp)), z₀]
  rw [WP.block_append_iff, hts]
  refine WP.mono (chainAdds_ok hs₁ (b := b) (by rw [← hts]; omega_arith) hb8 (hts ▸ hf.tail))
    fun s₃ ⟨e₃, k₃⟩ => ?_
  rw [← hts] at e₃ k₃ ⊢
  obtain nk₃ : ∀ r ∈ [Reg.x0, .x7], r ∉ Reg.x2 :: low M.n := by
    intro r hr h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases List.mem_cons.mp h with h | h
    · rcases hr with rfl | rfl <;> exact absurd h (by decide)
    · exact nf _ (List.mem_cons_of_mem _ h) (by rcases hr with rfl | rfl <;> simp)
  obtain hs₃ := hs₁.of_keeps k₃ (nk₃ .x0 (by simp))
  obtain hz₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr _ (nk₃ .x7 (by simp)), hz₁]
  rw [WP.block_append_iff]
  refine WP.mono (adcZero_ok s₃ (top M.n) hz₃) fun s₄ ⟨e₄, k₄⟩ => ?_
  obtain htop := nf _ (List.mem_cons_self ..)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at htop
  obtain hs₄ := hs₃.of_keeps k₄ (by simp [Ne.symm htop.1])
  obtain hz₄ : s₄.gpr .x7 = 0 := by rw [k₄.gpr _ (by simp [Ne.symm htop.2.2.2.2.2.2.2.1]), hz₃]
  obtain hR₄ : regsVal s₄ (low M.n) = regsVal s₃ (low M.n) :=
    regsVal_congr fun q hq => k₄.gpr q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => (List.nodup_cons.mp hf.1).1 (h ▸ hq))
  obtain hmem₄ : s₄.mem = s.mem := by rw [k₄.mem, k₃.mem, k₁.mem, k₀.mem]
  rw [hl, e₁, k₀.mem] at e₃
  obtain hV : regsVal s₄ (low M.n) + 2 ^ (64 * M.n) * (s₄.gpr (top M.n)).toNat =
      wordsVal s.mem base a M.n + wordsVal s.mem base b M.n := by rw [hR₄, e₄, e₃, k₁.mem, k₀.mem, hl]
  rw [WP.block_append_iff]
  obtain hlow : ∀ r ∈ low M.n, r ∈ acc M.n := fun r h => hsub r (List.mem_cons_of_mem _ h)
  refine WP.mono (correctP_ok hs₄ (M := M) hME hl hM.n0 h7 hf hM.mo hA.mo hz₄
    (by rw [hmem₄]; exact hM.val) (by rw [hV]; exact hAB)) fun s₅ ⟨e₅, k₅⟩ => ?_
  obtain hs₅ := hs₄.of_keeps k₅ (fun h => x0_not_clob M.n (csubR_keep h7 hlow _ h))
  refine WP.mono (stores_ok _ hs₅ (o := o) (by rw [hl]; omega_arith) ho8 hf.tail.1) fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  rw [hl] at e₆ O₆
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_⟩
  · obtain ⟨hr₁, hr₂⟩ := not_mem_of_clob hr
    obtain hr' : r ∉ top M.n :: low M.n := fun h => hr₂ (hsub r h)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr₁ hr'
    rw [k₆.gpr r (by simp), k₅.gpr r (fun h => hr (csubR_keep h7 hlow r h)),
      k₄.gpr r (by simpa using hr'.1),
      k₃.gpr r (by simp only [List.mem_cons, not_or]; exact ⟨hr₁.2.1, hr'.2⟩),
      k₁.gpr r hr'.2, k₀.gpr r (by simpa using hr₁.2.2.2.2.2.2.1)]
  · rw [k₆.rd, k₅.rd, k₄.rd, k₃.rd, k₁.rd, k₀.rd]
  · rw [k₆.wr, k₅.wr, k₄.wr, k₃.wr, k₁.wr, k₀.wr]
  · rw [k₆.sp, k₅.sp, k₄.sp, k₃.sp, k₁.sp, k₀.sp]
  · rw [O₆ x hx, k₅.mem, hmem₄]
  · rw [e₆, e₅, hV]


end VG.Proof.P256.VerifySparse

end

end

/-! ### `P256.VerifySparse.Square`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.VerifySparse
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P256Square
open VG.Proof.Mont.AArch64.P256Square
open VG.Proof.Ed25519.AArch64 (Keeps)

def sparseSquare (o a : Nat) : List Instr :=
  core a ++ (Impl.P256.VerifySparse.correct [.x8,.x9,.x10,.x11] .x12 ++
    stores [.x8,.x9,.x10,.x11] o)

theorem square_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {M : Mod} (hME : M=Impl.P256.VerifySparse.M) (hN : M.n=4) (hM : ModOkA M size p s.mem base) (hA : ModA M)
    {o a : Nat} (ho : o+32 ≤ size) (ha : a+32 ≤ size) (ho8 : o%8=0) (ha8 : a%8=0)
    (hB : wordsVal s.mem base a 4 < p) :
    WP isa (.block (sparseSquare o a)) s fun t => SquareKeep base o s t ∧
      wordsVal t.mem base o 4 < p ∧
      wordsVal t.mem base o 4 * R % p = wordsVal s.mem base a 4 * wordsVal s.mem base a 4 % p := by
  rw [sparseSquare,WP.block_append_iff]
  refine WP.mono (core_ok hs ha ha8) fun s₁ ⟨⟨u,hu,e₁⟩,z₁,k₁⟩ => ?_
  obtain pe : P256Square.p=p := by decide
  rw [pe] at e₁
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain hb := square_redc_bound hB hu e₁
  obtain hV : regsVal s₁ [.x8,.x9,.x10,.x11] + 2^(64*M.n)*(s₁.gpr .x12).toNat < 2*p := by
    simpa only [low_regs,hN,pe] using hb
  rw [WP.block_append_iff]
  refine WP.mono (correctP_ok hs₁ (M:=M) hME (ts:=[.x8,.x9,.x10,.x11]) (top:=.x12)
    (by simpa only [List.length_cons,List.length_nil] using hN.symm) hM.n0 hM.n10
    (by unfold Fresh; decide) hM.mo hA.mo z₁ (by rw [k₁.mem]; exact hM.val) hV)
    fun s₂ ⟨e₂,k₂⟩ => ?_
  obtain hkc : ∀ r ∈ (.x2 :: .x17 :: [.x8,.x9,.x10,.x11] ++ dRegs M.n), r ∈ squareClob := by
    rw [hN]; decide
  obtain k₂' := k₂.mono hkc
  obtain hs₂ := hs₁.of_keeps k₂' (by decide)
  refine WP.mono (stores_ok [.x8,.x9,.x10,.x11] hs₂ ho ho8 (by decide))
    fun t ⟨e₃,k₃,o₃⟩ => ?_
  change wordsVal t.mem base o 4 = regsVal s₂ [.x8,.x9,.x10,.x11] at e₃
  obtain kp := k₁.trans k₂'
  refine ⟨⟨fun r hr => (k₃.gpr r (by simp)).trans (kp.gpr r hr),
    k₃.rd.trans kp.rd,k₃.wr.trans kp.wr,k₃.sp.trans kp.sp,
    fun x hx => (o₃ x hx).trans (congrFun kp.mem x)⟩,?_,?_⟩
  · rw [e₃,e₂]; exact Nat.mod_lt _ (by decide)
  · rw [e₃,e₂,low_regs,hN,Nat.mod_mul_mod,Nat.mul_comm]
    change R*(lowValue s₁+R*(s₁.gpr .x12).toNat)%p = _
    rw [e₁,Nat.add_mul_mod_self_right]


end VG.Proof.P256.VerifySparse

end

end


/-! The executable suffix replacement agrees with the proved sparse operation bodies.
The prefix is kept symbolic so the proof does not evaluate the full instruction list. -/

@[expose] public section

namespace VG.Proof.P256.VerifySparse
open VG.Proof.Mont.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

private theorem take_prefix {α : Type} (xs ys : List α) :
    (xs++ys).take ((xs++ys).length-ys.length)=xs := by
  simp only [List.length_append,Nat.add_sub_cancel,List.take_left]

theorem op_add (o a b : Nat) : Impl.P256.VerifySparse.op (.add o a b)=
    sparseAdd Impl.P256.VerifySparse.M o a b := by
  let pre := zero7 :: loads (low 4) a ++ chain (.adds .x) (.adcs .x) (low 4) b ++
    [.adc .x (top 4) .x7 .x7]
  let tail := csubR Impl.P256.VerifySparse.M (low 4) (top 4) ++ stores (low 4) o
  obtain raw : opCode Impl.P256.VerifySparse.M (.add o a b)=pre++tail := by
    simp only [opCode,Impl.Mont.AArch64.add,pre,tail,List.append_assoc,List.cons_append]
    rfl
  change (opCode Impl.P256.VerifySparse.M (.add o a b)).take
    ((opCode Impl.P256.VerifySparse.M (.add o a b)).length-tail.length) ++
    Impl.P256.VerifySparse.correct (low 4) (top 4) ++ stores (low 4) o = _
  rw [raw]
  change (pre++tail).take ((pre++tail).length-tail.length) ++ _ ++ _ = _
  rw [take_prefix]
  simp only [pre,sparseAdd,List.append_assoc]
  rfl


theorem op_mul (o a b : Nat) (hab : a≠b) : Impl.P256.VerifySparse.op (.mul o a b)=
    sparseMul Impl.P256.VerifySparse.M o a b := by
  obtain h : (a==b)=false := beq_eq_false_iff_ne.mpr hab
  let ts := (List.range 4).map (win 4 4)
  let pre := mulSetup Impl.P256.VerifySparse.M .x0 b ++
    (List.range 4).flatMap (round Impl.P256.VerifySparse.M .x0 .x0 a b)
  let tail := csubR Impl.P256.VerifySparse.M ts (win 4 4 4) ++ stores ts o
  obtain raw : opCode Impl.P256.VerifySparse.M (.mul o a b)=pre++tail := by
    rw [opCode,h]
    change mul Impl.P256.VerifySparse.M o a b=pre++tail
    have hn : Impl.P256.VerifySparse.M.n = 4 := rfl
    rw [mul_eq, mulR, hn]
    simp only [pre,tail,ts,List.append_assoc]
    rfl
  dsimp only [Impl.P256.VerifySparse.op]
  rw [h]
  rw [raw]
  change (pre++tail).take ((pre++tail).length-tail.length) ++ _ ++ _ = _
  rw [take_prefix]
  simp only [pre,sparseMul,List.append_assoc]
  rfl

theorem op_square (o a : Nat) : Impl.P256.VerifySparse.op (.mul o a a)=
    sparseSquare o a := by
  obtain h : P256Square.supported Impl.P256.VerifySparse.M=true := by decide
  let pre := VG.Proof.Mont.AArch64.P256Square.core a
  let tail := csubR Impl.P256.VerifySparse.M [.x8,.x9,.x10,.x11] .x12 ++ stores [.x8,.x9,.x10,.x11] o
  obtain raw : opCode Impl.P256.VerifySparse.M (.mul o a a)=pre++tail := by
    simp only [opCode,BEq.rfl,Bool.true_and,h,ite_true]
    simp only [P256Square.square,VG.Proof.Mont.AArch64.P256Square.core,pre,tail,List.append_assoc]
  dsimp only [Impl.P256.VerifySparse.op]
  rw [show (a==a)=true from beq_self_eq_true a]
  rw [raw]
  change (pre++tail).take ((pre++tail).length-tail.length) ++ _ ++ _ = _
  rw [take_prefix]
  simp only [pre,sparseSquare,List.append_assoc]
  rfl

end VG.Proof.P256.VerifySparse

end

end

/-! ### `P256.VerifySparse.Sub`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.VerifySparse
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Proof.Ed25519

private def addPrime : List Instr :=
  [.lsr .x .x1 .x17 32,.lsl .x .x2 .x17 32,.sub .x .x2 .x2 .x17,
   .adds .x .x8 .x8 .x17,.adcs .x .x9 .x9 .x1,
   .adcs .x .x10 .x10 .x7,.adc .x .x11 .x11 .x2]

private theorem maskWords_ok (s : State) :
    WP isa (.block [.lsr .x .x1 .x17 32,.lsl .x .x2 .x17 32,.sub .x .x2 .x2 .x17]) s fun t =>
      t.gpr .x1=s.gpr .x17>>>32 ∧ t.gpr .x2=(s.gpr .x17<<<32)-s.gpr .x17 ∧ Keeps [.x1,.x2] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    show 32<64 by decide,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_false,
    Option.some.injEq,exists_eq_left']
  refine ⟨trivial,trivial,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

private theorem adc_ok (s : State) :
    WP isa (.block [.adc .x .x11 .x11 .x2]) s fun t =>
      t.gpr .x11=Word64.addCarry (s.gpr .x11) (s.gpr .x2) s.c ∧ Keeps [.x11] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write_self,
    BitVec.setWidth_eq,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

private theorem adds_ok (s : State) :
    WP isa (.block [.adds .x .x8 .x8 .x17,.adcs .x .x9 .x9 .x1,
      .adcs .x .x10 .x10 .x7,.adc .x .x11 .x11 .x2]) s fun t =>
      regsVal t (low 4)=(regsVal s (low 4)+four (s.gpr .x17) (s.gpr .x1) (s.gpr .x7) (s.gpr .x2))%2^256 ∧
      Keeps [.x8,.x9,.x10,.x11] s t := by
  rw [show ([.adds .x .x8 .x8 .x17,.adcs .x .x9 .x9 .x1,
      .adcs .x .x10 .x10 .x7,.adc .x .x11 .x11 .x2] : List Instr)=
    [.adds .x .x8 .x8 .x17]++([.adcs .x .x9 .x9 .x1]++
    ([.adcs .x .x10 .x10 .x7]++[.adc .x .x11 .x11 .x2])) from rfl,WP.block_append_iff]
  refine WP.mono (addc_ok s .x8 .x8 .x17 true (c:=false) rfl) fun s1 ⟨e1,c1,k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addc_ok s1 .x9 .x9 .x1 false (c:=s1.c) rfl) fun s2 ⟨e2,c2,k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addc_ok s2 .x10 .x10 .x7 false (c:=s2.c) rfl) fun s3 ⟨e3,c3,k3⟩ => ?_
  refine WP.mono (adc_ok s3) fun t ⟨e4,k4⟩ => ?_
  rw [k1.gpr _ (by decide),k1.gpr _ (by decide),c1] at e2 c2
  rw [k2.gpr _ (by decide),k1.gpr _ (by decide),k2.gpr _ (by decide),k1.gpr _ (by decide),c2] at e3 c3
  rw [k3.gpr _ (by decide),k2.gpr _ (by decide),k1.gpr _ (by decide),
    k3.gpr _ (by decide),k2.gpr _ (by decide),k1.gpr _ (by decide),c3] at e4
  refine ⟨?_,(((k1.mono (by sub_regs)).trans (k2.mono (by sub_regs))).trans
    (k3.mono (by sub_regs))).trans (k4.mono (by sub_regs))⟩
  obtain et1 : t.gpr .x8=s1.gpr .x8 := by rw [k4.gpr _ (by decide),k3.gpr _ (by decide),k2.gpr _ (by decide)]
  obtain et2 : t.gpr .x9=s2.gpr .x9 := by rw [k4.gpr _ (by decide),k3.gpr _ (by decide)]
  obtain et3 : t.gpr .x10=s3.gpr .x10 := k4.gpr _ (by decide)
  change four (t.gpr .x8) (t.gpr .x9) (t.gpr .x10) (t.gpr .x11)=_
  rw [et1,et2,et3,e1,e2,e3,e4]
  exact addFour_value _ _ _ _ _ _ _ _

private theorem addPrime_ok (s : State) (b : Bool) (hz : s.gpr .x7=0)
    (hm : s.gpr .x17=if b then -1 else 0) :
    WP isa (.block addPrime) s fun t =>
      regsVal t (low 4)=(regsVal s (low 4)+(if b then p else 0))%2^256 ∧
      Keeps [.x1,.x2,.x8,.x9,.x10,.x11] s t := by
  change WP isa (.block (([.lsr .x .x1 .x17 32,.lsl .x .x2 .x17 32,.sub .x .x2 .x2 .x17] : List Instr)++
    [.adds .x .x8 .x8 .x17,.adcs .x .x9 .x9 .x1,.adcs .x .x10 .x10 .x7,.adc .x .x11 .x11 .x2])) s _
  rw [WP.block_append_iff]
  refine WP.mono (maskWords_ok s) fun s1 ⟨e1,e2,k1⟩ => ?_
  refine WP.mono (adds_ok s1) fun t ⟨et,k2⟩ => ?_
  refine ⟨?_,(k1.mono (by sub_regs)).trans (k2.mono (by sub_regs))⟩
  obtain er : regsVal s1 (low 4)=regsVal s (low 4) := regsVal_congr fun q hq =>
    k1.gpr q ((by decide : ∀q∈low 4,q∉[Reg.x1,.x2]) q hq)
  rw [er,k1.gpr .x17 (by decide),k1.gpr .x7 (by decide),hz,e1,e2,hm,(masked_words b).2.2] at et
  exact et


/-- Canonical P-256 subtraction, with the ordinary field-operation frame. -/
theorem sub_ok {s : State} {base : Addr} {size o a b : Nat} (hs : Scr s base size)
    (ho : o+32≤size) (ha : a+32≤size) (hb : b+32≤size)
    (ho8 : o%8=0) (ha8 : a%8=0) (hb8 : b%8=0)
    (hA : wordsVal s.mem base a 4<p) (hB : wordsVal s.mem base b 4<p) :
    WP isa (.block (Impl.P256.VerifySparse.sub o a b)) s fun t =>
      OpKeep Impl.P256.VerifySparse.M base o s t ∧
      wordsVal t.mem base o 4=(wordsVal s.mem base a 4+p-wordsVal s.mem base b 4)%p := by
  obtain hf : Fresh (low 4) := by unfold Fresh; decide
  have hl : (low 4).length=4 := rfl
  rw [Impl.P256.VerifySparse.sub,show zero7::loads (low 4) a=[zero7]++loads (low 4) a from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s0 ⟨z0,k0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok (low 4) (hs.of_keeps k0 (by decide)) (a:=a) ha ha8 hf)
    fun s1 ⟨e1,k1,_⟩ => ?_
  obtain hs1 := (hs.of_keeps k0 (by decide)).of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  obtain cw := chainSubs_ok hs1 (b:=b) (t:=.x8) (ts:=[.x9,.x10,.x11]) hb hb8 hf
  refine WP.mono cw fun s2 ⟨e2,k2⟩ => ?_
  obtain hs2 := hs1.of_keeps k2 (by decide)
  obtain z2 : s2.gpr .x7=0 := by rw [k2.gpr _ (by decide),k1.gpr _ (by decide),z0]
  rw [show ([.sbc .x .x17 .x7 .x7,.lsr .x .x1 .x17 32,.lsl .x .x2 .x17 32,
      .sub .x .x2 .x2 .x17,.adds .x .x8 .x8 .x17,.adcs .x .x9 .x9 .x1,
      .adcs .x .x10 .x10 .x7,.adc .x .x11 .x11 .x2] : List Instr)=
      [.sbc .x .x17 .x7 .x7]++addPrime from rfl,List.append_assoc,WP.block_append_iff]
  refine WP.mono (sbcMask_ok s2 z2) fun s3 ⟨x3,k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addPrime_ok s3 (!s2.c) (by rw [k3.gpr _ (by decide),z2]) x3)
    fun s4 ⟨e4,k4⟩ => ?_
  obtain hs4 := (hs2.of_keeps k3 (by decide)).of_keeps k4 (by decide)
  refine WP.mono (stores_ok (low 4) hs4 (o:=o) ho ho8 hf.1) fun t ⟨et,kt,ot⟩ => ?_
  rw [hl] at et ot
  obtain keep : Keeps (clob 4) s s4 :=
    (((k0.mono (by decide)).trans (k1.mono (by decide))).trans (k2.mono (by decide))).trans
      ((k3.mono (by decide)).trans (k4.mono (by decide)))
  obtain er : regsVal s3 (low 4)=regsVal s2 (low 4) :=
    regsVal_congr fun q hq => k3.gpr q (by
      obtain ne : ∀ r∈low 4,r≠.x17 := by decide
      simpa only [List.mem_singleton] using ne q hq)
  rw [er] at e4
  change regsVal s2 (low 4)+wordsVal s1.mem base b 4=regsVal s1 (low 4)+2^256*(!s2.c).toNat at e2
  rw [e1,k1.mem,k0.mem] at e2
  change regsVal s2 (low 4)+wordsVal s.mem base b 4=wordsVal s.mem base a 4+2^256*(!s2.c).toNat at e2
  refine ⟨⟨fun r hr => (kt.gpr r (by simp)).trans (keep.gpr r hr),
    kt.rd.trans keep.rd,kt.wr.trans keep.wr,kt.sp.trans keep.sp,fun x hx _ => ?_⟩,?_⟩
  · exact (ot x hx).trans (congrFun keep.mem x)
  · rw [et,e4]
    obtain rr := regsVal_lt s2 (low 4)
    rw [hl] at rr
    obtain pp : p<2^256 := by decide
    cases hc : s2.c <;> simp only [hc,Bool.not_false,Bool.not_true,Bool.toNat_true,
      Bool.toNat_false,Nat.mul_one,Nat.mul_zero,Nat.add_zero,Bool.false_eq_true,ite_true,ite_false] at e2 ⊢
    · have ne : wordsVal s.mem base a 4<wordsVal s.mem base b 4 := by omega_arith
      obtain small : wordsVal s.mem base a 4+p-wordsVal s.mem base b 4<p := by omega_arith
      obtain eq : regsVal s2 (low 4)+p=2^256+(wordsVal s.mem base a 4+p-wordsVal s.mem base b 4) := by omega_arith
      rw [eq,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega_arith),Nat.mod_eq_of_lt small]
    · have ge : wordsVal s.mem base b 4≤wordsVal s.mem base a 4 := by omega_arith
      rw [Nat.mod_eq_of_lt rr,show wordsVal s.mem base a 4+p-wordsVal s.mem base b 4=
        (wordsVal s.mem base a 4-wordsVal s.mem base b 4)+p by omega_arith,Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith

end VG.Proof.P256.VerifySparse

end

end


@[expose] public section

namespace VG.Proof.P256.VerifySparse
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Weierstrass VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

/-- The sparse compiler retains the canonical Montgomery multiplication contract. -/
theorem mulOp_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {M : Mod} (hME : M=Impl.P256.VerifySparse.M) {m : Nat} (hp : m=p)
    (hM : ModOkA M size m s.mem base) (hA : ModA M) {o a b : Nat} (ho : o+8*M.n≤size)
    (ha : a+8*M.n≤size) (hb : b+8*M.n≤size) (ho8 : o%8=0) (ha8 : a%8=0) (hb8 : b%8=0)
    (hB : wordsVal s.mem base b M.n<m) :
    WP isa (.block (Impl.P256.VerifySparse.op (.mul o a b))) s fun t =>
      OpKeep M base o s t ∧ wordsVal t.mem base o M.n<m ∧
      wordsVal t.mem base o M.n*2^(64*M.n)%m =
        wordsVal s.mem base a M.n*wordsVal s.mem base b M.n%m := by
  subst m
  obtain hn : M.n=4 := hME ▸ rfl
  by_cases hab : a=b
  · subst b
    rw [op_square]
    refine WP.mono (square_ok hs hME hn hM hA (by simpa only [hn] using ho)
      (by simpa only [hn] using ha) ho8 ha8 (by simpa only [hn] using hB))
      fun t ⟨hk,hlt,he⟩ => ?_
    exact ⟨hk.toOpKeep hn,by simpa only [hn] using hlt,by simpa only [hn] using he⟩
  · rw [op_mul o a b hab]
    rw [←hME]
    exact mul_ok hs hME hM.toW hM.n10 hA ho ha hb ho8 ha8 hb8 hB

/-- The sparse compiler retains canonical addition and the ordinary memory frame. -/
theorem addOp_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {M : Mod} (hME : M=Impl.P256.VerifySparse.M) {m : Nat} (hp : m=p)
    (hM : ModOkA M size m s.mem base) (hA : ModA M) {o a b : Nat} (ho : o+8*M.n≤size)
    (ha : a+8*M.n≤size) (hb : b+8*M.n≤size) (ho8 : o%8=0) (ha8 : a%8=0) (hb8 : b%8=0)
    (hAB : wordsVal s.mem base a M.n+wordsVal s.mem base b M.n<2*m) :
    WP isa (.block (Impl.P256.VerifySparse.op (.add o a b))) s fun t =>
      OpKeep M base o s t ∧ wordsVal t.mem base o M.n=
        (wordsVal s.mem base a M.n+wordsVal s.mem base b M.n)%m := by
  subst m
  rw [op_add,←hME]
  exact add_ok hs hME hM.toW hM.n10 hA ho ha hb ho8 ha8 hb8 hAB

/-- The sparse compiler retains canonical subtraction and the ordinary memory frame. -/
theorem subOp_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {M : Mod} (hME : M=Impl.P256.VerifySparse.M) {m : Nat} (hp : m=p)
    {o a b : Nat} (ho : o+8*M.n≤size) (ha : a+8*M.n≤size) (hb : b+8*M.n≤size)
    (ho8 : o%8=0) (ha8 : a%8=0) (hb8 : b%8=0)
    (hA : wordsVal s.mem base a M.n<m) (hB : wordsVal s.mem base b M.n<m) :
    WP isa (.block (Impl.P256.VerifySparse.op (.sub o a b))) s fun t =>
      OpKeep M base o s t ∧ wordsVal t.mem base o M.n=
        (wordsVal s.mem base a M.n+m-wordsVal s.mem base b M.n)%m := by
  subst M m
  exact sub_ok hs ho ha hb ho8 ha8 hb8 hA hB

theorem fop_ok {M : Mod} (hME : M=Impl.P256.VerifySparse.M) {base : Addr} {size m : Nat} [NeZero m] (hp : m=p) {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {op : FOp} (hS : ∀ x ∈ op.out :: op.ins, Sl x)
    (hR : ∀ x ∈ op.ins, x ∈ V) :
    WP isa (.block (Impl.P256.VerifySparse.op op)) s fun s' =>
      OpKeep M base op.out s s' ∧ Inv M base size m Sl (op.out :: V) (op.run E) s' := by
  cases op with
  | mul o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    refine WP.mono (mulOp_ok hI.scr hME hp hI.mod hAl.mod (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hAl.sl o hS.1) (hAl.sl a hS.2.1) (hAl.sl b hS.2.2) (hI.lt b hR.2)) fun s' ⟨hk, hlt, heq⟩ => ⟨hk, hI.update hL hS.1 hk hlt ?_⟩
    rw [toM_mul hm heq, hI.val a hR.1, hI.val b hR.2]
  | add o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    obtain hA := hI.lt a hR.1
    obtain hB := hI.lt b hR.2
    refine WP.mono (addOp_ok hI.scr hME hp hI.mod hAl.mod (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hAl.sl o hS.1) (hAl.sl a hS.2.1) (hAl.sl b hS.2.2) (by omega_using [hA, hB])) fun s' ⟨hk, heq⟩ => ⟨hk, hI.update hL hS.1 hk ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega_using [hA])
    · rw [heq, toM_add, hI.val a hR.1, hI.val b hR.2]
  | sub o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    obtain hA := hI.lt a hR.1
    obtain hB := hI.lt b hR.2
    refine WP.mono (subOp_ok hI.scr hME hp (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hAl.sl o hS.1) (hAl.sl a hS.2.1) (hAl.sl b hS.2.2) hA hB)
      fun s' ⟨hk, heq⟩ => ⟨hk, hI.update hL hS.1 hk ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega_using [hA])
    · rw [heq, toM_sub (by omega_using [hB]), hI.val a hR.1, hI.val b hR.2]

/-- A field program. -/
theorem fprog_ok {M : Mod} (hME : M=Impl.P256.VerifySparse.M) {base : Addr} {size m : Nat} [NeZero m] (hp : m=p) {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fin m} {s : State},
      Inv M base size m Sl V E s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) →
      readsOk ops V = true →
      WP isa (.block (ops.flatMap Impl.P256.VerifySparse.op)) s fun s' => ProgKeep M base (ops.map FOp.out) s s' ∧
        Inv M base size m Sl (validAfter ops V) (runOps ops E) s'
  | [], _, _, s, hI, _, _ => WP.block_nil ⟨ProgKeep.refl _ _ _ s, hI⟩
  | op :: ops, V, E, s, hI, hS, hR => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (fop_ok hME hp hL hAl hm hI (hS op (List.mem_cons_self ..)) hR.1) fun s₁ ⟨k₁, I₁⟩ => ?_
    refine WP.mono (fprog_ok hME hp hL hAl hm ops I₁ (fun op' h => hS op' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨⟨fun r hr => (k₂.gpr r hr).trans (k₁.gpr r hr), k₂.rd.trans k₁.rd,
        k₂.wr.trans k₁.wr, k₂.sp.trans k₁.sp, fun x hx ht => ?_⟩, I₂⟩
    rw [List.map_cons] at hx
    rw [k₂.mem x (fun w hw => hx w (List.mem_cons_of_mem _ hw)) ht,
      k₁.mem x (hx _ (List.mem_cons_self ..)) ht]


end VG.Proof.P256.VerifySparse
