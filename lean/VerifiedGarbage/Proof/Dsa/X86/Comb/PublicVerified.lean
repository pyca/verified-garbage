module

import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Correct
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Dsa.X86.PowEntry
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicSetupTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicBuildTiming
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable
import VerifiedGarbage.Proof.Dsa.X86.Comb.Setup
import VerifiedGarbage.Proof.Mont.X86.CombBuild
import VerifiedGarbage.Proof.Dsa.X86.Comb.PrivateTiming
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerLoop
meta import VerifiedGarbage.Impl.Dsa.X86.Comb
meta import VerifiedGarbage.Impl.Mont.X86.CombPower
meta import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Mont.X86.CombTableState
meta import VerifiedGarbage.Proof.Mont.X86.CombTableState
import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerDigits
import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicSelectTiming
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerFrame
meta import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerFrame
meta import VerifiedGarbage.Proof.Mont.Words32

/-! ### `Dsa.X86.Comb.PublicPowerTiming`, which only this module used -/

section

/-! ### `Dsa.X86.Comb.PublicPowerStepTiming`, which only this module used -/

section

/-! A public comb step uses the same public digit in both executions. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (TableAt)

theorem powerDigits_check {n e : Nat} (h : Supported n e) :
    ∃ hint, (VG.Taint.check taint (workspaceTaint false) (VG.Impl.Mont.X86.Comb.powerDigits n e) hint).map
      (taint.le (workspaceTaint false))=some true := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> exact ⟨_, by taint_decide⟩

theorem powerDigits_relCT {n e : Nat} (h : Supported n e) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (VG.Impl.Mont.X86.Comb.powerDigits n e)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  obtain ⟨τ,check,le⟩ := Option.map_eq_some_iff.mp (powerDigits_check h).choose_spec
  exact checkedProgramChange check le

structure PublicPowerState (n e m g E x : Nat) (base : Addr) (s : State) : Prop where
  ctx : Context n m base (layout n e).size s
  table : TableAt n (context n) m g (32*e) base (fun _ => True) s.mem
  acc : wordsVal s.mem base (slot n 6) n=Spec.Rsa.powMod g E m*2^(64*n)%m
  exp : val32 s.mem base (slot n 8) (expWords e)=x

theorem publicPowerLookup_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g E x : Nat) :
    RelCT isa (fun s t => PublicPowerState n e m g E x base s ∧ PublicPowerState n e m g E x base t)
      (VG.Impl.Mont.X86.Comb.powerLookup n e (context n) true)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold VG.Impl.Mont.X86.Comb.powerLookup VG.Impl.Mont.X86.Comb.seq
  simp only [ite_true,List.foldr_cons,List.foldr_nil]
  refine RelCT.seq (R := WordPair base (layout n e).size) ?_
    (RelCT.seq (publicSelect_relCT _ _ _ _ _ (power_bounds h).2.2.2.2.2.2) (RelCT.block_nil (fun _ _ h => h)))
  intro s t tr ur sf tf ⟨S,T⟩ Es Et
  have DI : s.gpr .edi=t.gpr .edi := BitVec.eq_of_toNat_eq (S.ctx.scr.edi_toNat.trans T.ctx.scr.edi_toNat.symm)
  have A := agree_regs (rs := [.edi]) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact DI)
  obtain ⟨Cs,_,_,_,Ws,_,_⟩ := wp_result (powerDigits_ok h S.ctx S.table S.acc) Es
  obtain ⟨Ct,_,_,_,Wt,_,_⟩ := wp_result (powerDigits_ok h T.ctx T.table T.acc) Et
  exact ⟨(powerDigits_relCT h _ _ _ _ _ _ A Es Et).1,Cs.scr,Ct.scr,by rw [Ws,Wt,S.exp,T.exp]⟩

theorem publicPowerStep_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g E x : Nat) :
    RelCT isa (fun s t => PublicPowerState n e m g E x base s ∧ PublicPowerState n e m g E x base t)
      (VG.Impl.Mont.X86.Comb.powerStep n e (context n) true)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold VG.Impl.Mont.X86.Comb.powerStep VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons,List.foldr_nil]
  refine RelCT.seq (publicPowerLookup_relCT h base m g E x) (RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint false)) ?_ ?_)
  · exact checkedProgramChange (mul_check false _ _ _ _ _ _) rfl
  · exact RelCT.seq (checkedProgramChange (σ := workspaceTaint false) (hint := .block []) rfl rfl)
      (RelCT.block_nil (fun _ _ h => h))

end VG.Proof.Dsa.X86.Comb

end

end

/-! ### `Dsa.X86.Comb.PublicPowerLoopTiming`, which only this module used -/

section

/-! Equal public exponents follow the same fixed-count comb loop. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Rsa.FixedBaseComb (high)

theorem publicPowerLoop_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g x : Nat) (s₀ t₀ : State) :
    RelCT isa (fun s t => PowerLoop n e m g x 0 base s₀ s ∧ PowerLoop n e m g x 0 base t₀ t)
      (.loop (VG.Impl.Mont.X86.Comb.powerStep n e (context n) true) .ne)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  let I (remaining : Nat) (s t : State) : Prop := ∃ i, remaining=rows e-i ∧ i<rows e ∧
    PowerLoop n e m g x i base s₀ s ∧ PowerLoop n e m g x i base t₀ t
  refine (RelCT.loop I ?_ (rows e)).mono ?_ (fun _ _ h => h)
  · intro remaining s t tr ur sf tf ⟨i,eq,hi,S,T⟩ E F
    subst remaining
    have pair : PublicPowerState n e m g (high (32*e) x (rows e-i)) (x*2^i%2^(32*expWords e)) base s ∧
        PublicPowerState n e m g (high (32*e) x (rows e-i)) (x*2^i%2^(32*expWords e)) base t :=
      ⟨⟨S.ctx,S.table,S.acc,S.exp⟩,⟨T.ctx,T.table,T.acc,T.exp⟩⟩
    obtain ⟨Trace,Agree⟩ := publicPowerStep_relCT h base m g _ _ _ _ _ _ _ _ pair E F
    obtain ⟨S',Zs⟩ := wp_result (powerLoop_step h true hi S) E
    obtain ⟨T',Zt⟩ := wp_result (powerLoop_step h true hi T) F
    refine ⟨Trace,?_,fun _ => Agree,?_⟩
    · change VG.X86.eval .ne sf=VG.X86.eval .ne tf
      simp only [VG.X86.eval,Zs,Zt]
    · intro hc
      have next : i+1<rows e := by
        have le : i+1≤rows e := by omega_using [hi]
        by_contra hn
        have eq : i+1=rows e := by omega
        change VG.X86.eval .ne sf=some true at hc
        simp only [VG.X86.eval,Zs,eq,decide_true,Option.map_some,Bool.not_true] at hc
        cases hc
      exact ⟨rows e-(i+1),by omega_using [hi],i+1,rfl,next,S',T'⟩
  · intro s t ⟨S,T⟩
    exact ⟨0,by omega_using [],(power_bounds h).1,S,T⟩

end VG.Proof.Dsa.X86.Comb

end

end


/-! Timing of public exponentiation through initialization, the comb loop and decoding. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (TableAt)

theorem powerInit_check {n e : Nat} (h : Supported n e) :
    ∃ hint, (VG.Taint.check taint (workspaceTaint false) (VG.Impl.Mont.X86.Comb.powerInit n e (context n)) hint).map
      (taint.le (workspaceTaint false))=some true := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> exact ⟨_, by taint_decide⟩

structure PublicPowerInput (n e m g x : Nat) (base : Addr) (s : State) : Prop where
  ctx : Context n m base (layout n e).size s
  table : TableAt n (context n) m g (32*e) base (fun _ => True) s.mem
  exp : val32 s.mem base (slot n 8) e=x

theorem publicPower_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g x : Nat) :
    RelCT isa (fun s t => PublicPowerInput n e m g x base s ∧ PublicPowerInput n e m g x base t)
      (VG.Impl.Mont.X86.Comb.combPower n e (context n) true)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold VG.Impl.Mont.X86.Comb.combPower VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons,List.foldr_nil]
  let R := fun s t => PowerLoop n e m g x 0 base s s ∧ PowerLoop n e m g x 0 base t t
  refine RelCT.seq (R := R) ?_ (RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint false)) ?_
    (RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint false)) (checkedProgramChange (mul_check false _ _ _ _ _ _) rfl)
      (RelCT.block_nil (fun _ _ h => h))))
  · intro s t tr ur sf tf ⟨S,T⟩ Es Et
    obtain ⟨τ,check,le⟩ := Option.map_eq_some_iff.mp (powerInit_check h).choose_spec
    have CT := checkedProgramChange check le
    have DI : s.gpr .edi=t.gpr .edi := BitVec.eq_of_toNat_eq (S.ctx.scr.edi_toNat.trans T.ctx.scr.edi_toNat.symm)
    have A := agree_regs (rs := [.edi]) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact DI)
    obtain ⟨Cs,Ts,As,Xs,Is,_,_⟩ := wp_result (powerInit_ok h S.ctx S.table) Es
    obtain ⟨Ct,Tt,At,Xt,It,_,_⟩ := wp_result (powerInit_ok h T.ctx T.table) Et
    have bound : x<2^(32*e) := S.exp ▸ val32_lt s.mem base (slot n 8) e
    exact ⟨(CT _ _ _ _ _ _ A Es Et).1,
      powerLoop_initial h Cs Ts As (Xs.trans S.exp) bound Is,
      powerLoop_initial h Ct Tt At (Xt.trans T.exp) bound It⟩
  · intro s t tr ur sf tf P Es Et
    exact publicPowerLoop_relCT h base m g x s t _ _ _ _ _ _ P Es Et

end VG.Proof.Dsa.X86.Comb

end

end

/-! ### `Dsa.X86.Comb.PublicBodyTiming`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.Comb.PrivateBodyTiming`, which this module and modules that import it used -/

section

/-! The callable private comb helper leaks no exponent-dependent trace. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem save_relCT :
    RelCT isa (fun s t => s.gpr .esp=t.gpr .esp ∧ arg s 0=arg t 0 ∧
      readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg s 0) ∧
      readSrc t (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg t 0))
      (.block VG.Impl.Dsa.X86.Pow.save) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold VG.Impl.Dsa.X86.Pow.save
  rw [List.append_assoc]
  exact RelCT.block_append (RelCT.seq (scratchArgument_relCT 0)
    (checkedProgramChange (σ := workspaceTaint false) (hint := .block []) rfl rfl))

theorem private_body_relCT {n e : Nat} (h : Supported n e) :
    RelCT isa (fun s t => s.gpr .esp=t.gpr .esp ∧ arg s 0=arg t 0 ∧
      readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg s 0) ∧
      readSrc t (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg t 0))
      (body false n e) (fun _ _ => True) := by
  unfold body
  refine RelCT.seq save_relCT ?_
  have eq : privateInputs=workspaceTaint false := by decide
  rw [←eq]
  refine RelCT.seq (private_core_relCT h) ?_
  exact (checkedProgramChange (σ := { regs := .ofList [], flags := false }) (hint := .block []) rfl rfl).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Dsa.X86.Comb

end

end

/-! Public preparation uses the shared calling boundary and proven public core. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/PublicCoreTiming.lean`, which only this module imported.
section

/-! Public preparation leaks only the modulus, generator, exponent and workspace address. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

structure PublicCoreInput (n e m g x : Nat) (base : Addr) (s : State) extends PublicSetupInput n e m base s where
  generator : wordsVal s.mem base (slot n 5) n=g
  exponent : val32 s.mem base (slot n 8) e=x

theorem publicCore_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g x : Nat)
    (hm : 1<m) (odd : m%2=1) :
    RelCT isa (fun s t => PublicCoreInput n e m g x base s ∧ PublicCoreInput n e m g x base t)
      (core true n e) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  have shape : 128*n<2^32 := by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  let B := fun (s : State) => PublicBuildInput n e m g base s ∧ val32 s.mem base (slot n 8) e=x
  unfold core
  simp only [ite_true]
  refine RelCT.seq (R := fun s t => PublicPowerInput n e m g x base s ∧ PublicPowerInput n e m g x base t)
    (RelCT.seq (R := fun s t => B s ∧ B t) ?_ ?_) (publicPower_relCT h base m g x)
  · intro s t tr ur sf tf ⟨S,T⟩ Es Et
    have step {u v : State} (U : PublicCoreInput n e m g x base u) {trace}
        (E : Exec isa (setup n) u trace v) : B v := by
      obtain ⟨C,One,R,O,_⟩ := wp_result (setup_ok U.scr (table_layout h).positive shape
        (by have L := table_layout h; have := L.apart; have := L.bound; omega) U.modulus hm odd) E
      have G : wordsVal v.mem base (slot n 5) n=g := by
        rw [wordsVal_eq_val32,O.val32 (by
          rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
          rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),←wordsVal_eq_val32,U.generator]
      have X : val32 v.mem base (slot n 8) e=x := (O.val32 (by
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)).trans U.exponent
      exact ⟨⟨C,One,R,G⟩,X⟩
    exact ⟨(publicSetup_relCT h base m hm odd _ _ _ _ _ _ ⟨S.toPublicSetupInput,T.toPublicSetupInput⟩ Es Et).1,
      step S Es,step T Et⟩
  · intro s t tr ur sf tf ⟨⟨S,Xs⟩,⟨T,Xt⟩⟩ Es Et
    have step {u v : State} (U : PublicBuildInput n e m g base u)
        (X : val32 u.mem base (slot n 8) e=x) {trace}
        (E : Exec isa (VG.Impl.Mont.X86.Comb.combBuild n e (context n)) u trace v) : PublicPowerInput n e m g x base v := by
      obtain ⟨C,_,_,T,O,_⟩ := wp_result (VG.Proof.Mont.X86.Comb.build_ok (table_layout h) U.ctx U.one U.r2
        (power_bounds h).1 (power_bounds h).2.1) E
      rw [U.generator] at T
      exact ⟨C,T,(O.val32 (by
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
        rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)).trans X⟩
    exact ⟨(publicBuild_relCT h base m g _ _ _ _ _ _ ⟨S,T⟩ Es Et).1,step S Xs Es,step T Xt Et⟩

end VG.Proof.Dsa.X86.Comb
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

structure PublicBodyInput (n e m g x : Nat) (base : Addr) (s : State) : Prop where
  entry : Pow.Entry s base (layout n e).size
  modulus : wordsVal s.mem base (slot n 0) n=m
  generator : wordsVal s.mem base (slot n 5) n=g
  exponent : val32 s.mem base (slot n 8) e=x

theorem publicBody_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m g x : Nat)
    (hm : 1<m) (odd : m%2=1) :
    RelCT isa (fun s t => PublicBodyInput n e m g x base s ∧ PublicBodyInput n e m g x base t ∧
      s.gpr .esp=t.gpr .esp ∧ arg s 0=arg t 0 ∧
      readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg s 0) ∧
      readSrc t (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg t 0))
      (body true n e) (fun _ _ => True) := by
  have hz : 24≤(layout n e).size := by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  unfold body
  refine RelCT.seq (R := fun s t => PublicCoreInput n e m g x base s ∧ PublicCoreInput n e m g x base t) ?_
    (RelCT.seq (publicCore_relCT h base m g x hm odd)
      ((checkedProgramChange (σ := { regs := .ofList [], flags := false }) (hint := .block []) rfl rfl).mono
        (fun _ _ h => h) (fun _ _ _ => trivial)))
  intro s t tr ur sf tf ⟨S,T,A⟩ Es Et
  have step {u v : State} (U : PublicBodyInput n e m g x base u) {trace}
      (E : Exec isa (.block VG.Impl.Dsa.X86.Pow.save) u trace v) : PublicCoreInput n e m g x base v := by
    obtain ⟨C,_,O,_⟩ := wp_result (Pow.save_ok U.entry hz) E
    have bounds : 24≤slot n 0 ∧ slot n 0+8*n≤2^64 ∧ 24≤slot n 5 ∧ slot n 5+8*n≤2^64 ∧
        24≤slot n 8 ∧ slot n 8+4*e≤2^64 := by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
    refine ⟨⟨C,?_⟩,?_,?_⟩
    · exact (O.wordsVal (.inr bounds.1) bounds.2.1).trans U.modulus
    · exact (O.wordsVal (.inr bounds.2.2.1) bounds.2.2.2.1).trans U.generator
    · exact (O.val32 (by have := bounds.2.2.2.2.1; omega_using [bounds]) bounds.2.2.2.2.2).trans U.exponent
  exact ⟨(save_relCT _ _ _ _ _ _ A Es Et).1,step S Es,step T Et⟩

end VG.Proof.Dsa.X86.Comb

end

end

/-! The public helper satisfies the merged preparation contract, including timing. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Dsa.X86.Pow (ws bytes numAt_eq8 numAt_eq4)

theorem publicNarrowRun {n e m size : Nat} {base : Addr} {s t : State} {tr : List Leak}
    (h : Supported n e) (E : Pow.Entry s base size) (hz : (layout n e).size≤size)
    (hv : wordsVal s.mem base (slot n 0) n=m) (hm : 1<m) (odd : m%2=1)
    (run : Exec isa (body true n e) s tr t) :
    ∃ u, Exec isa (body true n e) (narrowState n e base s) tr u := by
  obtain ⟨En,R,W⟩ := narrowResources E hz
  obtain ⟨trace,u,Run,_⟩ := body_ok h true En hv hm odd (fun eq => Bool.noConfusion eq)
  obtain ⟨rfl,_⟩ := Exec.det run (regionModel.inline Run R W).1
  exact ⟨u,Run⟩

end VG.Proof.Dsa.X86.Comb
