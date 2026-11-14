module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.RepresentationMemory
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeLayout
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves
import VerifiedGarbage.Proof.Framework.Omega

/-! One existing Montgomery inversion between verified ordinary-field conversions. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime montBase prime_value)
open VG.Impl.Weierstrass.AArch64.P521Native (config)

private theorem config_prime : config.C.p=fieldPrime := by
  dsimp only [config,VG.Impl.Ecdsa.AArch64.p521,Spec.P521.curve,Spec.P521.p,fieldPrime]

private theorem config_n : config.n=9 := rfl
private theorem config_rz : config.sl VG.Impl.Ecdsa.AArch64.RZ=1216 := rfl
private theorem config_acc : config.sl VG.Impl.Ecdsa.AArch64.ACC=2152 := rfl

private theorem toM_pow_relabel {m n R a b k : Nat} [NeZero m] [NeZero n] (eq : m=n)
    (h : toM m R a=toM m R b^k) : toM n R a=toM n R b^k := by
  cases eq
  exact h

private theorem nine_base : 2^(64*9)=montBase := by
  dsimp only [montBase]

private theorem toM_pow_relabel_base {m R S a b k : Nat} [NeZero m] (eq : R=S)
    (h : toM m R a=toM m R b^k) : toM m S a=toM m S b^k := by
  cases eq
  exact h

def normalizeInversePhase : Prog isa :=
  .seq (.block (representationMemoryCode representationToCode 1216))
    (.seq config.pPow (.block (representationMemoryCode representationFromCode 2152)))

def normalizeInverseWrites : List (Nat × Nat) :=
  [(1216,72)]++(VG.Proof.Ecdsa.AArch64.chainWc config++[(2152,72)])

theorem normalize_inverse_writes_fit : ∀w∈normalizeInverseWrites,w.1+w.2≤8192 := by decide

theorem normalize_inverse_prefix_apart : ∀m<16,1≤m → ∀w∈normalizeInverseWrites,
    normalizePrefixSlot m+72≤w.1 ∨ w.1+w.2≤normalizePrefixSlot m := by decide

theorem normalize_inverse_readonly : ∀w∈normalizeInverseWrites,w.1+w.2≤3232 ∨ 3952≤w.1 := by decide

theorem normalize_pow_vectors (hc : VG.Proof.Ecdsa.AArch64.BaseCfgOk config)
    {s : State} {Q : State → Prop} (h : WP isa config.pPow s Q) :
    WP isa config.pPow s fun t => Q t ∧ t.v .v31=s.v .v31 := by
  have hi : config.inverse≠none := by decide
  obtain ⟨_,noV,_,_,_⟩ := hc.inv_fn hi
  have callSource : config.pPow=VG.Impl.Ecdsa.AArch64.Cfg.invCall "vg_p521_inv_mod_p" (config.invFn config.pPowI) := rfl
  have no31 : ∀i∈instrs config.pPow,vdstOf i≠some .v31 := by
    intro i hi
    rw [callSource] at hi
    simp only [VG.Impl.Ecdsa.AArch64.Cfg.invCall,instrs,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|hi|rfl
    · decide
    · have checked := List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ noV) i hi
      intro he
      rw [he] at checked
      cases checked
    · decide
  obtain ⟨trace,t,exec,q⟩ := h
  exact ⟨trace,t,exec,q,Exec.vec (c:=config.pPow) (r:=.v31) no31 exec⟩

theorem normalize_inverse_phase_ok (hc : VG.Proof.Ecdsa.AArch64.BaseCfgOk config)
    {s : State} {base : Addr} (hs : Scr s base 8192)
    (hM : ModOkA config.MP' 8192 config.C.p s.mem base)
    (bound : wordsVal s.mem base 1216 9<fieldPrime) :
    WP isa normalizeInversePhase s fun t =>
      wordsVal t.mem base 2152 9<fieldPrime ∧
      Fin.ofNat fieldPrime (wordsVal t.mem base 2152 9)=
        Fin.ofNat fieldPrime (wordsVal s.mem base 1216 9)^(fieldPrime-2) ∧
      Unch base normalizeInverseWrites s.mem t.mem ∧
      t.gpr .x0=base ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
      t.gpr .x20=s.gpr .x20 ∧ t.gpr .x26=s.gpr .x26 ∧ t.gpr .x30=s.gpr .x30 ∧ t.v .v31=s.v .v31 ∧
      wordsVal t.mem base 1216 9=toMontValue (wordsVal s.mem base 1216 9) ∧
      (∀r∈[Reg.x27,Reg.x28],t.gpr r=s.gpr r) := by
  rw [normalizeInversePhase,WP.seq_iff]
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by decide)
    (representation_to_memory hs (d:=1216) (by decide) (by decide) bound))
    fun u ⟨⟨toValue,toBound,ku,ou⟩,vu⟩ => ?_
  have hsu := hs.of_keepRegs ku (by decide)
  have modSame : wordsVal u.mem base config.MP'.mo config.MP'.n=wordsVal s.mem base config.MP'.mo config.MP'.n :=
    ou.wordsVal (by decide) (by decide)
  have hMu : ModOkA config.MP' 8192 config.C.p u.mem base := {hM with val:=by rw [modSame]; exact hM.val}
  have powerBound : wordsVal u.mem base (config.sl VG.Impl.Ecdsa.AArch64.RZ) config.n<config.C.p := by
    rw [config_rz,config_n,config_prime]
    exact toBound
  rw [WP.seq_iff]
  refine WP.mono (normalize_pow_vectors hc (VG.Proof.Ecdsa.AArch64.pPow_ok hc hsu hMu powerBound))
    fun v ⟨⟨kv,uv,invBound,invValue⟩,vv⟩ => ?_
  have hsv := hsu.of_keepRegs kv (by decide)
  rw [config_acc,config_n,config_prime] at invBound
  rw [config_acc,config_rz,config_n] at invValue
  have invValue := toM_pow_relabel config_prime invValue
  have exponentEq := congrArg (fun n : Nat => n-2) config_prime
  rw [exponentEq] at invValue
  change wordsVal v.mem base 2152 9<fieldPrime at invBound
  have invValue := toM_pow_relabel_base nine_base invValue
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by decide)
    (representation_from_memory hsv (d:=2152) (by decide) (by decide) invBound))
    fun t ⟨⟨fromValue,fromBound,kt,ot⟩,vt⟩ => ?_
  have fieldValue : Fin.ofNat fieldPrime (wordsVal t.mem base 2152 9)=
      Fin.ofNat fieldPrime (wordsVal s.mem base 1216 9)^(fieldPrime-2) := by
    rw [fromValue,fromMontValue_field invBound,invValue,toValue,toMontValue_field bound]
  have frame : Unch base normalizeInverseWrites s.mem t.mem := ou.unch.trans (uv.trans ot.unch)
  refine ⟨fromBound,fieldValue,frame,?_,kt.rd.trans (kv.rd.trans ku.rd),kt.wr.trans (kv.wr.trans ku.wr),
    kt.sp.trans (kv.sp.trans ku.sp),?_,?_,?_,?_,?_,?_⟩
  · exact (kt.gpr .x0 (by decide)).trans ((kv.gpr .x0 (by decide)).trans ((ku.gpr .x0 (by decide)).trans hs.x0))
  · exact (kt.gpr .x20 (by decide)).trans ((kv.gpr .x20 (by decide)).trans (ku.gpr .x20 (by decide)))
  · exact (kt.gpr .x26 (by decide)).trans ((kv.gpr .x26 (by decide)).trans (ku.gpr .x26 (by decide)))
  · exact (kt.gpr .x30 (by decide)).trans ((kv.gpr .x30 (by decide)).trans (ku.gpr .x30 (by decide)))
  · rw [vt,vv,vu]
  · rw [ot.wordsVal (by decide) (by decide),uv.wordsVal (by decide) (by decide),toValue]
  · intro r hr
    have choices : r=Reg.x27 ∨ r=Reg.x28 := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hr
    rcases choices with rfl|rfl
    all_goals exact (kt.gpr _ (by decide)).trans ((kv.gpr _ (by decide)).trans (ku.gpr _ (by decide)))

end VG.Proof.Weierstrass.AArch64.P521Native
