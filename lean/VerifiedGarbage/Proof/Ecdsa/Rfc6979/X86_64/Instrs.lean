module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Hash
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Proof.Framework.X86_64.Icall
public import VerifiedGarbage.Impl.Dispatch.X86_64

/-!
# Deterministic ECDSA on x86-64: the instructions of `sign`

For any hash function `P`, `sign` of its configuration keeps MXCSR's control
bits (`ctlC`: none of its instructions loads MXCSR, `core`'s neither, and the
streaming functions it calls indirectly keep them) and writes `rsp` only in
its frame's push and pop (`sign_fine`). Each block is built by functions of
the sizes (`padWord`, `copyN`, `loadBytes`, …), each of whose instructions,
whatever the sizes, is one of a few kinds that do neither (`ok`): so the
facts hold of every size at once, without evaluating the code.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64.Instrs

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Impl.Mgf1.X86_64 (initF updF finF ldFn)

/-- An instruction that neither loads MXCSR nor writes `rsp`. -/
def ok (i : Instr) : Bool := !loadsMxcsr i && !isa.writesSp i

/-- Code that keeps MXCSR's control bits (`ctlC`) and writes `rsp` only in
its frames' pushes and pops. -/
def Fine (c : Prog isa) : Prop := ctlC c = true ∧ c.all (fun i => !isa.writesSp i) = true

namespace Fine

theorem block {is : List Instr} (h : is.all ok = true) : Fine (.block is) := by
  refine ⟨?_, ?_⟩
  · show KList.all is _ = true
    rw [KList.all_eq]
    exact List.all_eq_true.mpr fun i hi => by
      have := List.all_eq_true.mp h i hi
      simp only [ok, Bool.and_eq_true] at this
      exact this.1
  · exact List.all_eq_true.mpr fun i hi => by
      have := List.all_eq_true.mp h i hi
      simp only [ok, Bool.and_eq_true] at this
      exact this.2

theorem seq {a b : Prog isa} (ha : Fine a) (hb : Fine b) : Fine (.seq a b) :=
  ⟨by simp only [ctlC, ha.1, hb.1, Bool.and_self], by simp only [Code.all, ha.2, hb.2, Bool.and_self]⟩

theorem ite {c : Cond} {a b : Prog isa} (ha : Fine a) (hb : Fine b) : Fine (.ite c a b) :=
  ⟨by simp only [ctlC, ha.1, hb.1, Bool.and_self], by simp only [Code.all, ha.2, hb.2, Bool.and_self]⟩

theorem loop {c : Cond} {b : Prog isa} (hb : Fine b) : Fine (.loop b c) := ⟨hb.1, hb.2⟩

theorem icall (n : Nat) : Fine (.icall n) := ⟨rfl, rfl⟩

/-- Code of none of whose instructions loads MXCSR keeps its control bits. -/
theorem ctlC_of_allInstrs : ∀ {c : Prog isa}, c.allInstrs (fun i => !loadsMxcsr i) = true → ctlC c = true
  | .block is, h => by
    show KList.all is _ = true
    rw [KList.all_eq]
    have : (Code.block is : Prog isa).allInstrs (fun i => !loadsMxcsr i) = is.all (fun i => !loadsMxcsr i) := by
      rw [Code.allInstrs_eq]; rfl
    rw [← this]; exact h
  | .seq a b, h => by
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [ctlC, ctlC_of_allInstrs h.1, ctlC_of_allInstrs h.2, Bool.and_self]
  | .ite _ a b, h => by
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [ctlC, ctlC_of_allInstrs h.1, ctlC_of_allInstrs h.2, Bool.and_self]
  | .loop b _, h => ctlC_of_allInstrs (c := b) h
  | .call _ b, h => ctlOk_of_ctlC (ctlC_of_allInstrs (c := b) h)
  | .icall _, h => by simp [Code.allInstrs, icallInstrs, loadsMxcsr] at h
  | .frame i b j, h => by
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [ctlC, h.1.1, h.2, ctlC_of_allInstrs h.1.2, Bool.and_self]

theorem call {n : String} {b : Prog isa} (hm : b.allInstrs (fun i => !loadsMxcsr i) = true)
    (hs : b.allInstrs (fun i => !isa.writesSp i) = true) : Fine (.call n b) :=
  ⟨ctlOk_of_ctlC (ctlC_of_allInstrs hm), Code.all_of_allInstrs (c := b) hs⟩

theorem frame {i j : Instr} {b : Prog isa} (hi : ok i = true) (hj : ok j = true) (hb : Fine b) :
    Fine (.frame i b j) := by
  simp only [ok, Bool.and_eq_true] at hi hj
  exact ⟨by simp only [ctlC, hi.1, hj.1, hb.1, Bool.and_self],
    by simp only [Code.all, hi.2, hj.2, hb.2, Bool.and_self]⟩

end Fine

/-! ## The blocks' pieces, at any sizes -/

/-- Each instruction the function `f` builds, for any index, is `ok`. -/
theorem all_flatMap {α : Type} {f : α → List Instr} (h : ∀ j, (f j).all ok = true) (l : List α) :
    (l.flatMap f).all ok = true := by
  rw [List.all_flatMap]; exact List.all_eq_true.mpr fun j _ => h j

theorem all_app {a b : List Instr} (ha : a.all ok = true) (hb : b.all ok = true) : (a ++ b).all ok = true := by
  rw [List.all_append, ha, hb]; rfl

theorem padBlock_ok (D B : Nat) (pad : BitVec 32) : (Cfg.padBlock D B pad).all ok = true :=
  all_flatMap (fun j => by unfold Cfg.padWord; split <;> rfl) _

theorem copyN_ok (k : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) : (Cfg.copyN k src so dst d).all ok = true :=
  all_flatMap (fun _ => rfl) _

theorem copyBytes_ok (len : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) :
    (Cfg.copyBytes len src so dst d).all ok = true :=
  all_app (copyN_ok _ _ _ _ _) (by split <;> rfl)

theorem zeroN_ok (k : Nat) (dst : Reg) (d : Nat) : (Cfg.zeroN k dst d).all ok = true := by
  unfold Cfg.zeroN; rw [List.all_map]; exact List.all_eq_true.mpr fun _ _ => rfl

theorem msg_ok (Q D b : Nat) (full wide : Bool) (ho : Nat) : (Cfg.msg Q D b full wide ho).all ok = true := by
  unfold Cfg.msg
  refine all_app (all_app (copyBytes_ok _ _ _ _ _) rfl) ?_
  split
  · split
    · exact all_app (all_app (all_app (copyBytes_ok _ _ _ _ _) rfl) (zeroN_ok _ _ _)) (copyBytes_ok _ _ _ _ _)
    · exact all_app (copyBytes_ok _ _ _ _ _) (copyBytes_ok _ _ _ _ _)
  · rfl

theorem msgPtrs_ok (wide : Bool) : (Cfg.msgPtrs wide).all ok = true := by
  unfold Cfg.msgPtrs; cases wide <;> rfl

theorem loadBytes_ok (len n o : Nat) (src : Reg) : (Impl.Weierstrass.X86_64.loadBytes len n o src).all ok = true :=
  all_flatMap (fun j => by split <;> [rfl; split <;> rfl]) _

theorem shrWords_ok (n o sh : Nat) : (Impl.Weierstrass.X86_64.shrWords n o sh).all ok = true :=
  all_flatMap (fun j => all_app (all_app rfl (by split <;> rfl)) rfl) _

theorem storeBytes_ok (len n : Nat) (dst : Reg) (d a : Nat) :
    (Impl.Weierstrass.X86_64.storeBytes len n dst d a).all ok = true :=
  all_flatMap (fun j => by
    split
    · rfl
    · exact all_app rfl (all_flatMap (fun i => all_app (all_app rfl (by split <;> rfl)) rfl) _)) _

section
variable (c : Cfg)

theorem conv_ok (o s : Nat) : (c.conv o s).all ok = true :=
  all_app (all_app (all_app (all_app rfl (loadBytes_ok _ _ _ _)) (shrWords_ok _ _ _)) rfl) (storeBytes_ok _ _ _ _ _)

theorem coreDigest_ok : c.coreDigest.all ok = true :=
  all_app (all_app (all_app rfl (zeroN_ok _ _ _)) (copyBytes_ok _ _ _ _ _)) (by split <;> [rfl; exact (conv_ok c) _ _])

theorem digestPtr_ok : c.digestPtr.all ok = true := by
  unfold Cfg.digestPtr; split <;> rfl

theorem reduce_ok : c.reduce.all ok = true :=
  all_app (all_app (all_flatMap (fun j => all_app (by unfold Cfg.loadWord; split <;> [rfl; split <;> rfl])
    rfl) _) rfl) (all_flatMap (fun _ => rfl) _)

theorem initKV_ok : Cfg.initKV.all ok = true := all_app rfl (all_flatMap (fun _ => rfl) _)

theorem coreArgs_ok : c.coreArgs.all ok = true := by
  unfold Cfg.coreArgs; split <;> rfl

theorem wipe_ok : Cfg.wipe.all ok = true := by
  unfold Cfg.wipe
  refine all_app (all_app rfl ?_) ?_ <;> (rw [List.all_map]; exact List.all_eq_true.mpr fun _ _ => rfl)

theorem keyed_fine (st : Nat) (pad : BitVec 32) : Fine (c.keyed st pad) :=
  .seq (.block rfl) (.seq (.seq (.block rfl) (.icall _)) (.seq (.block rfl)
    (.seq (.block (all_app (padBlock_ok _ _ _) rfl)) (.seq (.block rfl) (.icall _)))))

theorem hmac_fine {dataA : List Instr} (hd : dataA.all ok = true) (len dst : Nat) : Fine (c.hmac dataA len dst) := by
  have hu : ∀ (st cnt : Nat) (a : List Instr), a.all ok = true → ∀ l, (Cfg.updArgs st cnt a l).all ok = true :=
    fun _ _ _ h _ => all_app (all_app (all_app rfl h) rfl) rfl
  have hf : ∀ (st cnt : Nat) (a : List Instr), a.all ok = true → (Cfg.finArgs st cnt a).all ok = true :=
    fun _ _ _ h => all_app (all_app rfl h) rfl
  have hU : Fine (updF fFn) := .seq (.block rfl) (.icall _)
  have hF : Fine (finF fFn) := .seq (.block rfl) (.icall _)
  exact .seq ((keyed_fine c) _ _) (.seq ((keyed_fine c) _ _) (.seq (.block (hu _ _ _ hd _)) (.seq hU
    (.seq (.block (hf _ _ _ rfl)) (.seq hF (.seq (.block (hu _ _ _ rfl _)) (.seq hU
      (.seq (.block (hf _ _ _ rfl)) hF))))))))

theorem hmacV_fine : Fine c.hmacV := (hmac_fine c) rfl _ _

theorem rekeyFull_fine (b : Nat) : Fine (c.rekeyFull b) :=
  .seq (.block (msgPtrs_ok _)) (.seq (.block (msg_ok _ _ _ _ _ _)) (.seq ((hmac_fine c) rfl _ _) (hmacV_fine c)))

theorem rekey_fine : Fine c.rekey :=
  .seq (.block (msgPtrs_ok _)) (.seq (.block (msg_ok _ _ _ _ _ _)) (.seq ((hmac_fine c) rfl _ _) (hmacV_fine c)))

theorem candStep_fine (i : Nat) : Fine (c.candStep i) := .seq (hmacV_fine c) (.block (copyBytes_ok _ _ _ _ _))

theorem candSteps_fine : ∀ i k, Fine (c.candSteps i k)
  | _, 0 => .block rfl
  | i, 1 => (candStep_fine c) i
  | i, k + 2 => .seq ((candStep_fine c) i) (candSteps_fine (i + 1) (k + 1))

theorem cand_fine : Fine c.cand := by
  unfold Cfg.cand
  split
  · split
    · exact (candSteps_fine c) _ _
    · exact .seq ((candSteps_fine c) _ _) (.seq (.block rfl) (.block ((conv_ok c) _ _)))
  · exact (hmacV_fine c)

theorem tryOne_fine (hm : c.coreC.allInstrs (fun i => !loadsMxcsr i) = true)
    (hs : c.coreC.allInstrs (fun i => !isa.writesSp i) = true) : Fine c.tryOne :=
  .seq (cand_fine c) (.seq (.block ((coreArgs_ok c))) (.seq (.call hm hs) (.seq (.block rfl)
    (.ite (.seq (rekey_fine c) (.block rfl)) (.block rfl)))))

theorem body_fine (hm : c.coreC.allInstrs (fun i => !loadsMxcsr i) = true)
    (hs : c.coreC.allInstrs (fun i => !isa.writesSp i) = true) : Fine c.body :=
  .seq (.block (digestPtr_ok c)) (.seq (.block (all_app (by split <;> [exact (coreDigest_ok c); exact (reduce_ok c)])
    initKV_ok)) (.seq ((rekeyFull_fine c) 0) (.seq ((rekeyFull_fine c) 1) (.seq (.block rfl)
    (.seq (.loop ((tryOne_fine c) hm hs)) (.block wipe_ok))))))

/-- `sign` of any configuration whose `core` neither loads MXCSR nor writes `rsp`. -/
theorem sign_fine (hm : c.coreC.allInstrs (fun i => !loadsMxcsr i) = true)
    (hs : c.coreC.allInstrs (fun i => !isa.writesSp i) = true) : Fine c.sign :=
  .frame rfl rfl ((body_fine c) hm hs)

end

/-- A dispatch among cases that are. -/
theorem chain_fine : ∀ cs : List (Nat × Prog isa), (∀ c ∈ cs, Fine c.2) → Fine (Impl.Dispatch.X86_64.chain cs)
  | [], _ => .block rfl
  | [_], h => h _ List.mem_cons_self
  | _ :: c' :: cs, h =>
    .seq (.block rfl) (.ite (h _ List.mem_cons_self) (chain_fine (c' :: cs) fun c hc => h c (List.mem_cons_of_mem _ hc)))

/-- `vg_ecdsa_<curve>_rfc6979_sign`, whose `core` neither loads MXCSR nor writes `rsp`. -/
theorem signAny_fine (E : Curve) (hm : E.coreC.allInstrs (fun i => !loadsMxcsr i) = true)
    (hs : E.coreC.allInstrs (fun i => !isa.writesSp i) = true) : Fine (signAny E) :=
  .seq (.block rfl) (.seq (.block rfl) (chain_fine _ fun c hc => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hc
    exact sign_fine _ hm hs))

theorem cfgOf_fine (P : RfcHash) : Fine (cfgOf P).sign := sign_fine (cfgOf P) P.R.coreMx P.R.coreSp

end VG.Proof.Ecdsa.Rfc6979.X86_64.Instrs
