module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Table
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Table
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# Deterministic ECDSA on 32-bit ARM: the contract with the hash function as a table

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/TableSpec.lean`):
`TableInstance.signContract`, with the tables of `vs` for `hash`, the
curve's tables of constants and `stackT` bytes of stack, implies `tabK`
(`tab_implies`): the table `hash` points to is one of `vs`', whose words
give the contract the proof of its hash function's code is written against
(`preW_of`); its hash function is the one the table names, so the results
agree; and two runs whose public data agree take the same table.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.HashTable.Arm (TVar tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf hashAt_tableOf)
open VG.Proof.RsaOaep.Arm (tA)

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List TVar}

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specK (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64))) (vs : List TVar) :
    Contract isa :=
  T.signContract ((Arm.abi.withConsts cs).withTables T.signSig [("hash", tables vs)]) stackT

theorem names_eq (vs : List TVar) : ((List.map (fun x => x.fns) (tables vs)).flatten.append []) = names vs :=
  List.append_nil _

/-- The table `hash` points to holds `w`'s. -/
abbrev HeldW (w : TVar) (s : State) : Prop :=
  Abi.tableHeld 32 s.mem (State.addr (stackArg s 1)) (FnTable.words isa s (tableOf w))

/-- What the table of `w` gives the contract on entry. -/
theorem tab_of (hc : Coh vs) {w : TVar} (hv : w ∈ vs) {s : State} (hp : (stackArg s 1).toNat + 20 ≤ 2 ^ 32)
    (hpw : (names vs).Pairwise fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64)
    (hh : HeldW w s) :
    tabFacts w.g.H (fnsOf vs) s ∧
      s.mem.readW (tA (stackArg s 1) 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.g.G) ∧
      Spec.HashTable.hashAt 32 s.mem (State.addr (stackArg s 1)) = some w.g.G := by
  obtain ⟨hm, hi, -⟩ := held_tableOf hp hh
  have ho := tabOK_of hc hpw hv
  exact ⟨⟨⟨ho.i, ho.u, ho.f⟩, hm⟩, hi, hashAt_tableOf hp hi⟩

/-- Unfolds the contract's precondition at `h`. -/
macro "tab_pre" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val, Abi.withConsts, stackT] at $h:ident
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val, Abi.withConsts, stackT] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left', names_eq] at $h:ident))

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract on entry. -/
def PreFacts (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW w s) ∧ ∀ w ∈ vs, HeldW w s → PreW R T vs w s

theorem tablesOk_of {cs : List (String × List (BitVec 64))} {s : State} {ws : List Region}
    (held : Abi.constsHeld s.mem (fun n => State.addr (s.syms n)) cs)
    (fit : ∀ t ∈ Abi.constRegions (fun n => State.addr (s.syms n)) cs, t.base.toNat + t.len ≤ 2 ^ 32 ∧
      ∀ r ∈ ws, t.Disjoint r)
    (al : ∀ t ∈ Abi.constRegions (fun n => State.addr (s.syms n)) cs, t.base.toNat % 64 = 0) :
    TablesOk cs s.syms s.mem ws := fun c hc => by
  have ht := List.mem_map_of_mem (f := fun c => (⟨State.addr (s.syms c.1), 8 * c.2.length⟩ : Region)) hc
  refine ⟨held c hc, ?_, (fit _ ht).2, al _ ht⟩
  have := (fit _ ht).1
  rwa [toNat_addr] at this

/-- The precondition. -/
theorem pre_facts (hsw : T.scratchWords = 1024) (hO : OK vs) (cs : List (String × List (BitVec 64)))
    (hcs : R.coreConsts = cs) {s : State} (h : (specK T cs vs).pre s) : PreFacts R T vs s := by
  cases cs with
  | nil =>
    tab_pre at h
    obtain ⟨hsp, na, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, od, og, oc, ot, oa, dc, gc, ct, ca, ko, kd, kg, kc, kt, ka,
      no, nd, ng, nc, nt, hH⟩ := h
    obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
    refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hh => ?_⟩
    obtain ⟨hF, hi, hG⟩ := tab_of hO.1 hv nt hpw hh
    have hlen : (s.gpr .r3).toNat = w.g.H.D := (hH _ hG).1.trans w.g.glen
    rw [hlen] at og gc kg ng hrd
    simp only [hsw, Nat.reduceMul] at hwr oc dc gc ct ca kc nc
    refine ⟨⟨?_, hwr, od, og, oc, ot, oa, dc, gc, ct, ca, ko, kd, kg, kc, kt, ka, no, nd, ng, nc, nt, na, hsp,
      fun c hc => absurd hc (by rw [hcs]; simp), hF⟩, hi⟩
    rw [hrd, hcs]; rfl
  | cons c cs =>
    tab_pre at h
    obtain ⟨hsp, na, hdrop, held, fit, al, ⟨Tb, hTb, hheld⟩, hpw, htake, hwr, od, og, oc, ot, oa, dc, gc, ct, ca,
      ko, kd, kg, kc, kt, ka, no, nd, ng, nc, nt, hH⟩ := h
    obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
    refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hh => ?_⟩
    obtain ⟨hF, hi, hG⟩ := tab_of hO.1 hv nt hpw hh
    have hlen : (s.gpr .r3).toNat = w.g.H.D := (hH _ hG).1.trans w.g.glen
    rw [hlen] at og gc kg ng htake
    simp only [hsw, Nat.reduceMul] at hwr oc dc gc ct ca kc nc
    refine ⟨⟨?_, hwr, od, og, oc, ot, oa, dc, gc, ct, ca, ko, kd, kg, kc, kt, ka, no, nd, ng, nc, nt, na, hsp,
      ?_, hF⟩, hi⟩
    · rw [hcs, ← List.take_append_drop (s.rd.length - (cs.length + 1)) s.rd, htake, hdrop]; rfl
    · rw [hcs]
      refine tablesOk_of held (fun t ht => ⟨(fit t ht).1, fun r hr => ?_⟩) al
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (fit t ht).2.1 _ (by rw [hwr]; exact List.mem_cons_self)
      · exact (fit t ht).2.1 _ (by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      · exact (fit t ht).2.2

/-- The postcondition: the hash function the table names is its variant's. -/
theorem post_of {s s' : State} (hk : (tabK R T vs).pre s) (hp : (tabK R T vs).post s s') :
    ∀ (H : Spec.Mgf1.Hash) (F : Spec.Hmac.HashFunction),
      Spec.HashTable.hashAt 32 s.mem (State.addr (stackArg s 1)) = some H → Spec.Ecdsa.Rfc6979.hmacOf H = some F →
        match (T.result H F s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2))).fst with
        | some rs => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
            Spec.Ecdsa.bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * T.ecdsa.curve.len) =
              Spec.Ecdsa.encode T.ecdsa.curve rs
        | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
            Spec.Ecdsa.bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * T.ecdsa.curve.len) =
              List.replicate (2 * T.ecdsa.curve.len) 0 := by
  intro H F hH hF
  obtain ⟨w, hv, hw, hpre⟩ := hk
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf hpre.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpre.2))
  obtain rfl := Option.some.inj (hF.symm.trans hw.hmac)
  exact hp w hv hw hpre

/-- What the public data say. -/
def PubFacts (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) (s₁ s₂ : State) : Prop :=
  (∀ w ∈ vs, HeldW w s₁ ↔ HeldW w s₂) ∧ s₁.sp = s₂.sp ∧ (∀ r ∈ [Reg.r0, .r1, .r2], s₁.gpr r = s₂.gpr r) ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    T.tried 32 s₁.mem (State.addr (s₁.gpr .r1)) (State.addr (s₁.gpr .r2)) (State.addr (stackArg s₁ 1)) =
      T.tried 32 s₂.mem (State.addr (s₂.gpr .r1)) (State.addr (s₂.gpr .r2)) (State.addr (stackArg s₂ 1)) ∧
    (∀ c ∈ R.coreConsts, s₁.syms c.1 = s₂.syms c.1) ∧ ∀ n ∈ names vs, s₁.syms n = s₂.syms n

theorem tried_eq {w : TVar} (hw : WOk w) {s : State} (hp : PreW R T vs w s) :
    T.tried 32 s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) (State.addr (stackArg s 1)) =
      ((instOf T w).result s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2))).2 := by
  simp only [Spec.Ecdsa.Rfc6979.TableInstance.tried,
    hashAt_tableOf hp.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp.2, hw.hmac, tresult_eq]

/-- The public data of `tabK`, from the facts. -/
theorem pub_of (hO : OK vs) {s₁ s₂ : State} (h₁ : PreFacts R T vs s₁) (h₂ : PreFacts R T vs s₂)
    (hp : PubFacts R T vs s₁ s₂) : (tabK R T vs).pub s₁ s₂ := by
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  obtain ⟨hh', hsp, hg, ha0, ha1, ht, hc, hn⟩ := hp
  have p₁ := f₁ w hv hh
  have p₂ := h₂.2 w hv ((hh' w hv).mp hh)
  have hw := hO.2.2.2 w hv
  refine ⟨w, hv, hw, p₁, p₂, hsp, hg .r0 (by simp), hg .r1 (by simp), hg .r2 (by simp), ha0, ha1, ?_, hc, hn⟩
  rw [← tried_eq hw p₁, ← tried_eq hw p₂, ht]

/-- Unfolds the contract's public data at `h`. -/
macro "tab_pub" " at " h:ident : tactic => `(tactic| (
  sig_pub [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val, Abi.withConsts, stackT, String.reduceEq, ↓reduceIte, Option.map_some,
      List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', forall_eq', names_eq] at $h:ident))

/-- The public data. -/
theorem pub_facts (cs : List (String × List (BitVec 64))) (hcs : R.coreConsts = cs) {s₁ s₂ : State}
    (h : (specK T cs vs).pub s₁ s₂) : PubFacts R T vs s₁ s₂ := by
  cases cs with
  | nil =>
    tab_pub at h
    obtain ⟨hsp, hn, hT, htr, e₀, e₁, e₂, -, e₄, e₅⟩ := h
    refine ⟨fun w hv => hT _ _ rfl rfl _ (List.mem_map_of_mem hv), hsp, fun r hr => ?_, e₄, e₅,
      (List.cons.inj htr).1, fun c hc => absurd hc (by rw [hcs]; simp), hn⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  | cons c cs =>
    tab_pub at h
    obtain ⟨hsp, hc₀, hcs', hn, hT, htr, e₀, e₁, e₂, -, e₄, e₅⟩ := h
    refine ⟨fun w hv => hT _ _ rfl rfl _ (List.mem_map_of_mem hv), hsp, fun r hr => ?_, e₄, e₅,
      (List.cons.inj htr).1, fun c' hc' => ?_, hn⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> with_reducible assumption
    · rw [hcs] at hc'
      rcases List.mem_cons.mp hc' with rfl | h
      · exact hc₀
      · exact hcs' _ h

theorem PreFacts.pre (hO : OK vs) {s : State} (h : PreFacts R T vs s) : (tabK R T vs).pre s :=
  let ⟨⟨w, hv, hh⟩, f⟩ := h; ⟨w, hv, hO.2.2.2 w hv, f w hv hh⟩

/-- `TableInstance.signContract` with the tables of `vs` implies `tabK`. -/
theorem tab_implies (hsw : T.scratchWords = 1024) (hO : OK vs)
    (hsat : ∃ s, (specK T R.coreConsts vs).pre s) : (tabK R T vs).Implies (specK T R.coreConsts vs) := by
  generalize hcs : R.coreConsts = cs at hsat ⊢
  have facts : ∀ s, (specK T cs vs).pre s → PreFacts R T vs s := fun s h => pre_facts hsw hO cs hcs h
  refine ⟨fun s h => (facts s h).pre hO, fun s s' h hp => ?_,
    fun s₁ s₂ h₁ h₂ hp => pub_of hO (facts _ h₁) (facts _ h₂) (pub_facts cs hcs hp), hsat⟩
  have hk := (facts s h).pre hO
  cases cs
  all_goals
    sig_post [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val, Abi.withConsts, stackT]
    exact post_of hk hp

/-- `vg_ecdsa_<curve>_sign`, with the tables of `vs`, meets
`TableInstance.signContract` (given a state that meets it). -/
theorem signT_verified (hC : CurveT R T) (hsw : T.scratchWords = 1024) (hO : OK vs)
    (hsat : ∃ s, (specK T R.coreConsts vs).pre s) :
    Verified Arm.target (signCode R T.tries vs) (specK T R.coreConsts vs) :=
  Verified.of_correct (fun _ h => let ⟨t, s', he, hp⟩ := signT_ok hC h; ⟨t, s', he, hp⟩)
    (signT_ct hC hO.2.2.2) (tab_implies hsw hO hsat)

end VG.Proof.Ecdsa.Rfc6979.Arm
