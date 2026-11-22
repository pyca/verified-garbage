module

public import VerifiedGarbage.Proof.HashTable.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.HashTable.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Table
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Table

/-! ### `Ecdsa.Rfc6979.Arm.TableSpec`, which only this module used -/

section

/-!
# Deterministic ECDSA on 32-bit ARM: the contract with the hash function as a table

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/TableSat.lean`):
`TableInstance.signContract`, with the tables of `vs` for `hmac`, the
curve's tables of constants and `stackT` bytes of stack, implies `tabK`
(`tab_implies`): the table `hmac` points to is one of `vs`', whose words
give the contract the proof of the body is written against (`preW_of`); its
hash function is the one the table names, so the results agree; and two
runs whose public data agree take the same table.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.HmacTable.Arm (HVar vars tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf
  hashAt_tableOf tA)

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specK (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64))) (vs : List HVar) :
    Contract isa :=
  T.signContract ((Arm.abi.withConsts cs).withTables T.signSig [("hmac", tables vs)]) stackT

theorem tableRegion_eq (p : Addr) : Sig.tableRegion 32 p 6 = ⟨p, 24⟩ := rfl

theorem names_eq (vs : List HVar) : (List.map (fun x => x.fns) (tables vs)).flatten = names vs := rfl

theorem argAddr0 (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar}

/-- The facts of the contract with the table of `w`, on entry. -/
theorem preW_of {w : HVar} (hv : w ∈ vs) (hc : Coh vs) {cs : List (String × List (BitVec 64))} {s : State}
    (hcs : R.coreConsts = cs)
    (hsp : 544 ≤ s.sp.toNat) (hsp8 : s.sp.toNat + 8 ≤ 2 ^ 32)
    (hrd : s.rd = [⟨State.addr (s.gpr .r1), T.ecdsa.curve.len⟩, ⟨State.addr (s.gpr .r2), w.F.H.D⟩,
      ⟨State.addr (stackArg s 1), 24⟩, ⟨State.addr s.sp, 8⟩] ++ Abi.constRegions (fun n => State.addr (s.syms n)) cs)
    (hwr : s.wr = [⟨State.addr (s.gpr .r0), 2 * T.ecdsa.curve.len⟩, ⟨State.addr (stackArg s 0), 8192⟩])
    (od : Region.Disjoint ⟨State.addr (s.gpr .r0), 2 * T.ecdsa.curve.len⟩ ⟨State.addr (s.gpr .r1), T.ecdsa.curve.len⟩)
    (og : Region.Disjoint ⟨State.addr (s.gpr .r0), 2 * T.ecdsa.curve.len⟩ ⟨State.addr (s.gpr .r2), w.F.H.D⟩)
    (oc : Region.Disjoint ⟨State.addr (s.gpr .r0), 2 * T.ecdsa.curve.len⟩ ⟨State.addr (stackArg s 0), 8192⟩)
    (ot : Region.Disjoint ⟨State.addr (s.gpr .r0), 2 * T.ecdsa.curve.len⟩ ⟨State.addr (stackArg s 1), 24⟩)
    (oa : Region.Disjoint ⟨State.addr (s.gpr .r0), 2 * T.ecdsa.curve.len⟩ ⟨State.addr s.sp, 8⟩)
    (dc : Region.Disjoint ⟨State.addr (s.gpr .r1), T.ecdsa.curve.len⟩ ⟨State.addr (stackArg s 0), 8192⟩)
    (gc : Region.Disjoint ⟨State.addr (s.gpr .r2), w.F.H.D⟩ ⟨State.addr (stackArg s 0), 8192⟩)
    (ct : Region.Disjoint ⟨State.addr (stackArg s 0), 8192⟩ ⟨State.addr (stackArg s 1), 24⟩)
    (ca : Region.Disjoint ⟨State.addr (stackArg s 0), 8192⟩ ⟨State.addr s.sp, 8⟩)
    (ko : Region.Disjoint (stkR s.sp 544) ⟨State.addr (s.gpr .r0), 2 * T.ecdsa.curve.len⟩)
    (kd : Region.Disjoint (stkR s.sp 544) ⟨State.addr (s.gpr .r1), T.ecdsa.curve.len⟩)
    (kg : Region.Disjoint (stkR s.sp 544) ⟨State.addr (s.gpr .r2), w.F.H.D⟩)
    (kc : Region.Disjoint (stkR s.sp 544) ⟨State.addr (stackArg s 0), 8192⟩)
    (kt : Region.Disjoint (stkR s.sp 544) ⟨State.addr (stackArg s 1), 24⟩)
    (no : (s.gpr .r0).toNat + 2 * T.ecdsa.curve.len ≤ 2 ^ 32) (nd : (s.gpr .r1).toNat + T.ecdsa.curve.len ≤ 2 ^ 32)
    (ng : (s.gpr .r2).toNat + w.F.H.D ≤ 2 ^ 32) (nc : (stackArg s 0).toNat + 8192 ≤ 2 ^ 32)
    (nt : (stackArg s 1).toNat + 24 ≤ 2 ^ 32)
    (htab : TablesOk cs s.syms s.mem [⟨State.addr (s.gpr .r0), 2 * T.ecdsa.curve.len⟩,
      ⟨State.addr (stackArg s 0), 8192⟩, stkR s.sp 544])
    (hheld : Abi.tableHeld 32 s.mem (State.addr (stackArg s 1)) (FnTable.words isa s (tableOf w)))
    (hpw : (names vs).Pairwise fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) :
    PreW R T vs w s := by
  have hh := held_tableOf nt hheld
  subst hcs
  exact ⟨⟨hrd, hwr, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp, hsp8, oa.symm, ca.symm, nt,
    ot.symm, ct.symm, kt.symm, htab, tabOK_of hc hpw hv, hh.1, hh.2.2.1, hh.2.2.2⟩, hh.2.1⟩

/-- The table `hmac` points to holds `w`'s. -/
abbrev HeldW (w : HVar) (s : State) : Prop :=
  Abi.tableHeld 32 s.mem (State.addr (stackArg s 1)) (FnTable.words isa s (tableOf w))

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract on entry. -/
def PreFacts (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW w s) ∧ ∀ w ∈ vs, HeldW w s → PreW R T vs w s

/-- The constants' facts, as the contract states them. -/
theorem tables_of {cs : List (String × List (BitVec 64))} {s : State} {ws : List Region} {stk : Region}
    (held : Abi.constsHeld s.mem (fun n => State.addr (s.syms n)) cs)
    (fit : ∀ t ∈ Abi.constRegions (fun n => State.addr (s.syms n)) cs, t.base.toNat + t.len ≤ 2 ^ 32 ∧
      (∀ r ∈ ws, t.Disjoint r) ∧ t.Disjoint stk)
    (al : ∀ t ∈ Abi.constRegions (fun n => State.addr (s.syms n)) cs, t.base.toNat % 64 = 0) :
    TablesOk cs s.syms s.mem (ws ++ [stk]) := fun c hc => by
  have hm : (⟨State.addr (s.syms c.1), 8 * c.2.length⟩ : Region) ∈ Abi.constRegions (fun n => State.addr (s.syms n)) cs :=
    List.mem_map_of_mem (f := fun c => (⟨State.addr (s.syms c.1), 8 * c.2.length⟩ : Region)) hc
  obtain ⟨h₁, h₂, h₃⟩ := fit _ hm
  refine ⟨held c hc, by simpa only [toNat_addr] using h₁, fun r hr => ?_, al _ hm⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact h₂ r hr
  · rw [List.mem_singleton] at hr; subst hr; exact h₃

/-- The precondition, with tables of constants. -/
theorem pre_cons (hsw : T.scratchWords = 1024) (hO : OK vs) {c : String × List (BitVec 64)}
    {cs : List (String × List (BitVec 64))} (hcs : R.coreConsts = c :: cs) {s : State}
    (h : (specK T (c :: cs) vs).pre s) : PreFacts R T vs s := by
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Abi.withConsts, stackBelow, stackT, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, hsw, tableRegion_eq, names_eq, argAddr0] at h
  obtain ⟨hsp, hsp8, hdrop, held, fit, al, ⟨Tb, hTb, hheld⟩, hpw, htake, hwr, od, og, oc, ot, oa, dc, gc, ct, ca,
    ko, kd, kg, kc, kt, -, no, nd, ng, nc, nt, hH⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf nt hheld
  have hlen : (s.gpr .r3).toNat = w.F.H.D := (hH _ (hashAt_tableOf nt hh.2.1)).1.trans w.glen
  rw [hlen] at og gc kg ng htake
  rw [hsw] at hwr oc dc gc ct ca kc nc
  rw [List.append_eq, List.append_nil] at hpw
  refine preW_of hv hO.1 hcs hsp hsp8 ?_ hwr od og oc ot oa dc gc ct ca ko kd kg kc kt no nd ng nc nt ?_ hheld hpw
  · rw [← List.take_append_drop (s.rd.length - (cs.length + 1)) s.rd, htake, hdrop]; rfl
  · rw [hwr] at fit
    exact tables_of (ws := [_, _]) held fit al

/-- The precondition, without tables of constants. -/
theorem pre_nil (hsw : T.scratchWords = 1024) (hO : OK vs) (hcs : R.coreConsts = []) {s : State}
    (h : (specK T [] vs).pre s) : PreFacts R T vs s := by
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Abi.withConsts, stackBelow, stackT, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, hsw, tableRegion_eq, names_eq, argAddr0] at h
  obtain ⟨hsp, hsp8, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, od, og, oc, ot, oa, dc, gc, ct, ca,
    ko, kd, kg, kc, kt, -, no, nd, ng, nc, nt, hH⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf nt hheld
  have hlen : (s.gpr .r3).toNat = w.F.H.D := (hH _ (hashAt_tableOf nt hh.2.1)).1.trans w.glen
  rw [hlen] at og gc kg ng hrd
  rw [hsw] at hwr oc dc gc ct ca kc nc
  rw [List.append_eq, List.append_nil] at hpw
  refine preW_of hv hO.1 hcs hsp hsp8 (by rw [hrd]; rfl) hwr od og oc ot oa dc gc ct ca ko kd kg kc kt no nd ng nc nt
    (fun c hc => absurd hc List.not_mem_nil) hheld hpw

theorem PreW.nt {w : HVar} {s : State} (h : PreW R T vs w s) : (stackArg s 1).toNat + 24 ≤ 2 ^ 32 :=
  h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The postcondition: the hash function the table names is its own. -/
theorem post_of {s s' : State} (hk : (tabK R T vs).pre s) (hp : (tabK R T vs).post s s') :
    ∀ (H : Spec.Mgf1.Hash) (F : Spec.Hmac.HashFunction),
      Spec.HmacTable.hashAt 32 s.mem (State.addr (stackArg s 1)) = some H → Spec.HmacTable.hmacOf H = some F →
        match (T.result H F s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2))).fst with
        | some rs => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
            Spec.Ecdsa.bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * T.ecdsa.curve.len) =
              Spec.Ecdsa.encode T.ecdsa.curve rs
        | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
            Spec.Ecdsa.bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * T.ecdsa.curve.len) =
              List.replicate (2 * T.ecdsa.curve.len) 0 := by
  intro H F hH hF
  obtain ⟨w, hv, hw, hpre⟩ := hk
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf hpre.nt hpre.2))
  obtain rfl := Option.some.inj (hF.symm.trans w.hmac)
  exact hp w hv hw hpre

/-- What the public data say. -/
def PubFacts (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) (s₁ s₂ : State) : Prop :=
  (∀ w ∈ vs, HeldW w s₁ ↔ HeldW w s₂) ∧ s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    T.tried 32 s₁.mem (State.addr (s₁.gpr .r1)) (State.addr (s₁.gpr .r2)) (State.addr (stackArg s₁ 1)) =
      T.tried 32 s₂.mem (State.addr (s₂.gpr .r1)) (State.addr (s₂.gpr .r2)) (State.addr (stackArg s₂ 1)) ∧
    (∀ c ∈ R.coreConsts, s₁.syms c.1 = s₂.syms c.1) ∧ ∀ n ∈ names vs, s₁.syms n = s₂.syms n

theorem tried_eq {w : HVar} {s : State} (hp : PreW R T vs w s) :
    T.tried 32 s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) (State.addr (stackArg s 1)) =
      ((instOf T w).result s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2))).2 := by
  simp only [Spec.Ecdsa.Rfc6979.TableInstance.tried, hashAt_tableOf hp.nt hp.2, w.hmac, tresult_eq]

/-- The public data of `tabK`, from the facts. -/
theorem pub_of (hO : OK vs) {s₁ s₂ : State} (h₁ : PreFacts R T vs s₁) (h₂ : PreFacts R T vs s₂)
    (hp : PubFacts R T vs s₁ s₂) : (tabK R T vs).pub s₁ s₂ := by
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  obtain ⟨hh', hsp, h0, h1, h2, ha0, ha1, ht, hc, hn⟩ := hp
  have p₁ := f₁ w hv hh
  have p₂ := h₂.2 w hv ((hh' w hv).mp hh)
  refine ⟨w, hv, hO.2 w hv, p₁, p₂, hsp, h0, h1, h2, ha0, ha1, ?_, hc, hn⟩
  show ((instOf T w).result s₁.mem (State.addr (s₁.gpr .r1)) (State.addr (s₁.gpr .r2))).2 =
    ((instOf T w).result s₂.mem (State.addr (s₂.gpr .r1)) (State.addr (s₂.gpr .r2))).2
  rw [← tried_eq p₁, ← tried_eq p₂, ht]

/-- The public data, with tables of constants. -/
theorem pub_cons {c : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    (hcs : R.coreConsts = c :: cs) {s₁ s₂ : State}
    (h : (specK T (c :: cs) vs).pub s₁ s₂) : PubFacts R T vs s₁ s₂ := by
  sig_pub [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Abi.withConsts, stackBelow, stackT, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, tableRegion_eq, names_eq, argAddr0] at h
  obtain ⟨hsp, hc₀, hcs', hn, hT, htr, h0, h1, h2, -, ha0, ha1⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  refine ⟨fun w hv => hT _ _ rfl rfl _ (List.mem_map_of_mem hv), hsp, h0, h1, h2, ha0, ha1, (List.cons.inj htr).1,
    fun c' hc' => ?_, hn⟩
  rw [hcs] at hc'
  rcases List.mem_cons.mp hc' with rfl | h
  · exact hc₀
  · exact hcs' _ h

/-- The public data, without tables of constants. -/
theorem pub_nil (hcs : R.coreConsts = []) {s₁ s₂ : State}
    (h : (specK T [] vs).pub s₁ s₂) : PubFacts R T vs s₁ s₂ := by
  sig_pub [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Abi.withConsts, stackBelow, stackT, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, tableRegion_eq, names_eq, argAddr0] at h
  obtain ⟨hsp, hn, hT, htr, h0, h1, h2, -, ha0, ha1⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  exact ⟨fun w hv => hT _ _ rfl rfl _ (List.mem_map_of_mem hv), hsp, h0, h1, h2, ha0, ha1, (List.cons.inj htr).1,
    fun c' hc' => absurd hc' (by rw [hcs]; exact List.not_mem_nil), hn⟩

theorem PreFacts.pre (hO : OK vs) {s : State} (h : PreFacts R T vs s) : (tabK R T vs).pre s :=
  let ⟨⟨w, hv, hh⟩, f⟩ := h; ⟨w, hv, hO.2 w hv, f w hv hh⟩

/-- `TableInstance.signContract` with the tables of `vs` implies `tabK`. -/
theorem tab_implies (hsw : T.scratchWords = 1024) (hO : OK vs)
    (hsat : ∃ s, (specK T R.coreConsts vs).pre s) : (tabK R T vs).Implies (specK T R.coreConsts vs) := by
  generalize hcs : R.coreConsts = cs at hsat ⊢
  have facts : ∀ s, (specK T cs vs).pre s → PreFacts R T vs s := fun s h => by
    cases cs with
    | nil => exact pre_nil hsw hO hcs h
    | cons c cs => exact pre_cons hsw hO hcs h
  have pubs : ∀ s₁ s₂, (specK T cs vs).pub s₁ s₂ → PubFacts R T vs s₁ s₂ := fun s₁ s₂ h => by
    cases cs with
    | nil => exact pub_nil hcs h
    | cons c cs => exact pub_cons hcs h
  refine ⟨fun s h => (facts s h).pre hO, fun s s' h hp => ?_,
    fun s₁ s₂ h₁ h₂ hp => pub_of hO (facts _ h₁) (facts _ h₂) (pubs _ _ hp), hsat⟩
  have hk := (facts s h).pre hO
  cases cs
  all_goals
    sig_post [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
      Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Abi.withConsts, stackBelow, stackT, String.reduceEq,
      Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
      List.append_nil, tableRegion_eq, names_eq, argAddr0]
    exact post_of hk hp

/-- `vg_ecdsa_<curve>_sign`, with the tables of `vs`, meets
`TableInstance.signContract` (given a state that meets it). -/
theorem signT_verified (hC : CurveT R T) (hsw : T.scratchWords = 1024) (hO : OK vs)
    (hsat : ∃ s, (specK T R.coreConsts vs).pre s) :
    Verified Arm.target (signCodeT R T.tries vs) (specK T R.coreConsts vs) :=
  Verified.of_correct (fun _ h => signT_ok hC h) (signT_ct hC) (tab_implies hsw hO hsat)

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end

/-!
# Deterministic ECDSA on 32-bit ARM: the contract with the table is satisfiable

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/TableSat.lean`): a state meeting
`TableInstance.signContract` with the tables of `vs` (`satT`): the buffers
at fixed addresses, the stack arguments at `0x9000`, the table of a hash
function `w` of `vs` at `0x300000`, the functions of `vs` at distinct
addresses (`HashTable.symsOf32`), and the curve's table of constants, if
any, at `0x100000`, where the memory `m₀` holds it (`sat_nil`, `sat_one`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm
open VG.Proof.HmacTable.Arm (HVar vars sha256V tables names tableOf held_tableOf hashAt_tableOf readW_sepW put6w
  put6w_held put6w_below put2w put2w_above symT symT_distinct)

/-- The words of `w`'s table. -/
def tw6 (vs : List HVar) (w : HVar) : List (BitVec 64) :=
  [(symT vs w.F.hiAnyN).setWidth 64, (symT vs w.F.H.updN).setWidth 64, (symT vs w.F.hfN).setWidth 64,
    BitVec.ofNat 64 (Spec.HashTable.index w.G), BitVec.ofNat 64 w.G.len,
    BitVec.ofNat 64 (Spec.HmacTable.blockSize w.G)]

/-- A state meeting the contract, for scalars of `Q` bytes, with the table
of `w` and the memory `m₀` (the curve's tables of constants `Tr`). -/
def satT (vs : List HVar) (w : HVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => BitVec.ofNat 32 w.F.H.D | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem := put6w (put2w m₀ 0x10000 0x300000) 0x300000 (((tw6 vs w).getD 0 0).setWidth 32)
    (((tw6 vs w).getD 1 0).setWidth 32) (((tw6 vs w).getD 2 0).setWidth 32) (((tw6 vs w).getD 3 0).setWidth 32)
    (((tw6 vs w).getD 4 0).setWidth 32) (((tw6 vs w).getD 5 0).setWidth 32)
  rd := [⟨0x2000, Q⟩, ⟨0x3000, w.F.H.D⟩, ⟨0x300000, 24⟩, ⟨0x9000, 8⟩] ++ Tr
  wr := [⟨0x1000, 2 * Q⟩, ⟨0x10000, 8192⟩]
  syms := symT vs

theorem satT_held (vs : List HVar) (w : HVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) :
    Abi.tableHeld 32 (satT vs w m₀ Q Tr).mem (State.addr (0x300000 : BitVec 32))
      (FnTable.words isa (satT vs w m₀ Q Tr) (tableOf w)) := by
  rw [show State.addr (0x300000 : BitVec 32) = 0x300000 by decide]
  exact put6w_held (ws := tw6 vs w) rfl

theorem satT_arg0 (vs : List HVar) (w : HVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) :
    stackArg (satT vs w m₀ Q Tr) 0 = 0x10000 := by
  show (put6w _ _ _ _ _ _ _ _).readW (State.addr (0x9000 + BitVec.ofNat 32 (4 * 0))) 32 = _
  rw [put6w_below (by decide) (by decide)]
  simp only [put2w]
  rw [readW_sepW (.inl (by decide)) (by decide) (by decide) (by decide)]
  exact Mem.readW_writeW_self32 _ _ _

theorem satT_arg1 (vs : List HVar) (w : HVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) :
    stackArg (satT vs w m₀ Q Tr) 1 = 0x300000 := by
  show (put6w _ _ _ _ _ _ _ _).readW (State.addr (0x9000 + BitVec.ofNat 32 (4 * 1))) 32 = _
  rw [put6w_below (by decide) (by decide)]
  simp only [put2w]
  exact Mem.readW_writeW_self32 _ _ _

theorem constRegions_symT (vs : List HVar) (n : String) (W : List (BitVec 64)) (hna : n ∉ names vs) :
    Abi.constRegions (fun name => (symT vs name).setWidth 64) [(n, W)] = [⟨0x100000, 8 * W.length⟩] := by
  simp only [Abi.constRegions, List.map_cons, List.map_nil, symT, hna, ite_false]; rfl

theorem sat_nil {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar} {w : HVar} (hv : w ∈ vs)
    (hl : (names vs).length < 2 ^ 24) (hD : w.F.H.D ≤ 64)
    (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) : ∃ s, (specK T [] vs).pre s := by
  refine ⟨satT vs w (fun _ => 0) T.ecdsa.curve.len [], ?_⟩
  have a0 := satT_arg0 vs w (fun _ => 0) T.ecdsa.curve.len []
  have a1 := satT_arg1 vs w (fun _ => 0) T.ecdsa.curve.len []
  have hG : Spec.HmacTable.hashAt 32 (satT vs w (fun _ => 0) T.ecdsa.curve.len []).mem
      (State.addr (0x300000 : BitVec 32)) = some w.G :=
    hashAt_tableOf (by decide) (held_tableOf (by decide) (satT_held vs w _ _ _)).2.1
  have hDn : (BitVec.ofNat 32 w.F.H.D).toNat = w.F.H.D := by rw [BitVec.toNat_ofNat]; omega_using [hD]
  have hsp : (satT vs w (fun _ => 0) T.ecdsa.curve.len []).sp = 0x9000 := rfl
  have hsy : (satT vs w (fun _ => 0) T.ecdsa.curve.len []).syms = symT vs := rfl
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Abi.withConsts, stackBelow, stackT, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, hsw, tableRegion_eq, names_eq, argAddr0, a0, a1, hsp, hsy]
  have hA : State.addr (0x9000 : BitVec 32) = 0x9000 := by decide
  simp only [hDn, a0, a1, hsw, hA]
  sig_and_intros
  all_goals try rw [hsp]
  all_goals try rw [hA]
  all_goals first
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, satT_held vs w _ _ _⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hl)
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, BitVec.reduceSetWidth,
          BitVec.reduceSub, BitVec.reduceToNat]
        omega_using [hQ, hD])
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨w.glen.symm, by rw [w.hmac]; rfl⟩)

theorem sat_one {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar} {w : HVar} (hv : w ∈ vs)
    (hl : (names vs).length < 2 ^ 24) (hD : w.F.H.D ≤ 64) {n : String} {W : List (BitVec 64)} (m₀ : Mem)
    (hna : n ∉ names vs) (hW : 8 * W.length ≤ 0x100000)
    (hheld : ∀ i < W.length, m₀.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0)
    (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) : ∃ s, (specK T [(n, W)] vs).pre s := by
  refine ⟨satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩], ?_⟩
  have a0 := satT_arg0 vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]
  have a1 := satT_arg1 vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]
  have hG : Spec.HmacTable.hashAt 32 (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).mem
      (State.addr (0x300000 : BitVec 32)) = some w.G :=
    hashAt_tableOf (by decide) (held_tableOf (by decide) (satT_held vs w _ _ _)).2.1
  have hDn : (BitVec.ofNat 32 w.F.H.D).toNat = w.F.H.D := by rw [BitVec.toNat_ofNat]; omega_using [hD]
  have hsp : (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).sp = 0x9000 := rfl
  have hsy : (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).syms = symT vs := rfl
  have hsym : symT vs n = 0x100000 := by simp only [symT, hna, ite_false]
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Abi.withConsts, stackBelow, stackT, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, hsw, tableRegion_eq, names_eq, argAddr0, a0, a1, hsp, hsy]
  have hA : State.addr (0x9000 : BitVec 32) = 0x9000 := by decide
  simp only [hDn, a0, a1, hsw, hA]
  sig_and_intros
  all_goals try rw [hsp]
  all_goals try rw [hA]
  all_goals try (intro c hc; simp only [List.mem_singleton] at hc; subst hc)
  all_goals try (intro t ht; rw [constRegions_symT vs n W hna, List.mem_singleton] at ht; subst ht)
  all_goals first
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, satT_held vs w _ _ _⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hl)
    | exact (constRegions_symT vs n W hna).symm
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, BitVec.reduceSetWidth,
          BitVec.reduceSub, BitVec.reduceToNat]
        omega_using [hQ, hD])
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨w.glen.symm, by rw [w.hmac]; rfl⟩)
    | (intro i hi
       show (put6w _ _ _ _ _ _ _ _).readW ((symT vs n).setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0
       rw [hsym, put6w_below (by decide) (by bv_omega), put2w_above (by decide) (by bv_omega) (by bv_omega)]
       exact hheld i hi)
    | (refine ⟨show (1048576 : BitVec 64).toNat + 8 * W.length ≤ 2 ^ 32 by bv_omega, ?_, ?_, ?_⟩ <;>
       exact Region.disjoint_of_sep (by
         simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, BitVec.reduceSub,
           BitVec.reduceToNat]
         omega_using [hQ, hW]))

theorem names_len : (names vars).length < 2 ^ 24 := by decide

theorem sha256V_mem : sha256V ∈ vars := .tail _ (.tail _ (.tail _ (.head _)))

/-- `vg_ecdsa_<curve>_sign` with the tables of every hash function with HMAC
on ARMv7, for a curve without tables of constants. -/
theorem nilT_verified {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T)
    (hsw : T.scratchWords = 1024) (hQ : T.ecdsa.curve.len ≤ 66) (hcs : R.coreConsts = []) :
    Verified Arm.target (signCodeT R T.tries vars) (specK T R.coreConsts vars) :=
  signT_verified hC hsw vars_ok (by rw [hcs]; exact sat_nil sha256V_mem names_len (by decide) hQ hsw)

/-- The same, for a curve with one table of constants `W`, `m₀` holding it
at `0x100000`. -/
theorem oneT_verified {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T)
    (hsw : T.scratchWords = 1024) (hQ : T.ecdsa.curve.len ≤ 66) {n : String} {W : List (BitVec 64)}
    (hcs : R.coreConsts = [(n, W)]) (m₀ : Mem) (hna : n ∉ names vars) (hW : 8 * W.length ≤ 0x100000)
    (hheld : ∀ i < W.length, m₀.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0) :
    Verified Arm.target (signCodeT R T.tries vars) (specK T R.coreConsts vars) :=
  signT_verified hC hsw vars_ok (by
    rw [hcs]; exact sat_one sha256V_mem names_len (by decide) m₀ hna hW hheld hQ hsw)

end VG.Proof.Ecdsa.Rfc6979.Arm
