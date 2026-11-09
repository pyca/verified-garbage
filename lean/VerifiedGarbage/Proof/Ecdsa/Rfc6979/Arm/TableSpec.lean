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
    (hsp : 536 ≤ s.sp.toNat) (hsp8 : s.sp.toNat + 8 ≤ 2 ^ 32)
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
    (ko : Region.Disjoint (stkR s.sp 536) ⟨State.addr (s.gpr .r0), 2 * T.ecdsa.curve.len⟩)
    (kd : Region.Disjoint (stkR s.sp 536) ⟨State.addr (s.gpr .r1), T.ecdsa.curve.len⟩)
    (kg : Region.Disjoint (stkR s.sp 536) ⟨State.addr (s.gpr .r2), w.F.H.D⟩)
    (kc : Region.Disjoint (stkR s.sp 536) ⟨State.addr (stackArg s 0), 8192⟩)
    (kt : Region.Disjoint (stkR s.sp 536) ⟨State.addr (stackArg s 1), 24⟩)
    (no : (s.gpr .r0).toNat + 2 * T.ecdsa.curve.len ≤ 2 ^ 32) (nd : (s.gpr .r1).toNat + T.ecdsa.curve.len ≤ 2 ^ 32)
    (ng : (s.gpr .r2).toNat + w.F.H.D ≤ 2 ^ 32) (nc : (stackArg s 0).toNat + 8192 ≤ 2 ^ 32)
    (nt : (stackArg s 1).toNat + 24 ≤ 2 ^ 32)
    (htab : TablesOk cs s.syms s.mem [⟨State.addr (s.gpr .r0), 2 * T.ecdsa.curve.len⟩,
      ⟨State.addr (stackArg s 0), 8192⟩, stkR s.sp 536])
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
