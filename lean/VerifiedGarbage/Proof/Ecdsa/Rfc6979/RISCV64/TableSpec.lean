module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Table
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Table
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# Deterministic ECDSA on RISC-V: the contract with the hash function as a table

`TableInstance.signContract`, with the tables of `vs` for `hash`, the
curve's tables of constants and `stackT` bytes of stack, implies `tabK`
(`tab_implies`): the table `hash` points to is one of `vs`', whose words
give the contract the proof of its hash function's code is written against,
on entry; its hash function is the one the table names, so the results
agree; and two runs whose public data agree take the same table.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64

open VG VG.RISCV64 VG.Impl.Ecdsa.Rfc6979.RISCV64
open VG.Proof.HashTable.RISCV64 (TVar tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf hashAt_tableOf)

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List TVar}

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specK (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64))) (vs : List TVar) :
    Contract isa :=
  T.signContract ((RISCV64.abi.withConsts cs).withTables T.signSig [("hash", tables vs)]) stackT

theorem tableRegion_eq (p : Addr) : Sig.tableRegion 64 p 5 = ⟨p, 40⟩ := rfl

theorem names_eq (vs : List TVar) : (List.map (fun x => x.fns) (tables vs)).flatten = names vs := rfl

/-- The table `hash` points to holds `w`'s. -/
abbrev HeldW (w : TVar) (s : State) : Prop := Abi.tableHeld 64 s.mem (s.gpr .a5) (FnTable.words isa s (tableOf w))

/-- The facts of the contract with the table of `w`, on entry. -/
theorem preW_of {w : TVar} (hv : w ∈ vs) (hc : Coh vs) {s : State}
    (hal : s.sp.toNat % 16 = 0) (hsp : 560 ≤ s.sp.toNat)
    (hrd : (stripConsts R.kit.K s).rd = [⟨s.gpr .a1, T.ecdsa.curve.len⟩, ⟨s.gpr .a2, w.H.D⟩, ⟨s.gpr .a5, 40⟩])
    (hwr : s.wr = [⟨s.gpr .a0, 2 * T.ecdsa.curve.len⟩, ⟨s.gpr .a4, 8192⟩])
    (od : Region.Disjoint ⟨s.gpr .a0, 2 * T.ecdsa.curve.len⟩ ⟨s.gpr .a1, T.ecdsa.curve.len⟩)
    (og : Region.Disjoint ⟨s.gpr .a0, 2 * T.ecdsa.curve.len⟩ ⟨s.gpr .a2, w.H.D⟩)
    (oc : Region.Disjoint ⟨s.gpr .a0, 2 * T.ecdsa.curve.len⟩ ⟨s.gpr .a4, 8192⟩)
    (ot : Region.Disjoint ⟨s.gpr .a0, 2 * T.ecdsa.curve.len⟩ ⟨s.gpr .a5, 40⟩)
    (dc : Region.Disjoint ⟨s.gpr .a1, T.ecdsa.curve.len⟩ ⟨s.gpr .a4, 8192⟩)
    (gc : Region.Disjoint ⟨s.gpr .a2, w.H.D⟩ ⟨s.gpr .a4, 8192⟩)
    (ct : Region.Disjoint ⟨s.gpr .a4, 8192⟩ ⟨s.gpr .a5, 40⟩)
    (ko : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 560, 560⟩ ⟨s.gpr .a0, 2 * T.ecdsa.curve.len⟩)
    (kd : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 560, 560⟩ ⟨s.gpr .a1, T.ecdsa.curve.len⟩)
    (kg : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 560, 560⟩ ⟨s.gpr .a2, w.H.D⟩)
    (kc : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 560, 560⟩ ⟨s.gpr .a4, 8192⟩)
    (kt : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 560, 560⟩ ⟨s.gpr .a5, 40⟩)
    (no : (s.gpr .a0).toNat + 2 * T.ecdsa.curve.len ≤ 2 ^ 64)
    (nd : (s.gpr .a1).toNat + T.ecdsa.curve.len ≤ 2 ^ 64) (ng : (s.gpr .a2).toNat + w.H.D ≤ 2 ^ 64)
    (nc : (s.gpr .a4).toNat + 8192 ≤ 2 ^ 64) (nt : (s.gpr .a5).toNat + 40 ≤ 2 ^ 64)
    (ca : (s.gpr .a4).toNat % 8 = 0) (ta : (s.gpr .a5).toNat % 8 = 0)
    (hK : ConstsOk R.kit.K stackT s)
    (hheld : HeldW w s) (hpw : (names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) :
    PreW R T vs w s := by
  have hh := held_tableOf hheld
  refine ⟨⟨⟨hrd, hwr, od, og, oc, dc, gc, hal, hsp, ko, kd, kg, kc, no, nd, ng, nc, ca, ot.symm, ct.symm, kt,
    ta, nt, hh.1, ?_⟩, hK⟩, hh.2.1⟩
  obtain ⟨a, b, c⟩ := tabOK_of hc hpw hv
  exact ⟨a, b, c⟩

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract on entry. -/
def PreFacts (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW w s) ∧ ∀ w ∈ vs, HeldW w s → PreW R T vs w s

theorem sig_rd_nil (s : State) : (stripConsts [] s).rd = s.rd := by simp [stripConsts, State.withRegions]

/-- The precondition, with tables of constants. -/
theorem pre_cons (hsw : T.scratchWords = 1024) (hO : OK vs) {c : String × List (BitVec 64)}
    {cs : List (String × List (BitVec 64))} (hcs : R.kit.K = c :: cs) {s : State}
    (h : (specK T (c :: cs) vs).pre s) : PreFacts R T vs s := by
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    RISCV64.abi, RISCV64.argRegs, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw, tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hal, hsp, hdrop, held, hfit, htal, ⟨Tb, hTb, hheld⟩, hpw, htake, hwr, od, og, oc, ot, dc, gc, ct, ko, kd,
    kg, kc, kt, no, nd, ng, nc, nt, hH, ca, ta⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf hheld
  have hlen : (s.gpr .a3).toNat = w.H.D := (hH _ (hashAt_tableOf hh.2.1)).1.trans w.l.len
  rw [hlen] at og gc kg ng htake
  rw [hsw] at hwr oc dc gc kc nc ct
  rw [List.append_eq, List.append_nil] at hpw
  refine preW_of hv hO.1 hal hsp ?_ hwr od og oc ot dc gc ct ko kd kg kc kt no nd ng nc nt ca ta ?_ hheld hpw
  · show s.rd.take (s.rd.length - R.kit.K.length) = _
    rw [hcs]; exact htake
  · rw [hcs]
    refine ⟨hdrop, held, fun t htm => ⟨(hfit t htm).1, (hfit t htm).2.1, fun r hr => ?_⟩, htal⟩
    simp only [abi, stackBelow, stackT, List.mem_singleton] at hr
    subst hr
    exact (hfit t htm).2.2

/-- The precondition, without tables of constants. -/
theorem pre_nil (hsw : T.scratchWords = 1024) (hO : OK vs) (hcs : R.kit.K = []) {s : State}
    (h : (specK T [] vs).pre s) : PreFacts R T vs s := by
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    RISCV64.abi, RISCV64.argRegs, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw, tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hal, hsp, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, od, og, oc, ot, dc, gc, ct, ko, kd,
    kg, kc, kt, no, nd, ng, nc, nt, hH, ca, ta⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf hheld
  have hlen : (s.gpr .a3).toNat = w.H.D := (hH _ (hashAt_tableOf hh.2.1)).1.trans w.l.len
  rw [hlen] at og gc kg ng hrd
  rw [hsw] at hwr oc dc gc kc nc ct
  rw [List.append_eq, List.append_nil] at hpw
  refine preW_of hv hO.1 hal hsp ?_ hwr od og oc ot dc gc ct ko kd kg kc kt no nd ng nc nt ca ta ?_ hheld hpw
  · rw [hcs, sig_rd_nil]; exact hrd
  · rw [hcs]; exact ⟨by simp [constRegs, Abi.constRegions], fun _ h => absurd h (by simp),
      fun _ h => absurd h (by simp [constRegs, Abi.constRegions]), fun _ h => absurd h (by simp [constRegs, Abi.constRegions])⟩

/-- The postcondition: the hash function the table names is its own. -/
theorem post_of {s s' : State} (hk : (tabK R T vs).pre s) (hp : (tabK R T vs).post s s') :
    ∀ (H : Spec.Mgf1.Hash) (F : Spec.Hmac.HashFunction),
      Spec.HashTable.hashAt 64 s.mem (s.gpr .a5) = some H → Spec.Ecdsa.Rfc6979.hmacOf H = some F →
        match (T.result H F s.mem (s.gpr .a1) (s.gpr .a2)).fst with
        | some rs => BitVec.setWidth 32 (s'.gpr .a0) = 1 ∧
            Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
        | none => BitVec.setWidth 32 (s'.gpr .a0) = 0 ∧
            Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) (2 * T.ecdsa.curve.len) =
              List.replicate (2 * T.ecdsa.curve.len) 0 := by
  intro H F hH hF
  obtain ⟨w, hv, hw, hpre⟩ := hk
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf hpre.2))
  obtain rfl := Option.some.inj (hF.symm.trans hw.hmac)
  exact hp w hv hw hpre

/-- What the public data say. -/
def PubFacts (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) (s₁ s₂ : State) : Prop :=
  (∀ w ∈ vs, HeldW w s₁ ↔ HeldW w s₂) ∧ (∀ r ∈ [Reg.a0, .a1, .a2, .a4, .a5], s₁.gpr r = s₂.gpr r) ∧
    s₁.sp = s₂.sp ∧
    T.tried 64 s₁.mem (s₁.gpr .a1) (s₁.gpr .a2) (s₁.gpr .a5) =
      T.tried 64 s₂.mem (s₂.gpr .a1) (s₂.gpr .a2) (s₂.gpr .a5) ∧
    (∀ c ∈ R.kit.K, s₁.syms c.1 = s₂.syms c.1) ∧ ∀ n ∈ names vs, s₁.syms n = s₂.syms n

theorem tried_eq {w : TVar} (hw : WOk w) {s : State} (hp : PreW R T vs w s) :
    T.tried 64 s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a5) =
      ((instOf T w).result s.mem (s.gpr .a1) (s.gpr .a2)).2 := by
  simp only [Spec.Ecdsa.Rfc6979.TableInstance.tried, hashAt_tableOf hp.2, hw.hmac, tresult_eq]

/-- The public data of `tabK`, from the facts. -/
theorem pub_of (hO : OK vs) {s₁ s₂ : State} (h₁ : PreFacts R T vs s₁) (h₂ : PreFacts R T vs s₂)
    (hp : PubFacts R T vs s₁ s₂) : (tabK R T vs).pub s₁ s₂ := by
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  obtain ⟨hh', hg, hsp, ht, hc, hn⟩ := hp
  have p₁ := f₁ w hv hh
  have p₂ := h₂.2 w hv ((hh' w hv).mp hh)
  have hw := hO.2.2.2 w hv
  have hm := mem_names hv
  refine ⟨w, hv, hw, p₁, p₂, ⟨hsp, hg .a0 (by simp), hg .a1 (by simp), hg .a2 (by simp), hg .a4 (by simp),
    hg .a5 (by simp), hn _ hm.1, hn _ hm.2.1, hn _ hm.2.2, ?_⟩, hc⟩
  show ((instOf T w).result s₁.mem (s₁.gpr .a1) (s₁.gpr .a2)).2 =
    ((instOf T w).result s₂.mem (s₂.gpr .a1) (s₂.gpr .a2)).2
  rw [← tried_eq hw p₁, ← tried_eq hw p₂, ht]

/-- The public data, with tables of constants. -/
theorem pub_cons {c : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    (hcs : R.kit.K = c :: cs) {s₁ s₂ : State}
    (h : (specK T (c :: cs) vs).pub s₁ s₂) : PubFacts R T vs s₁ s₂ := by
  sig_pub [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    RISCV64.abi, RISCV64.argRegs, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨e₁, hc₀, hcs', hn, hT, htr, e₂, e₃, e₄, -, e₅, e₆⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  refine ⟨fun w hv => hT _ _ rfl rfl _ (List.mem_map_of_mem hv), fun r hr => ?_, e₁, (List.cons.inj htr).1,
    fun c' hc' => ?_, hn⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [hcs] at hc'
    rcases List.mem_cons.mp hc' with rfl | h
    · exact hc₀
    · exact hcs' _ h

/-- The public data, without tables of constants. -/
theorem pub_nil (hcs : R.kit.K = []) {s₁ s₂ : State}
    (h : (specK T [] vs).pub s₁ s₂) : PubFacts R T vs s₁ s₂ := by
  sig_pub [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    RISCV64.abi, RISCV64.argRegs, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨e₁, hn, hT, htr, e₂, e₃, e₄, -, e₅, e₆⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  refine ⟨fun w hv => hT _ _ rfl rfl _ (List.mem_map_of_mem hv), fun r hr => ?_, e₁, (List.cons.inj htr).1,
    fun c' hc' => absurd hc' (by rw [hcs]; simp), hn⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem PreFacts.pre (hO : OK vs) {s : State} (h : PreFacts R T vs s) : (tabK R T vs).pre s :=
  let ⟨⟨w, hv, hh⟩, f⟩ := h; ⟨w, hv, hO.2.2.2 w hv, f w hv hh⟩

/-- `TableInstance.signContract` with the tables of `vs` implies `tabK`. -/
theorem tab_implies (hsw : T.scratchWords = 1024) (hO : OK vs)
    (hsat : ∃ s, (specK T R.kit.K vs).pre s) : (tabK R T vs).Implies (specK T R.kit.K vs) := by
  generalize hcs : R.kit.K = cs at hsat ⊢
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
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    RISCV64.abi, RISCV64.argRegs, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq]
    exact post_of hk hp

/-- `vg_ecdsa_<curve>_sign`, with the tables of `vs`, meets
`TableInstance.signContract` (given the taint checks of each index's code
and a state that meets it). -/
theorem signT_verified (hC : CurveT R T) (hsw : T.scratchWords = 1024) (hO : OK vs)
    (hck : ∀ i ∈ idxs, Checks (cfgS R T.tries (shapeOf i).1 (shapeOf i).2))
    (hsat : ∃ s, (specK T R.kit.K vs).pre s) :
    Verified RISCV64.target (signCode R T.tries vs) (specK T R.kit.K vs) :=
  Verified.of_correct (fun _ h => signT_ok hC h) (signT_ct hC hck) (tab_implies hsw hO hsat)

end VG.Proof.Ecdsa.Rfc6979.RISCV64
