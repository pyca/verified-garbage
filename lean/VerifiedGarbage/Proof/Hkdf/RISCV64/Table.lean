module

public import VerifiedGarbage.Proof.Hkdf.RISCV64.Key
public import VerifiedGarbage.Proof.Hkdf.RISCV64.Extract
public import VerifiedGarbage.Proof.Hkdf.RISCV64.Expand
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.HashTable.Basic
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# HKDF on RISC-V: the contracts with the hash function as a table

Each function is one body, which loads `D` and `B` from the table `hmac`
and calls the table's functions. For the hash functions `vs` whose tables it
takes (`OK`: their functions of the same name have the same code, each's
streaming states are the specification's for its hash function), the table
of each `w` makes the body meet the contract with `w`'s hash function fixed
(`keyR`, `key_correct`, `key_ct`). `keyTab` states that contract for
whichever of the tables `hmac` holds, on entry, which the specification's
contract with the tables of `vs` implies (`key_implies`): the table `hmac`
points to is one of `vs`', whose words give the contract the proof is
written against; its hash function is the one the table names; and two
runs whose public data agree take the same table. A state meets it
(`key_sat`): the buffers at fixed addresses, the table of a hash function of
`vs` at `0x300000`, the functions of `vs` at distinct addresses.
-/

@[expose] public section

namespace VG.Proof.Hkdf.RISCV64

open VG VG.RISCV64
open VG.Impl.Hkdf.RISCV64
open VG.Proof.HmacTable.RISCV64 (HVar tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf
  hashAt_tableOf)
open VG.Proof.HashTable (symsOf symsOf_distinct readW_sep64)

/-- What the registrations check of the hash functions whose tables the
functions take: the functions of the same name have the same code, there
are fewer than `2 ^ 32` names, and there is one. -/
def OK (vs : List HVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ []

instance (vs : List HVar) : Decidable (OK vs) := by unfold OK; infer_instance

/-- Each hash function's streaming states are those the specification
gives it (`Spec.Hkdf.streamingOf`). -/
def Streams (vs : List HVar) : Prop := ∀ w ∈ vs, Spec.Hkdf.streamingOf w.G = some w.hH.SH

theorem tableRegion_eq (p : Addr) : Sig.tableRegion 64 p 6 = ⟨p, 48⟩ := rfl

theorem names_eq (vs : List HVar) : (List.map (fun x => x.fns) (tables vs)).flatten = names vs := rfl

/-- The table `hmac` (in `r`) points to holds `w`'s. -/
abbrev HeldW (r : Reg) (w : HVar) (s : State) : Prop :=
  Abi.tableHeld 64 s.mem (s.gpr r) (FnTable.words isa s (tableOf w))

/-- The table's index, as the table of `w` holds it. -/
abbrev IdxW (r : Reg) (w : HVar) (s : State) : Prop :=
  s.mem.readW (s.gpr r + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.G)

theorem index_lt (w : HVar) : Spec.HashTable.index w.G < 2 ^ 64 := by
  have h := w.t.idx
  have : Spec.HashTable.index w.G < Spec.Mgf1.hashes.length := by
    rcases Nat.lt_or_ge (Spec.HashTable.index w.G) Spec.Mgf1.hashes.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  exact Nat.lt_of_lt_of_le this (by decide)

/-- The hash function a table of `w` names, and its streaming states. -/
theorem streams_of {vs : List HVar} (hS : Streams vs) {w : HVar} (hv : w ∈ vs) {m : Mem} {p : Addr}
    (h : m.readW (p + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.G))
    {H : Spec.Mgf1.Hash} {S : Spec.Hmac.StreamingHash} (hH : Spec.HmacTable.hashAt 64 m p = some H)
    (hSt : Spec.Hkdf.streamingOf H = some S) : S = w.hH.SH := by
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf h))
  exact Option.some.inj (hSt.symm.trans (hS w hv))

/-! ## A state meeting a contract -/

/-- Six words at `p`. -/
def put6 (m : Mem) (p : Addr) (w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 64) : Mem :=
  (((((m.writeW (p + BitVec.ofNat 64 (8 * 0)) w₀).writeW (p + BitVec.ofNat 64 (8 * 1)) w₁).writeW
    (p + BitVec.ofNat 64 (8 * 2)) w₂).writeW (p + BitVec.ofNat 64 (8 * 3)) w₃).writeW
    (p + BitVec.ofNat 64 (8 * 4)) w₄).writeW (p + BitVec.ofNat 64 (8 * 5)) w₅

/-- The table `put6` writes at `0x300000`. -/
theorem put6_held {m : Mem} {ws : List (BitVec 64)} (hl : ws.length = 6) :
    Abi.tableHeld 64 (put6 m 0x300000 (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) (ws.getD 3 0) (ws.getD 4 0)
      (ws.getD 5 0)) 0x300000 ws := by
  intro i hi
  rw [hl] at hi
  simp only [put6]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [readW_sep64, readW_sep64, readW_sep64, readW_sep64, readW_sep64, Mem.readW_writeW_self64,
      BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, readW_sep64, readW_sep64, readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, readW_sep64, readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [Mem.readW_writeW_self64, BitVec.setWidth_eq]

/-- The functions of `vs` at distinct addresses, and every other symbol at `0x100000`. -/
def symT (vs : List HVar) (n : String) : Addr := if n ∈ names vs then symsOf (names vs) n else 0x100000

theorem symT_distinct {vs : List HVar} (hl : (names vs).length < 2 ^ 32) :
    (names vs).Pairwise fun f g => f ≠ g → symT vs f ≠ symT vs g :=
  (symsOf_distinct hl).imp_of_mem fun {f g} hf hg h hne => by
    simp only [symT, hf, hg, ite_true]; exact h hne

/-- The memory with the table of `w` at `0x300000`. -/
def tabMem (vs : List HVar) (w : HVar) : Mem :=
  put6 (fun _ => 0) 0x300000 (symT vs w.hiN) (symT vs w.H.updN) (symT vs w.hfN)
    (BitVec.ofNat 64 (Spec.HashTable.index w.G)) (BitVec.ofNat 64 w.G.len)
    (BitVec.ofNat 64 (Spec.HmacTable.blockSize w.G))

theorem tabMem_held (vs : List HVar) (w : HVar) (s : State) (hs : s.syms = symT vs) :
    Abi.tableHeld 64 (tabMem vs w) 0x300000 (FnTable.words isa s (tableOf w)) := by
  rw [Proof.HmacTable.RISCV64.words_tableOf, hs]
  exact put6_held (ws := [symT vs w.hiN, symT vs w.H.updN, symT vs w.hfN,
    BitVec.ofNat 64 (Spec.HashTable.index w.G), BitVec.ofNat 64 w.G.len,
    BitVec.ofNat 64 (Spec.HmacTable.blockSize w.G)]) rfl

/-! ## `vg_hkdf_key` -/

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specKey (vs : List HVar) : Contract isa :=
  Spec.Hkdf.keyContract (RISCV64.abi.withTables Spec.Hkdf.keySig [("hmac", tables vs)]) keyStack

/-- The contract with the table of `w`, and its index. -/
def KeyW (vs : List HVar) (w : HVar) (s : State) : Prop :=
  (keyR w (fnsOf vs) (names vs) keyStack).pre s ∧ IdxW .a3 w s

/-- The contract with whichever of the tables of `vs` the table at `a3` is. -/
def keyTab (vs : List HVar) : Contract isa where
  pre s := ∃ w ∈ vs, KeyW vs w s
  post s s' := ∀ H S, Spec.HmacTable.hashAt 64 s.mem (s.gpr .a3) = some H → Spec.Hkdf.streamingOf H = some S →
    Spec.Hkdf.Keyed S s'.mem (s.gpr .a2) (Spec.Sha256.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
  pub s₁ s₂ := ∃ w ∈ vs, KeyW vs w s₁ ∧ KeyW vs w s₂ ∧ (keyR w (fnsOf vs) (names vs) keyStack).pub s₁ s₂

section
variable {vs : List HVar}

theorem keyT_ok (hS : Streams vs) {s : State} (h : (keyTab vs).pre s) :
    ∃ t s', Exec isa (key (fnsOf vs)) s t s' ∧ abiPreserved s s' ∧ (keyTab vs).post s s' := by
  obtain ⟨w, hv, hp, hix⟩ := h
  obtain ⟨t, s', he, ha, hpost⟩ := key_correct hp
  refine ⟨t, s', he, ha, fun H S hH hSt => ?_⟩
  rw [streams_of hS hv hix hH hSt]
  exact hpost

theorem keyT_ct : ConstantTime isa (keyTab vs).pre (keyTab vs).pub (key (fnsOf vs)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, p₁, p₂, hpub⟩ e₁ e₂
  exact key_ct (mem_names hv).1 s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract on entry. -/
def KeyFacts (vs : List HVar) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW .a3 w s) ∧ ∀ w ∈ vs, HeldW .a3 w s → KeyW vs w s

theorem key_pre (hO : OK vs) {s : State} (h : (specKey vs).pre s) : KeyFacts vs s := by
  sig_pre [Spec.Hkdf.keyContract, Spec.Hkdf.keySig, Spec.Hkdf.keyPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    RISCV64.abi, RISCV64.argRegs, stackBelow, keyStack, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, hN, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, d1, d2, d3, d4, d5, n1, n2, n3, -, a3⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf hheld
  rw [List.append_eq, List.append_nil] at hpw
  exact ⟨⟨hrd, hwr, d1, d2.symm, hsp, hN, d3, d4, d5, n1, n2, n3, a3, hh.1, tabOK_of hO.1 hpw hv⟩, hh.2.1⟩

theorem key_pub {s₁ s₂ : State} (h₁ : KeyFacts vs s₁) (h₂ : KeyFacts vs s₂) (h : (specKey vs).pub s₁ s₂) :
    (keyTab vs).pub s₁ s₂ := by
  sig_pub [Spec.Hkdf.keyContract, Spec.Hkdf.keySig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    RISCV64.abi, RISCV64.argRegs, stackBelow, keyStack, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, hn, hT, e0, e1, e2, e3⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  exact ⟨w, hv, f₁ w hv hh, h₂.2 w hv ((hT _ _ rfl rfl _ (List.mem_map_of_mem hv)).mp hh),
    hsp, e0, e1, e2, e3, hn⟩

/-- The contract with the tables of `vs`, given a state that meets it. -/
theorem key_implies (hO : OK vs) (hsat : ∃ s, (specKey vs).pre s) : (keyTab vs).Implies (specKey vs) := by
  refine ⟨fun s h => ?_, fun s s' h hp => ?_, fun s₁ s₂ h₁ h₂ hp => key_pub (key_pre hO h₁) (key_pre hO h₂) hp,
    hsat⟩
  · obtain ⟨⟨w, hv, hh⟩, f⟩ := key_pre hO h
    exact ⟨w, hv, f w hv hh⟩
  · sig_post [Spec.Hkdf.keyContract, Spec.Hkdf.keySig, Spec.Hkdf.keyPost,
      Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
      RISCV64.abi, RISCV64.argRegs, stackBelow, keyStack, String.reduceEq, Option.map_some,
      List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
      List.append_nil, names_eq]
    exact fun H S a b => hp H S a b

/-- A state meeting the contract: `PRK` (32 bytes) at `0x1000`, `key` at
`0x2000`, the table of a hash function of `vs` at `0x300000`. -/
def keySat (vs : List HVar) (w : HVar) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 32 | .a2 => 0x2000 | .a3 => 0x300000 | _ => 0
  sp := 0x20000
  mem := tabMem vs w
  rd := [⟨0x1000, 32⟩, ⟨0x300000, 48⟩]
  wr := [⟨0x2000, 384⟩]
  syms := symT vs

theorem key_sat (hO : OK vs) (hS : Streams vs) : ∃ s, (specKey vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2
  refine ⟨keySat vs w, ?_⟩
  sig_pre [Spec.Hkdf.keyContract, Spec.Hkdf.keySig, Spec.Hkdf.keyPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    RISCV64.abi, RISCV64.argRegs, stackBelow, keyStack, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq]
  have hh := held_tableOf (tabMem_held vs w (keySat vs w) rfl)
  have hG : Spec.HmacTable.hashAt 64 (keySat vs w).mem 0x300000 = some w.G := hashAt_tableOf hh.2.1
  simp only [keySat] at hG ⊢
  sig_and_intros
  all_goals first
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, tabMem_held vs w (keySat vs w) rfl⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega)
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       rw [hS w hv]; rfl)

/-- `vg_hkdf_key`, with the tables of `vs`, meets `Spec.Hkdf.keyContract`. -/
theorem key_spec (hO : OK vs) (hS : Streams vs) : Verified RISCV64.target (key (fnsOf vs)) (specKey vs) :=
  Verified.of_correct (fun _ h => keyT_ok hS h) keyT_ct (key_implies hO (key_sat hO hS))

end

/-! ## `vg_hkdf_extract` -/

open VG.Proof.Hkdf.RISCV64.Extract (extractR xStack extract_correct extract_ct)

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specExtract (vs : List HVar) : Contract isa :=
  Spec.Hkdf.extractContract (RISCV64.abi.withTables Spec.Hkdf.extractSig [("hmac", tables vs)]) xStack

/-- The contract with the table of `w`, and its index. -/
def ExtractW (vs : List HVar) (w : HVar) (s : State) : Prop :=
  (extractR w (fnsOf vs) (names vs) xStack).pre s ∧ IdxW .a6 w s

/-- The contract with whichever of the tables of `vs` the table at `a6` is. -/
def extractTab (vs : List HVar) : Contract isa where
  pre s := ∃ w ∈ vs, ExtractW vs w s
  post s s' := ∀ H F, Spec.HmacTable.hashAt 64 s.mem (s.gpr .a6) = some H → Spec.HmacTable.hmacOf H = some F →
    Spec.Sha256.bytesAt s'.mem (s.gpr .a4) H.len = Spec.Hkdf.extract F
      (Spec.Sha256.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) (Spec.Sha256.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
  pub s₁ s₂ := ∃ w ∈ vs, ExtractW vs w s₁ ∧ ExtractW vs w s₂ ∧
    (extractR w (fnsOf vs) (names vs) xStack).pub s₁ s₂

section
variable {vs : List HVar}

theorem extractT_ok {s : State} (h : (extractTab vs).pre s) :
    ∃ t s', Exec isa (Impl.Hkdf.RISCV64.extract (fnsOf vs)) s t s' ∧ abiPreserved s s' ∧ (extractTab vs).post s s' := by
  obtain ⟨w, hv, hp, hix⟩ := h
  obtain ⟨t, s', he, ha, hpost⟩ := extract_correct hp
  refine ⟨t, s', he, ha, fun H F hH hF => ?_⟩
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf hix))
  obtain rfl := Option.some.inj (hF.symm.trans w.hmac)
  rw [w.t.l.len]
  exact hpost

theorem extractT_ct : ConstantTime isa (extractTab vs).pre (extractTab vs).pub (Impl.Hkdf.RISCV64.extract (fnsOf vs)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, p₁, p₂, hpub⟩ e₁ e₂
  have hn := mem_names hv
  exact extract_ct (fun n hn' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn'
    rcases hn' with rfl | rfl | rfl
    exacts [hn.1, hn.2.1, hn.2.2]) s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

/-- What the precondition says. -/
def ExtractFacts (vs : List HVar) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW .a6 w s) ∧ ∀ w ∈ vs, HeldW .a6 w s → ExtractW vs w s

theorem extract_pre (hO : OK vs) {s : State} (h : (specExtract vs).pre s) : ExtractFacts vs s := by
  sig_pre [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    RISCV64.abi, RISCV64.argRegs, stackBelow, xStack, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, hN, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, d1, d2, d3, d4, d5, d6, d7, n1, n2, n3, n4, hH, a6⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf hheld
  have hl : (s.gpr .a5).toNat = w.H.D := (hH _ (hashAt_tableOf hh.2.1)).1.trans w.t.l.len
  rw [hl] at hwr d1 d2 d3 d6 n3
  rw [List.append_eq, List.append_nil] at hpw
  exact ⟨⟨hrd, hwr, hl, d1, d2, d3.symm, hsp, hN, d4, d5, d6, d7, n1, n2, n3, n4, a6, hh.1, hh.2.2.1, hh.2.2.2,
    tabOK_of hO.1 hpw hv⟩, hh.2.1⟩

theorem extract_pub {s₁ s₂ : State} (h₁ : ExtractFacts vs s₁) (h₂ : ExtractFacts vs s₂)
    (h : (specExtract vs).pub s₁ s₂) : (extractTab vs).pub s₁ s₂ := by
  sig_pub [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    RISCV64.abi, RISCV64.argRegs, stackBelow, xStack, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, hn, hT, e0, e1, e2, e3, e4, e5, e6⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  exact ⟨w, hv, f₁ w hv hh, h₂.2 w hv ((hT _ _ rfl rfl _ (List.mem_map_of_mem hv)).mp hh),
    hsp, e0, e1, e2, e3, e4, e5, e6, hn⟩

theorem extract_implies (hO : OK vs) (hsat : ∃ s, (specExtract vs).pre s) :
    (extractTab vs).Implies (specExtract vs) := by
  refine ⟨fun s h => ?_, fun s s' h hp => ?_,
    fun s₁ s₂ h₁ h₂ hp => extract_pub (extract_pre hO h₁) (extract_pre hO h₂) hp, hsat⟩
  · obtain ⟨⟨w, hv, hh⟩, f⟩ := extract_pre hO h
    exact ⟨w, hv, f w hv hh⟩
  · sig_post [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPost,
      Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
      RISCV64.abi, RISCV64.argRegs, stackBelow, xStack, String.reduceEq, Option.map_some,
      List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
      List.append_nil, names_eq]
    exact fun H F a b => hp H F a b

/-- A state meeting the contract: a salt and input keying material of 16
bytes each at `0x1000` and `0x2000`, `PRK` at `0x3000`, the table of a hash
function of `vs` at `0x300000`. -/
def extractSat (vs : List HVar) (w : HVar) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 16 | .a2 => 0x2000 | .a3 => 16 | .a4 => 0x3000 | .a5 => BitVec.ofNat 64 w.H.D
    | .a6 => 0x300000 | _ => 0
  sp := 0x20000
  mem := tabMem vs w
  rd := [⟨0x1000, 16⟩, ⟨0x2000, 16⟩, ⟨0x300000, 48⟩]
  wr := [⟨0x3000, w.H.D⟩]
  syms := symT vs

theorem extract_sat (hO : OK vs) : ∃ s, (specExtract vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2
  refine ⟨extractSat vs w, ?_⟩
  sig_pre [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    RISCV64.abi, RISCV64.argRegs, stackBelow, xStack, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq]
  have hh := held_tableOf (tabMem_held vs w (extractSat vs w) rfl)
  have hG : Spec.HmacTable.hashAt 64 (extractSat vs w).mem 0x300000 = some w.G := hashAt_tableOf hh.2.1
  have hD := w.hH.hD64
  have hDn : (BitVec.ofNat 64 w.H.D).toNat = w.H.D := by rw [BitVec.toNat_ofNat]; omega_using [hD]
  simp only [extractSat, hDn] at hG ⊢
  sig_and_intros
  all_goals first
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, tabMem_held vs w (extractSat vs w) rfl⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega)
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨w.t.l.len.symm, by rw [w.hmac]; rfl⟩)

/-- `vg_hkdf_extract`, with the tables of `vs`, meets `Spec.Hkdf.extractContract`. -/
theorem extract_spec (hO : OK vs) :
    Verified RISCV64.target (Impl.Hkdf.RISCV64.extract (fnsOf vs)) (specExtract vs) :=
  Verified.of_correct (fun _ h => extractT_ok h) extractT_ct (extract_implies hO (extract_sat hO))

end

/-! ## `vg_hkdf_expand` -/

open VG.Proof.Hkdf.RISCV64.Expand (expandR eStack expand_correct expand_ct)

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specExpand (vs : List HVar) : Contract isa :=
  Spec.Hkdf.expandContract (RISCV64.abi.withTables Spec.Hkdf.expandSig [("hmac", tables vs)]) eStack

/-- The contract with the table of `w`, and its index. -/
def ExpandW (vs : List HVar) (w : HVar) (s : State) : Prop :=
  (expandR w (fnsOf vs) (names vs) eStack).pre s ∧ IdxW .a5 w s

/-- The contract with whichever of the tables of `vs` the table at `a5` is. -/
def expandTab (vs : List HVar) : Contract isa where
  pre s := ∃ w ∈ vs, ExpandW vs w s
  post s s' := ∀ H S prk, Spec.HmacTable.hashAt 64 s.mem (s.gpr .a5) = some H → Spec.Hkdf.streamingOf H = some S →
    Spec.Hkdf.Keyed S s.mem (s.gpr .a0) prk →
    Spec.Hkdf.expand S.H H.len prk (Spec.Sha256.bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat) (s.gpr .a4).toNat =
      some (Spec.Sha256.bytesAt s'.mem (s.gpr .a3) (s.gpr .a4).toNat)
  pub s₁ s₂ := ∃ w ∈ vs, ExpandW vs w s₁ ∧ ExpandW vs w s₂ ∧
    (expandR w (fnsOf vs) (names vs) eStack).pub s₁ s₂

section
variable {vs : List HVar}

theorem expandT_ok (hS : Streams vs) {s : State} (h : (expandTab vs).pre s) :
    ∃ t s', Exec isa (Impl.Hkdf.RISCV64.expand (fnsOf vs)) s t s' ∧ abiPreserved s s' ∧
      (expandTab vs).post s s' := by
  obtain ⟨w, hv, hp, hix⟩ := h
  obtain ⟨t, s', he, ha, hpost⟩ := expand_correct hp
  refine ⟨t, s', he, ha, fun H S prk hH hSt hK => ?_⟩
  obtain rfl := streams_of hS hv hix hH hSt
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf hix))
  rw [w.t.l.len]
  exact hpost prk hK

theorem expandT_ct : ConstantTime isa (expandTab vs).pre (expandTab vs).pub (Impl.Hkdf.RISCV64.expand (fnsOf vs)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, p₁, p₂, hpub⟩ e₁ e₂
  have hn := mem_names hv
  exact expand_ct (fun n hn' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn'
    rcases hn' with rfl | rfl
    exacts [hn.2.1, hn.2.2]) s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

/-- What the precondition says. -/
def ExpandFacts (vs : List HVar) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW .a5 w s) ∧ ∀ w ∈ vs, HeldW .a5 w s → ExpandW vs w s

theorem expand_pre (hO : OK vs) {s : State} (h : (specExpand vs).pre s) : ExpandFacts vs s := by
  sig_pre [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig, Spec.Hkdf.expandPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    RISCV64.abi, RISCV64.argRegs, stackBelow, eStack, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, hN, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, d1, d2, d3, d4, d5, d6, d7, n1, n2, n3, n4, hH, a5⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf hheld
  have hl : (s.gpr .a4).toNat ≤ 255 * w.H.D := by
    have := (hH _ (hashAt_tableOf hh.2.1)).1; rwa [w.t.l.len] at this
  rw [List.append_eq, List.append_nil] at hpw
  exact ⟨⟨hrd, hwr, hl, d1, d2, d3.symm, hsp, hN, d4, d5, d6, d7, n1, n2, n3, n4, a5, hh.1, hh.2.2.1, hh.2.2.2,
    tabOK_of hO.1 hpw hv⟩, hh.2.1⟩

theorem expand_pub {s₁ s₂ : State} (h₁ : ExpandFacts vs s₁) (h₂ : ExpandFacts vs s₂)
    (h : (specExpand vs).pub s₁ s₂) : (expandTab vs).pub s₁ s₂ := by
  sig_pub [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    RISCV64.abi, RISCV64.argRegs, stackBelow, eStack, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, hn, hT, e0, e1, e2, e3, e4, e5⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  exact ⟨w, hv, f₁ w hv hh, h₂.2 w hv ((hT _ _ rfl rfl _ (List.mem_map_of_mem hv)).mp hh),
    hsp, e0, e1, e2, e3, e4, e5, hn⟩

theorem expand_implies (hO : OK vs) (hsat : ∃ s, (specExpand vs).pre s) :
    (expandTab vs).Implies (specExpand vs) := by
  refine ⟨fun s h => ?_, fun s s' h hp => ?_,
    fun s₁ s₂ h₁ h₂ hp => expand_pub (expand_pre hO h₁) (expand_pre hO h₂) hp, hsat⟩
  · obtain ⟨⟨w, hv, hh⟩, f⟩ := expand_pre hO h
    exact ⟨w, hv, f w hv hh⟩
  · sig_post [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig, Spec.Hkdf.expandPost,
      Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
      RISCV64.abi, RISCV64.argRegs, stackBelow, eStack, String.reduceEq, Option.map_some,
      List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
      List.append_nil, names_eq]
    exact fun H S prk a b c => hp H S prk a b c

/-- A state meeting the contract: the states at `0x1000`, 16 bytes of `info`
at `0x2000`, 32 bytes of `out` at `0x3000`, the table of a hash function of
`vs` at `0x300000`. -/
def expandSat (vs : List HVar) (w : HVar) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 16 | .a3 => 0x3000 | .a4 => 32 | .a5 => 0x300000 | _ => 0
  sp := 0x20000
  mem := tabMem vs w
  rd := [⟨0x1000, 384⟩, ⟨0x2000, 16⟩, ⟨0x300000, 48⟩]
  wr := [⟨0x3000, 32⟩]
  syms := symT vs

theorem expand_sat (hO : OK vs) (hS : Streams vs) : ∃ s, (specExpand vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2
  refine ⟨expandSat vs w, ?_⟩
  sig_pre [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig, Spec.Hkdf.expandPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    RISCV64.abi, RISCV64.argRegs, stackBelow, eStack, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq]
  have hh := held_tableOf (tabMem_held vs w (expandSat vs w) rfl)
  have hG : Spec.HmacTable.hashAt 64 (expandSat vs w).mem 0x300000 = some w.G := hashAt_tableOf hh.2.1
  have hD0 := w.hH.hD0
  simp only [expandSat] at hG ⊢
  sig_and_intros
  all_goals first
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, tabMem_held vs w (expandSat vs w) rfl⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega)
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       refine ⟨?_, by rw [hS w hv]; rfl⟩
       rw [w.t.l.len]
       show 32 ≤ 255 * w.H.D
       omega_using [hD0])

/-- `vg_hkdf_expand`, with the tables of `vs`, meets `Spec.Hkdf.expandContract`. -/
theorem expand_spec (hO : OK vs) (hS : Streams vs) :
    Verified RISCV64.target (Impl.Hkdf.RISCV64.expand (fnsOf vs)) (specExpand vs) :=
  Verified.of_correct (fun _ h => expandT_ok hS h) expandT_ct (expand_implies hO (expand_sat hO hS))

end

end VG.Proof.Hkdf.RISCV64
