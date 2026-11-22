module

public import VerifiedGarbage.Proof.Hkdf.X86_64.Key
public import VerifiedGarbage.Proof.Hkdf.X86_64.Extract
public import VerifiedGarbage.Proof.Hkdf.X86_64.Expand
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.HashTable.Basic
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# HKDF on x86-64: the contracts with the hash function as a table

Each function is one body, which loads `D` and `B` from the table `hmac`
and calls the table's functions. For the variants `vs` whose tables it
takes (`OK`: their functions of the same name have the same code, their
sizes fit the frames (`HOk`), and each's streaming states are the
specification's for its hash function, `Streams`), the table of each `w`
makes the body meet the contract with `w` fixed (`keyR`, `key_correct`,
`key_ct`). `keyTab` states that contract for whichever of the tables `hmac`
holds, on entry, which the specification's contract with the tables of `vs`
implies (`key_implies`): the table `hmac` points to is one of `vs`', whose
words give the contract the proof is written against; its hash function is
the one the table names; and two runs whose public data agree take the same
table. A state meets it (`key_sat`): the buffers at fixed addresses, the
table of a variant of `vs` at `0x300000`, the functions of `vs` at distinct
addresses.
-/

@[expose] public section

namespace VG.Proof.Hkdf.X86_64

open VG VG.X86_64
open VG.Impl.Hkdf.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.HmacTable.X86_64 (tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf
  hashAt_tableOf put6_held symT symT_distinct)

/-- What the registrations check of the variants whose tables the functions
take: the functions of the same name have the same code, there are fewer
than `2 ^ 32` names, there is one, and each's sizes fit the frames. -/
def OK (vs : List MdHash) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ [] ∧ ∀ w ∈ vs, HOk w

instance (vs : List MdHash) : Decidable (OK vs) := by unfold OK; infer_instance

/-- Each variant's streaming states are those the specification gives its
hash function (`Spec.Hkdf.streamingOf`). -/
def Streams (vs : List MdHash) : Prop := ∀ w ∈ vs, Spec.Hkdf.streamingOf w.mgf.G = some w.ok.SH

theorem tableRegion_eq (p : Addr) : Sig.tableRegion 64 p 6 = ⟨p, 48⟩ := rfl

theorem names_eq (vs : List MdHash) : (List.map (fun x => x.fns) (tables vs)).flatten = names vs := rfl

/-- The table `hmac` (in `r`) points to holds `w`'s. -/
abbrev HeldW (r : Reg) (w : MdHash) (s : State) : Prop :=
  Abi.tableHeld 64 s.mem (s.gpr r) (FnTable.words isa s (tableOf w))

/-- The table's index, as the table of `w` holds it. -/
abbrev IdxW (r : Reg) (w : MdHash) (s : State) : Prop :=
  s.mem.readW (s.gpr r + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G)

/-- The hash function a table of `w` names, and its streaming states. -/
theorem streams_of {vs : List MdHash} (hS : Streams vs) {w : MdHash} (hv : w ∈ vs) {m : Mem} {p : Addr}
    (h : m.readW (p + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G))
    {H : Spec.Mgf1.Hash} {S : Spec.Hmac.StreamingHash} (hH : Spec.HmacTable.hashAt 64 m p = some H)
    (hSt : Spec.Hkdf.streamingOf H = some S) : S = w.ok.SH := by
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf h))
  exact Option.some.inj (hSt.symm.trans (hS w hv))

/-! ## No instruction loads MXCSR -/

theorem icalls_mx : ∀ {ts : List (String × Prog isa)}, (∀ q ∈ ts, q.2.allInstrs (fun i => !loadsMxcsr i) = true) →
    (Code.icalls (.callr .r11) ts).allInstrs (fun i => !loadsMxcsr i) = true
  | [], _ => rfl
  | q :: ts, h => by
    have hq := h q (List.mem_cons_self ..)
    have ih := icalls_mx (ts := ts) fun r hr => h r (List.mem_cons_of_mem _ hr)
    show (Code.icalls (.callr .r11) (q :: ts)).allInstrs _ = true
    simp only [Code.icalls, Code.allInstrs, hq, ih, Bool.and_true]; rfl

theorem init_mx (vs : List MdHash) : ∀ q ∈ (fnsOf vs).init, q.2.allInstrs (fun i => !loadsMxcsr i) = true := by
  intro q hq; obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq; exact w.hmacAnyMx

theorem key_mx (vs : List MdHash) : (key (fnsOf vs)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [key, keyMain, Code.allInstrs, icalls_mx (init_mx vs), Bool.and_true]
  rfl

/-! ## `vg_hkdf_key` -/

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specKey (vs : List MdHash) : Contract isa :=
  Spec.Hkdf.keyContract (X86_64.abi.withTables Spec.Hkdf.keySig [("hmac", tables vs)]) kStack

/-- The contract with the table of `w`, and its index. -/
def KeyW (vs : List MdHash) (w : MdHash) (s : State) : Prop :=
  (keyR w (fnsOf vs) (names vs) kStack).pre s ∧ IdxW .rcx w s

/-- The contract with whichever of the tables of `vs` the table at `rcx` is. -/
def keyTab (vs : List MdHash) : Contract isa where
  pre s := ∃ w ∈ vs, KeyW vs w s
  post s s' := ∀ H S, Spec.HmacTable.hashAt 64 s.mem (s.gpr .rcx) = some H → Spec.Hkdf.streamingOf H = some S →
    Spec.Hkdf.Keyed S s'.mem (s.gpr .rdx) (Spec.Sha256.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s₁ s₂ := ∃ w ∈ vs, KeyW vs w s₁ ∧ KeyW vs w s₂ ∧ (keyR w (fnsOf vs) (names vs) kStack).pub s₁ s₂

section
variable {vs : List MdHash}

theorem keyT_ok (hO : OK vs) (hS : Streams vs) {s : State} (h : (keyTab vs).pre s) :
    ∃ t s', Exec isa (key (fnsOf vs)) s t s' ∧ abiPreserved s s' ∧ (keyTab vs).post s s' := by
  obtain ⟨w, hv, hp, hix⟩ := h
  obtain ⟨t, s', he, ⟨hg, hpost⟩⟩ := key_correct (hO.2.2.2 w hv) hp
  refine ⟨t, s', he, abiPreserved_of_exec (key_mx vs) he hg, fun H S hH hSt => ?_⟩
  rw [streams_of hS hv hix hH hSt]
  exact hpost

theorem keyT_ct (hO : OK vs) : ConstantTime isa (keyTab vs).pre (keyTab vs).pub (key (fnsOf vs)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, p₁, p₂, hpub⟩ e₁ e₂
  exact key_ct (hO.2.2.2 w hv) (mem_names hv).1 s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract on entry. -/
def KeyFacts (vs : List MdHash) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW .rcx w s) ∧ ∀ w ∈ vs, HeldW .rcx w s → KeyW vs w s

theorem key_pre (hO : OK vs) {s : State} (h : (specKey vs).pre s) : KeyFacts vs s := by
  sig_pre [Spec.Hkdf.keyContract, Spec.Hkdf.keySig, Spec.Hkdf.keyPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86_64.abi, X86_64.argRegs, stackBelow, kStack, kFr, work, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, d1, d2, r1, r2, r3, k1, k2, k3, n1, n2, n3, -⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf hheld
  rw [List.append_eq, List.append_nil] at hpw
  exact ⟨⟨hsp, hrd, hwr, d1, d2, r1, r2, r3, k1, k2, k3, n1, n2, n3, hh.1, tabOK_of hO.1 hpw hv⟩, hh.2.1⟩

theorem key_pub {s₁ s₂ : State} (h₁ : KeyFacts vs s₁) (h₂ : KeyFacts vs s₂) (h : (specKey vs).pub s₁ s₂) :
    (keyTab vs).pub s₁ s₂ := by
  sig_pub [Spec.Hkdf.keyContract, Spec.Hkdf.keySig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86_64.abi, X86_64.argRegs, stackBelow, kStack, kFr, work, String.reduceEq, Option.map_some,
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
      X86_64.abi, X86_64.argRegs, stackBelow, kStack, kFr, work, String.reduceEq, Option.map_some,
      List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
      List.append_nil, names_eq]
    exact fun H S a b => hp H S a b

/-- The memory with the table of `w` at `0x300000`. -/
def tabMem (vs : List MdHash) (w : MdHash) : Mem :=
  Proof.HmacTable.X86_64.put6 (fun _ => 0) 0x300000 (symT vs w.H.hmacInitAnyN) (symT vs w.H.updN)
    (symT vs w.H.hmacFinN) (BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G)) (BitVec.ofNat 64 w.mgf.G.len)
    (BitVec.ofNat 64 (Spec.HmacTable.blockSize w.mgf.G))

theorem tabMem_held (vs : List MdHash) (w : MdHash) (s : State) (hs : s.syms = symT vs) :
    Abi.tableHeld 64 (tabMem vs w) 0x300000 (FnTable.words isa s (tableOf w)) := by
  rw [Proof.HmacTable.X86_64.words_tableOf, hs]
  exact put6_held (ws := [symT vs w.H.hmacInitAnyN, symT vs w.H.updN, symT vs w.H.hmacFinN,
    BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G), BitVec.ofNat 64 w.mgf.G.len,
    BitVec.ofNat 64 (Spec.HmacTable.blockSize w.mgf.G)]) rfl

/-- A state meeting the contract: `PRK` (32 bytes) at `0x1000`, `key` at
`0x2000`, the table of a variant of `vs` at `0x300000`. -/
def keySat (vs : List MdHash) (w : MdHash) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 32 | .rdx => 0x2000 | .rcx => 0x300000 | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := tabMem vs w
  rd := [⟨0x1000, 32⟩, ⟨0x300000, 48⟩]
  wr := [⟨0x2000, 384⟩]
  syms := symT vs

theorem key_sat (hO : OK vs) (hS : Streams vs) : ∃ s, (specKey vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  refine ⟨keySat vs w, ?_⟩
  sig_pre [Spec.Hkdf.keyContract, Spec.Hkdf.keySig, Spec.Hkdf.keyPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86_64.abi, X86_64.argRegs, stackBelow, kStack, kFr, work, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq]
  have hh := held_tableOf (tabMem_held vs w (keySat vs w) rfl)
  have hG : Spec.HmacTable.hashAt 64 (keySat vs w).mem 0x300000 = some w.mgf.G := hashAt_tableOf hh.2.1
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
theorem key_spec (hO : OK vs) (hS : Streams vs) : Verified X86_64.target (key (fnsOf vs)) (specKey vs) :=
  Verified.of_correct (fun _ h => keyT_ok hO hS h) (keyT_ct hO) (key_implies hO (key_sat hO hS))

end

/-! ## `vg_hkdf_extract` -/

open Extract (extractR xStack)

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specExtract (vs : List MdHash) : Contract isa :=
  Spec.Hkdf.extractContract (X86_64.abi.withTables Spec.Hkdf.extractSig [("hmac", tables vs)]) xStack

/-- The table's index, as the table of `w` holds it, at the stack argument. -/
abbrev IdxA (w : MdHash) (s : State) : Prop :=
  s.mem.readW (stackArg s 0 + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G)

/-- The contract with the table of `w`, and its index. -/
def ExtractW (vs : List MdHash) (w : MdHash) (s : State) : Prop :=
  (extractR w (fnsOf vs) (names vs) xStack).pre s ∧ IdxA w s

/-- The contract with whichever of the tables of `vs` the table on the stack is. -/
def extractTab (vs : List MdHash) : Contract isa where
  pre s := ∃ w ∈ vs, ExtractW vs w s
  post s s' := ∀ H F, Spec.HmacTable.hashAt 64 s.mem (stackArg s 0) = some H → Spec.HmacTable.hmacOf H = some F →
    Spec.Sha256.bytesAt s'.mem (s.gpr .r8) H.len = Spec.Hkdf.extract F
      (Spec.Sha256.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (Spec.Sha256.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ := ∃ w ∈ vs, ExtractW vs w s₁ ∧ ExtractW vs w s₂ ∧ (extractR w (fnsOf vs) (names vs) xStack).pub s₁ s₂

/-- The HMAC of a variant's hash function. -/
theorem hmac_of {vs : List MdHash} (hS : Streams vs) {w : MdHash} (hv : w ∈ vs) :
    Spec.HmacTable.hmacOf w.mgf.G = some w.ok.SH.H :=
  Spec.Hkdf.streamingOf_hmacOf _ _ (hS w hv)

theorem upd_mx (vs : List MdHash) : ∀ q ∈ (fnsOf vs).upd, q.2.allInstrs (fun i => !loadsMxcsr i) = true := by
  intro q hq; obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq; exact w.ok.updMx

theorem fin_mx (vs : List MdHash) : ∀ q ∈ (fnsOf vs).fin, q.2.allInstrs (fun i => !loadsMxcsr i) = true := by
  intro q hq; obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
  exact Proof.Pbkdf2.Md.X86_64.core_hmacFin w.K.cMx w.C.hfinMx

theorem extract_mx (vs : List MdHash) : (extract (fnsOf vs)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [extract, extractMain, Impl.Mgf1.X86_64.seqs, tcall, Code.allInstrs, icalls_mx (init_mx vs),
    icalls_mx (upd_mx vs), icalls_mx (fin_mx vs), Bool.and_true]
  rfl

section
variable {vs : List MdHash}

theorem extractT_ok (hO : OK vs) (hS : Streams vs) {s : State} (h : (extractTab vs).pre s) :
    ∃ t s', Exec isa (extract (fnsOf vs)) s t s' ∧ abiPreserved s s' ∧ (extractTab vs).post s s' := by
  obtain ⟨w, hv, hp, hix⟩ := h
  obtain ⟨t, s', he, ⟨hg, hpost⟩⟩ := Extract.extract_correct (hO.2.2.2 w hv) hp
  refine ⟨t, s', he, abiPreserved_of_exec (extract_mx vs) he hg, fun H F hH hF => ?_⟩
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf hix))
  obtain rfl := Option.some.inj (hF.symm.trans (hmac_of hS hv))
  rw [w.mgf.len]
  exact hpost

theorem extractT_ct (hO : OK vs) :
    ConstantTime isa (extractTab vs).pre (extractTab vs).pub (extract (fnsOf vs)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, p₁, p₂, hpub⟩ e₁ e₂
  have hn := mem_names hv
  exact Extract.extract_ct (hO.2.2.2 w hv) (fun n h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      exacts [hn.1, hn.2.1, hn.2.2])
    s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract on entry. -/
def ExtractFacts (vs : List MdHash) (s : State) : Prop :=
  (∃ w ∈ vs, Abi.tableHeld 64 s.mem (stackArg s 0) (FnTable.words isa s (tableOf w))) ∧
    ∀ w ∈ vs, Abi.tableHeld 64 s.mem (stackArg s 0) (FnTable.words isa s (tableOf w)) → ExtractW vs w s

theorem extract_pre (hO : OK vs) (hS : Streams vs) {s : State} (h : (specExtract vs).pre s) : ExtractFacts vs s := by
  sig_pre [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86_64.abi, X86_64.argRegs, stackBelow, xStack, xFr, xWork, work, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq, List.range, List.range.loop] at h
  obtain ⟨hsp, htop, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, d1, d2, d3, -, -, -, r3, -, -, k1, k2, k3, k4, -,
    n1, n2, n3, n4, hP⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf hheld
  have hG : Spec.HmacTable.hashAt 64 s.mem (stackArg s 0) = some w.mgf.G := hashAt_tableOf hh.2.1
  have hB : Spec.HmacTable.blockSize w.mgf.G = w.H.P.B := by
    simp only [Spec.HmacTable.blockSize, hmac_of hS hv, Option.map_some, Option.getD_some]; exact w.ok.hB
  rw [List.append_eq, List.append_nil] at hpw
  refine ⟨⟨hsp, htop, hrd, hwr, d1, d2, d3, r3, k1, k2, k3, k4, n1, n2, n3, n4,
    by rw [(hP _ hG).1, w.mgf.len], hh.1, by rw [hh.2.2.2, hB], tabOK_of hO.1 hpw hv⟩, hh.2.1⟩

theorem extract_pub {s₁ s₂ : State} (h₁ : ExtractFacts vs s₁) (h₂ : ExtractFacts vs s₂)
    (h : (specExtract vs).pub s₁ s₂) : (extractTab vs).pub s₁ s₂ := by
  sig_pub [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86_64.abi, X86_64.argRegs, stackBelow, xStack, xFr, xWork, work, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq, List.range, List.range.loop] at h
  obtain ⟨hsp, hn, hT, e0, e1, e2, e3, e4, e5, e6⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  exact ⟨w, hv, f₁ w hv hh, h₂.2 w hv ((hT _ _ rfl rfl _ (List.mem_map_of_mem hv)).mp hh),
    hsp, e0, e1, e2, e3, e4, e5, e6, hn⟩

/-- The contract with the tables of `vs`, given a state that meets it. -/
theorem extract_implies (hO : OK vs) (hS : Streams vs) (hsat : ∃ s, (specExtract vs).pre s) :
    (extractTab vs).Implies (specExtract vs) := by
  refine ⟨fun s h => ?_, fun s s' h hp => ?_, fun s₁ s₂ h₁ h₂ hp =>
    extract_pub (extract_pre hO hS h₁) (extract_pre hO hS h₂) hp, hsat⟩
  · obtain ⟨⟨w, hv, hh⟩, f⟩ := extract_pre hO hS h
    exact ⟨w, hv, f w hv hh⟩
  · sig_post [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPost,
      Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
      X86_64.abi, X86_64.argRegs, stackBelow, xStack, xFr, xWork, work, String.reduceEq, Option.map_some,
      List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
      List.append_nil, names_eq, List.range, List.range.loop]
    exact fun H F a b => hp H F a b

/-- The memory with the table of `w` at `0x300000`, and its address in the
stack argument at `0x20008`. -/
def extractMem (vs : List MdHash) (w : MdHash) : Mem :=
  Proof.HmacTable.X86_64.put6 (Mem.writeW (fun _ => 0) 0x20008 (0x300000 : BitVec 64)) 0x300000
    (symT vs w.H.hmacInitAnyN) (symT vs w.H.updN) (symT vs w.H.hmacFinN)
    (BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G)) (BitVec.ofNat 64 w.mgf.G.len)
    (BitVec.ofNat 64 (Spec.HmacTable.blockSize w.mgf.G))

/-- A state meeting the contract: the salt and the input keying material
(16 bytes each) at `0x1000` and `0x2000`, `PRK` at `0x3000`, the table of a
variant of `vs` at `0x300000`. -/
def extractSat (vs : List MdHash) (w : MdHash) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 16 | .r8 => 0x3000
    | .r9 => BitVec.ofNat 64 w.H.D | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := extractMem vs w
  rd := [⟨0x1000, 16⟩, ⟨0x2000, 16⟩, ⟨0x300000, 48⟩, ⟨0x20008, 8⟩]
  wr := [⟨0x3000, w.H.D⟩]
  syms := symT vs

theorem extractSat_argAddr (vs : List MdHash) (w : MdHash) : stackArgAddr (extractSat vs w) 0 = 0x20008 := by
  simp only [stackArgAddr, extractSat]; decide

theorem extractSat_arg (vs : List MdHash) (w : MdHash) : stackArg (extractSat vs w) 0 = 0x300000 := by
  simp only [stackArg, extractSat_argAddr]
  rw [show (extractSat vs w).mem = extractMem vs w from rfl, extractMem,
    Proof.HmacTable.X86_64.put6_below (by decide), Mem.readW_writeW_self64]

theorem extract_sat (hO : OK vs) (hS : Streams vs) : ∃ s, (specExtract vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hD : w.H.D ≤ 64 := by have := w.ok.hDN; have := w.ok.N_le; omega_arith
  have hD0 : 0 < w.H.D := w.ok.hD0
  refine ⟨extractSat vs w, ?_⟩
  sig_pre [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86_64.abi, X86_64.argRegs, stackBelow, xStack, xFr, xWork, work, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq, List.range, List.range.loop]
  simp only [extractSat_arg, extractSat_argAddr]
  have hheld : Abi.tableHeld 64 (extractSat vs w).mem 0x300000 (FnTable.words isa (extractSat vs w) (tableOf w)) := by
    rw [Proof.HmacTable.X86_64.words_tableOf]
    exact put6_held (ws := [symT vs w.H.hmacInitAnyN, symT vs w.H.updN, symT vs w.H.hmacFinN,
      BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G), BitVec.ofNat 64 w.mgf.G.len,
      BitVec.ofNat 64 (Spec.HmacTable.blockSize w.mgf.G)]) rfl
  have hh := held_tableOf hheld
  have hG : Spec.HmacTable.hashAt 64 (extractSat vs w).mem 0x300000 = some w.mgf.G := hashAt_tableOf hh.2.1
  have h9 : ((extractSat vs w).gpr .r9).toNat = w.H.D := by
    show (BitVec.ofNat 64 w.H.D).toNat = _; rw [BitVec.toNat_ofNat]; omega_using [hD]
  simp only [extractSat] at hG h9 ⊢
  simp only [h9]
  sig_and_intros
  all_goals first
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, hheld⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega)
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨by rw [w.mgf.len], by rw [hmac_of hS hv]; rfl⟩)

/-- `vg_hkdf_extract`, with the tables of `vs`, meets `Spec.Hkdf.extractContract`. -/
theorem extract_spec (hO : OK vs) (hS : Streams vs) :
    Verified X86_64.target (extract (fnsOf vs)) (specExtract vs) :=
  Verified.of_correct (fun _ h => extractT_ok hO hS h) (extractT_ct hO) (extract_implies hO hS (extract_sat hO hS))

end

/-! ## `vg_hkdf_expand` -/

open Expand (expandR eStack)

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specExpand (vs : List MdHash) : Contract isa :=
  Spec.Hkdf.expandContract (X86_64.abi.withTables Spec.Hkdf.expandSig [("hmac", tables vs)]) eStack

/-- The contract with the table of `w`, and its index. -/
def ExpandW (vs : List MdHash) (w : MdHash) (s : State) : Prop :=
  (expandR w (fnsOf vs) (names vs) eStack).pre s ∧ IdxW .r9 w s

/-- The contract with whichever of the tables of `vs` the table at `r9` is. -/
def expandTab (vs : List MdHash) : Contract isa where
  pre s := ∃ w ∈ vs, ExpandW vs w s
  post s s' := ∀ H S prk, Spec.HmacTable.hashAt 64 s.mem (s.gpr .r9) = some H → Spec.Hkdf.streamingOf H = some S →
    Spec.Hkdf.Keyed S s.mem (s.gpr .rdi) prk →
    Spec.Hkdf.expand S.H H.len prk (Spec.Sha256.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) (s.gpr .r8).toNat =
      some (Spec.Sha256.bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat)
  pub s₁ s₂ := ∃ w ∈ vs, ExpandW vs w s₁ ∧ ExpandW vs w s₂ ∧ (expandR w (fnsOf vs) (names vs) eStack).pub s₁ s₂

theorem expand_mx (vs : List MdHash) : (expand (fnsOf vs)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [expand, expandMain, block, outLen, outCopy, Impl.Mgf1.X86_64.byteLoop, Impl.Mgf1.X86_64.seqs, tcall,
    Code.allInstrs, icalls_mx (upd_mx vs), icalls_mx (fin_mx vs), Bool.and_true]
  rfl

section
variable {vs : List MdHash}

theorem expandT_ok (hO : OK vs) (hS : Streams vs) {s : State} (h : (expandTab vs).pre s) :
    ∃ t s', Exec isa (expand (fnsOf vs)) s t s' ∧ abiPreserved s s' ∧ (expandTab vs).post s s' := by
  obtain ⟨w, hv, hp, hix⟩ := h
  obtain ⟨t, s', he, ⟨hg, hpost⟩⟩ := Expand.expand_correct (hO.2.2.2 w hv) hp
  refine ⟨t, s', he, abiPreserved_of_exec (expand_mx vs) he hg, fun H S prk hH hSt hK => ?_⟩
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf hix))
  obtain rfl := streams_of hS hv hix hH hSt
  rw [w.mgf.len]
  exact hpost prk hK

theorem expandT_ct (hO : OK vs) :
    ConstantTime isa (expandTab vs).pre (expandTab vs).pub (expand (fnsOf vs)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, p₁, p₂, hpub⟩ e₁ e₂
  have hn := mem_names hv
  exact Expand.expand_ct (hO.2.2.2 w hv) (fun n h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      exacts [hn.2.1, hn.2.2])
    s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract on entry. -/
def ExpandFacts (vs : List MdHash) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW .r9 w s) ∧ ∀ w ∈ vs, HeldW .r9 w s → ExpandW vs w s

theorem expand_pre (hO : OK vs) (hS : Streams vs) {s : State} (h : (specExpand vs).pre s) : ExpandFacts vs s := by
  sig_pre [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig, Spec.Hkdf.expandPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86_64.abi, X86_64.argRegs, stackBelow, eStack, eFr, eWork, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, d1, d2, d3, -, -, r3, -, k1, k2, k3, k4, n1, n2, n3, n4, hP⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf hheld
  have hG : Spec.HmacTable.hashAt 64 s.mem (s.gpr .r9) = some w.mgf.G := hashAt_tableOf hh.2.1
  have hB : Spec.HmacTable.blockSize w.mgf.G = w.H.P.B := by
    simp only [Spec.HmacTable.blockSize, hmac_of hS hv, Option.map_some, Option.getD_some]; exact w.ok.hB
  rw [List.append_eq, List.append_nil] at hpw
  refine ⟨⟨hsp, hrd, hwr, d1, d2, d3, r3, k1, k2, k3, k4, n1, n2, n3, n4,
    by rw [← w.mgf.len]; exact (hP _ hG).1, hh.1, hh.2.2.1, by rw [hh.2.2.2, hB], tabOK_of hO.1 hpw hv⟩, hh.2.1⟩

end

section
variable {vs : List MdHash}

theorem expand_pub {s₁ s₂ : State} (h₁ : ExpandFacts vs s₁) (h₂ : ExpandFacts vs s₂)
    (h : (specExpand vs).pub s₁ s₂) : (expandTab vs).pub s₁ s₂ := by
  sig_pub [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86_64.abi, X86_64.argRegs, stackBelow, eStack, eFr, eWork, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, hn, hT, e0, e1, e2, e3, e4, e5⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  exact ⟨w, hv, f₁ w hv hh, h₂.2 w hv ((hT _ _ rfl rfl _ (List.mem_map_of_mem hv)).mp hh),
    hsp, e0, e1, e2, e3, e4, e5, hn⟩

/-- The contract with the tables of `vs`, given a state that meets it. -/
theorem expand_implies (hO : OK vs) (hS : Streams vs) (hsat : ∃ s, (specExpand vs).pre s) :
    (expandTab vs).Implies (specExpand vs) := by
  refine ⟨fun s h => ?_, fun s s' h hp => ?_, fun s₁ s₂ h₁ h₂ hp =>
    expand_pub (expand_pre hO hS h₁) (expand_pre hO hS h₂) hp, hsat⟩
  · obtain ⟨⟨w, hv, hh⟩, f⟩ := expand_pre hO hS h
    exact ⟨w, hv, f w hv hh⟩
  · sig_post [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig, Spec.Hkdf.expandPost,
      Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
      X86_64.abi, X86_64.argRegs, stackBelow, eStack, eFr, eWork, String.reduceEq, Option.map_some,
      List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
      List.append_nil, names_eq]
    exact fun H S prk a b c => hp H S prk a b c

/-- A state meeting the contract: the states at `0x1000`, `info` (16 bytes)
at `0x2000`, 16 bytes of `out` at `0x3000`, the table of a variant of `vs`
at `0x300000`. -/
def expandSat (vs : List MdHash) (w : MdHash) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 16 | .rcx => 0x3000 | .r8 => 16 | .r9 => 0x300000
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := tabMem vs w
  rd := [⟨0x1000, 384⟩, ⟨0x2000, 16⟩, ⟨0x300000, 48⟩]
  wr := [⟨0x3000, 16⟩]
  syms := symT vs

theorem expand_sat (hO : OK vs) (hS : Streams vs) : ∃ s, (specExpand vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hD0 : 0 < w.H.D := w.ok.hD0
  refine ⟨expandSat vs w, ?_⟩
  sig_pre [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig, Spec.Hkdf.expandPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86_64.abi, X86_64.argRegs, stackBelow, eStack, eFr, eWork, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq]
  have hh := held_tableOf (tabMem_held vs w (expandSat vs w) rfl)
  have hG : Spec.HmacTable.hashAt 64 (expandSat vs w).mem 0x300000 = some w.mgf.G := hashAt_tableOf hh.2.1
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
       have h16 : (16 : BitVec 64).toNat = 16 := rfl
       refine ⟨by rw [w.mgf.len, h16]; omega_using [hD0], by rw [hS w hv]; rfl⟩)

/-- `vg_hkdf_expand`, with the tables of `vs`, meets `Spec.Hkdf.expandContract`. -/
theorem expand_spec (hO : OK vs) (hS : Streams vs) :
    Verified X86_64.target (expand (fnsOf vs)) (specExpand vs) :=
  Verified.of_correct (fun _ h => expandT_ok hO hS h) (expandT_ct hO) (expand_implies hO hS (expand_sat hO hS))

end

end VG.Proof.Hkdf.X86_64
