module

public import VerifiedGarbage.Proof.Hkdf.Arm.Key
public import VerifiedGarbage.Proof.Hkdf.Arm.Extract
public import VerifiedGarbage.Proof.Hkdf.Arm.Expand
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.HashTable.Basic
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# HKDF on 32-bit ARM: the contracts with the hash function as a table

As on AArch64 (`Proof/Hkdf/AArch64/Table.lean`): each function is one body,
which loads `D` and `B` from the table `hmac` and calls the table's
functions. For the variants `vs` whose tables it takes (`OK`: their
functions of the same name have the same code, their sizes fit the frames
(`HOk`), and each's streaming states are the specification's for its hash
function, `Streams`), the table of each `w` makes the body meet the
contract with `w` fixed (`keyR`, `key_correct`, `key_ct`). `keyTab` states
that contract for whichever of the tables `hmac` holds, on entry, which the
specification's contract with the tables of `vs` implies (`key_implies`).
A state meets it (`key_sat`): the buffers at fixed addresses, the stack
arguments at `0x9000`, the table of a variant at `0x300000`, the functions
of `vs` at distinct addresses (`symT`).
-/

@[expose] public section

namespace VG.Proof.Hkdf.Arm

open VG VG.Arm
open VG.Impl.Hkdf.Arm
open VG.Proof.HmacTable.Arm (HVar tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf
  hashAt_tableOf readW_sepW put6w put6w_held put6w_below put2w symT symT_distinct tA)

/-- What the registrations check of the variants whose tables the functions
take: the functions of the same name have the same code, there are fewer
than `2 ^ 24` names, there is one, and each's sizes fit the frames. -/
def OK (vs : List HVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 24 ∧ vs ≠ [] ∧ ∀ w ∈ vs, HOk w

/-- Each variant's streaming states are those the specification gives its
hash function (`Spec.Hkdf.streamingOf`). -/
def Streams (vs : List HVar) : Prop := ∀ w ∈ vs, Spec.Hkdf.streamingOf w.G = some w.ok.hH.SH

theorem tableRegion_eq (p : Addr) : Sig.tableRegion 32 p 6 = ⟨p, 24⟩ := rfl

theorem names_eq (vs : List HVar) : (List.map (fun x => x.fns) (tables vs)).flatten = names vs := rfl

theorem argAddr0 (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]

/-- The table at `p` holds `w`'s. -/
abbrev HeldW (p : BitVec 32) (w : HVar) (s : State) : Prop :=
  Abi.tableHeld 32 s.mem (State.addr p) (FnTable.words isa s (tableOf w))

/-- The table's index, as the table of `w` holds it. -/
abbrev IdxW (p : BitVec 32) (w : HVar) (s : State) : Prop :=
  s.mem.readW (tA p 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.G)

/-- The hash function a table of `w` names, and its streaming states. -/
theorem streams_of {vs : List HVar} (hS : Streams vs) {w : HVar} (hv : w ∈ vs) {m : Mem} {p : BitVec 32}
    (hp : p.toNat + 24 ≤ 2 ^ 32) (h : m.readW (tA p 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.G))
    {H : Spec.Mgf1.Hash} {S : Spec.Hmac.StreamingHash} (hH : Spec.HmacTable.hashAt 32 m (State.addr p) = some H)
    (hSt : Spec.Hkdf.streamingOf H = some S) : S = w.ok.hH.SH := by
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf hp h))
  exact Option.some.inj (hSt.symm.trans (hS w hv))

/-! ## States that meet the contracts -/

/-- The words of `w`'s table. -/
def tw6 (vs : List HVar) (w : HVar) : List (BitVec 64) :=
  [(symT vs w.F.hiAnyN).setWidth 64, (symT vs w.F.H.updN).setWidth 64, (symT vs w.F.hfN).setWidth 64,
    BitVec.ofNat 64 (Spec.HashTable.index w.G), BitVec.ofNat 64 w.G.len,
    BitVec.ofNat 64 (Spec.HmacTable.blockSize w.G)]

/-- The memory `m` with the table of `w` at `0x300000`. -/
def tabMem (vs : List HVar) (w : HVar) (m : Mem) : Mem :=
  put6w m 0x300000 (((tw6 vs w).getD 0 0).setWidth 32) (((tw6 vs w).getD 1 0).setWidth 32)
    (((tw6 vs w).getD 2 0).setWidth 32) (((tw6 vs w).getD 3 0).setWidth 32) (((tw6 vs w).getD 4 0).setWidth 32)
    (((tw6 vs w).getD 5 0).setWidth 32)

/-- A state with the table of `w` at `0x300000`, the stack pointer at
`0x9000` and the memory below the table `m`. -/
def satS (vs : List HVar) (w : HVar) (g : Reg → BitVec 32) (m : Mem) (rd wr : List Region) : State where
  gpr := g
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem := tabMem vs w m
  rd := rd
  wr := wr
  syms := symT vs

theorem satS_held (vs : List HVar) (w : HVar) (g : Reg → BitVec 32) (m : Mem) (rd wr : List Region) :
    HeldW 0x300000 w (satS vs w g m rd wr) := by
  rw [HeldW, show State.addr (0x300000 : BitVec 32) = 0x300000 by decide]
  exact put6w_held (ws := tw6 vs w) rfl

theorem satS_hash (vs : List HVar) (w : HVar) (g : Reg → BitVec 32) (m : Mem) (rd wr : List Region) :
    Spec.HmacTable.hashAt 32 (satS vs w g m rd wr).mem (State.addr (0x300000 : BitVec 32)) = some w.G :=
  hashAt_tableOf (by decide) (held_tableOf (by decide) (satS_held vs w g m rd wr)).2.1

/-- The stack arguments `w₀`, `w₁`, `w₂` at `0x9000`. -/
def put3w (m : Mem) (w₀ w₁ w₂ : BitVec 32) : Mem := (put2w m w₀ w₁).writeW 0x9008 w₂

theorem satS_arg (vs : List HVar) (w : HVar) (g : Reg → BitVec 32) (m : Mem) (rd wr : List Region) {i : Nat}
    (hi : i < 3) : stackArg (satS vs w g m rd wr) i = m.readW (State.addr (0x9000 + BitVec.ofNat 32 (4 * i))) 32 := by
  show (put6w m _ _ _ _ _ _ _).readW (State.addr (0x9000 + BitVec.ofNat 32 (4 * i))) 32 = _
  have : (State.addr (0x9000 + BitVec.ofNat 32 (4 * i))).toNat + 32 / 8 ≤ 0x300000 := by
    match i, hi with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
  rw [put6w_below (by decide) this]

theorem put3w_0 (m : Mem) (w₀ w₁ w₂ : BitVec 32) :
    (put3w m w₀ w₁ w₂).readW (State.addr (0x9000 + BitVec.ofNat 32 (4 * 0))) 32 = w₀ := by
  rw [show State.addr (0x9000 + BitVec.ofNat 32 (4 * 0)) = 0x9000 by decide]
  simp only [put3w, put2w]
  rw [readW_sepW (.inl (by decide)) (by decide) (by decide) (by decide),
    readW_sepW (.inl (by decide)) (by decide) (by decide) (by decide)]
  exact Mem.readW_writeW_self32 _ _ _

theorem put3w_1 (m : Mem) (w₀ w₁ w₂ : BitVec 32) :
    (put3w m w₀ w₁ w₂).readW (State.addr (0x9000 + BitVec.ofNat 32 (4 * 1))) 32 = w₁ := by
  rw [show State.addr (0x9000 + BitVec.ofNat 32 (4 * 1)) = 0x9004 by decide]
  simp only [put3w, put2w]
  rw [readW_sepW (.inl (by decide)) (by decide) (by decide) (by decide)]
  exact Mem.readW_writeW_self32 _ _ _

theorem put3w_2 (m : Mem) (w₀ w₁ w₂ : BitVec 32) :
    (put3w m w₀ w₁ w₂).readW (State.addr (0x9000 + BitVec.ofNat 32 (4 * 2))) 32 = w₂ := by
  rw [show State.addr (0x9000 + BitVec.ofNat 32 (4 * 2)) = 0x9008 by decide]
  exact Mem.readW_writeW_self32 _ _ _

theorem put2w_0 (m : Mem) (w₀ w₁ : BitVec 32) :
    (put2w m w₀ w₁).readW (State.addr (0x9000 + BitVec.ofNat 32 (4 * 0))) 32 = w₀ := by
  rw [show State.addr (0x9000 + BitVec.ofNat 32 (4 * 0)) = 0x9000 by decide]
  simp only [put2w]
  rw [readW_sepW (.inl (by decide)) (by decide) (by decide) (by decide)]
  exact Mem.readW_writeW_self32 _ _ _

theorem put2w_1 (m : Mem) (w₀ w₁ : BitVec 32) :
    (put2w m w₀ w₁).readW (State.addr (0x9000 + BitVec.ofNat 32 (4 * 1))) 32 = w₁ := by
  rw [show State.addr (0x9000 + BitVec.ofNat 32 (4 * 1)) = 0x9004 by decide]
  exact Mem.readW_writeW_self32 _ _ _

/-! ## `vg_hkdf_key` -/

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specKey (vs : List HVar) : Contract isa :=
  Spec.Hkdf.keyContract (Arm.abi.withTables Spec.Hkdf.keySig [("hmac", tables vs)]) kStack

/-- The contract with the table of `w`, and its index. -/
def KeyW (vs : List HVar) (w : HVar) (s : State) : Prop :=
  (keyR w (fnsOf vs) (names vs) kStack).pre s ∧ IdxW (s.gpr .r3) w s

/-- The contract with whichever of the tables of `vs` the table at `r3` is. -/
def keyTab (vs : List HVar) : Contract isa where
  pre s := ∃ w ∈ vs, KeyW vs w s
  post s s' := ∀ H S, Spec.HmacTable.hashAt 32 s.mem (State.addr (s.gpr .r3)) = some H →
    Spec.Hkdf.streamingOf H = some S →
    Spec.Hkdf.Keyed S s'.mem (State.addr (s.gpr .r2))
      (Spec.Sha256.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
  pub s₁ s₂ := ∃ w ∈ vs, KeyW vs w s₁ ∧ KeyW vs w s₂ ∧ (keyR w (fnsOf vs) (names vs) kStack).pub s₁ s₂

section
variable {vs : List HVar}

theorem keyT_ok (hO : OK vs) (hS : Streams vs) {s : State} (h : (keyTab vs).pre s) :
    ∃ t s', Exec isa (key (fnsOf vs)) s t s' ∧ abiPreserved s s' ∧ (keyTab vs).post s s' := by
  obtain ⟨w, hv, hp, hix⟩ := h
  have p := kp_of hp
  obtain ⟨t, s', he, hg, hpost⟩ := key_correct p (hO.2.2.2 w hv)
  refine ⟨t, s', he, hg, fun H S hH hSt => ?_⟩
  rw [streams_of hS hv p.nt hix hH hSt]
  exact hpost

theorem keyT_ct (hO : OK vs) : ConstantTime isa (keyTab vs).pre (keyTab vs).pub (key (fnsOf vs)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, p₁, p₂, hpub⟩ e₁ e₂
  exact key_ct (hO.2.2.2 w hv) (mem_names hv).1 s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract on entry. -/
def KeyFacts (vs : List HVar) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW (s.gpr .r3) w s) ∧ ∀ w ∈ vs, HeldW (s.gpr .r3) w s → KeyW vs w s

theorem key_pre (hO : OK vs) {s : State} (h : (specKey vs).pre s) : KeyFacts vs s := by
  sig_pre [Spec.Hkdf.keyContract, Spec.Hkdf.keySig, Spec.Hkdf.keyPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, stackBelow, kStack, kFr, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, tableRegion_eq, names_eq] at h
  obtain ⟨hsp, -, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, d1, d2, k1, k2, k3, n1, n2, n3, -⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf n3 hheld
  rw [List.append_eq, List.append_nil] at hpw
  exact ⟨⟨hsp, hrd, hwr, d1, d2, k1, k2, k3, n1, n2, n3, hh.1, tabOK_of hO.1 hpw hv⟩, hh.2.1⟩

theorem key_pub {s₁ s₂ : State} (h₁ : KeyFacts vs s₁) (h₂ : KeyFacts vs s₂) (h : (specKey vs).pub s₁ s₂) :
    (keyTab vs).pub s₁ s₂ := by
  sig_pub [Spec.Hkdf.keyContract, Spec.Hkdf.keySig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, stackBelow, kStack, kFr, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, tableRegion_eq, names_eq] at h
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
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, stackBelow, kStack, kFr, String.reduceEq,
      Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
      List.append_nil, tableRegion_eq, names_eq]
    exact fun H S a b => hp H S a b

/-- `key`'s arguments: `PRK` (32 bytes) at `0x1000`, `key` at `0x2000`, the
table at `0x300000`. -/
def keyG : Reg → BitVec 32
  | .r0 => 0x1000
  | .r1 => 32
  | .r2 => 0x2000
  | .r3 => 0x300000
  | _ => 0

/-- A state meeting the contract, with the table of a variant of `vs`. -/
def keySat (vs : List HVar) (w : HVar) : State :=
  satS vs w keyG (fun _ => 0) [⟨0x1000, 32⟩, ⟨0x300000, 24⟩] [⟨0x2000, 384⟩]

theorem key_sat (hO : OK vs) (hS : Streams vs) : ∃ s, (specKey vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  refine ⟨keySat vs w, ?_⟩
  have hG := satS_hash vs w keyG (fun _ => 0) [⟨0x1000, 32⟩, ⟨0x300000, 24⟩] [⟨0x2000, 384⟩]
  have hh := satS_held vs w keyG (fun _ => 0) [⟨0x1000, 32⟩, ⟨0x300000, 24⟩] [⟨0x2000, 384⟩]
  sig_pre [Spec.Hkdf.keyContract, Spec.Hkdf.keySig, Spec.Hkdf.keyPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, stackBelow, kStack, kFr, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, tableRegion_eq, names_eq]
  have hA : State.addr (0x9000 : BitVec 32) = 0x9000 := by decide
  simp only [keySat, satS, keyG, hA] at hG hh ⊢
  sig_and_intros
  all_goals first
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, hh⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega)
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       rw [hS w hv]; rfl)

/-- `vg_hkdf_key`, with the tables of `vs`, meets `Spec.Hkdf.keyContract`. -/
theorem key_spec (hO : OK vs) (hS : Streams vs) : Verified Arm.target (key (fnsOf vs)) (specKey vs) :=
  Verified.of_correct (fun _ h => keyT_ok hO hS h) (keyT_ct hO) (key_implies hO (key_sat hO hS))

end

/-! ## `vg_hkdf_extract` -/

open Extract (extractR xStack xp_of)

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specExtract (vs : List HVar) : Contract isa :=
  Spec.Hkdf.extractContract (Arm.abi.withTables Spec.Hkdf.extractSig [("hmac", tables vs)]) xStack

/-- The contract with the table of `w`, and its index. -/
def ExtractW (vs : List HVar) (w : HVar) (s : State) : Prop :=
  (extractR w (fnsOf vs) (names vs) xStack).pre s ∧ IdxW (stackArg s 2) w s

/-- The contract with whichever of the tables of `vs` the table, the third
stack argument, is. -/
def extractTab (vs : List HVar) : Contract isa where
  pre s := ∃ w ∈ vs, ExtractW vs w s
  post s s' := ∀ H F, Spec.HmacTable.hashAt 32 s.mem (State.addr (stackArg s 2)) = some H →
    Spec.HmacTable.hmacOf H = some F →
    Spec.Sha256.bytesAt s'.mem (State.addr (stackArg s 0)) H.len = Spec.Hkdf.extract F
      (Spec.Sha256.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
      (Spec.Sha256.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
  pub s₁ s₂ := ∃ w ∈ vs, ExtractW vs w s₁ ∧ ExtractW vs w s₂ ∧ (extractR w (fnsOf vs) (names vs) xStack).pub s₁ s₂

section
variable {vs : List HVar}

theorem extractT_ok (hO : OK vs) {s : State} (h : (extractTab vs).pre s) :
    ∃ t s', Exec isa (extract (fnsOf vs)) s t s' ∧ abiPreserved s s' ∧ (extractTab vs).post s s' := by
  obtain ⟨w, hv, hp, hix⟩ := h
  obtain ⟨t, s', he, hg, hpost⟩ := Extract.extract_correct (hO.2.2.2 w hv) hp
  refine ⟨t, s', he, hg, fun H F hH hF => ?_⟩
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf (xp_of hp).nt hix))
  obtain rfl := Option.some.inj (hF.symm.trans w.hmac)
  rw [w.glen]
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
def ExtractFacts (vs : List HVar) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW (stackArg s 2) w s) ∧ ∀ w ∈ vs, HeldW (stackArg s 2) w s → ExtractW vs w s

theorem extract_pre (hO : OK vs) {s : State} (h : (specExtract vs).pre s) : ExtractFacts vs s := by
  sig_pre [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, stackBelow, xStack, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, tableRegion_eq, names_eq, argAddr0] at h
  obtain ⟨hsp, h12, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, d1, d2, d3, d4, k1, k2, k3, k4, k5, n1, n2, n3, n4, hP⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf n4 hheld
  have hG : Spec.HmacTable.hashAt 32 s.mem (State.addr (stackArg s 2)) = some w.G := hashAt_tableOf n4 hh.2.1
  rw [List.append_eq, List.append_nil] at hpw
  exact ⟨⟨hsp, h12, hrd, hwr, d1, d2, d3, d4, k1, k2, k3, k4, k5, n1, n2, n3, n4,
    by rw [(hP _ hG).1, w.glen], hh.1, hh.2.2.2, tabOK_of hO.1 hpw hv⟩, hh.2.1⟩

theorem extract_pub {s₁ s₂ : State} (h₁ : ExtractFacts vs s₁) (h₂ : ExtractFacts vs s₂)
    (h : (specExtract vs).pub s₁ s₂) : (extractTab vs).pub s₁ s₂ := by
  sig_pub [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, stackBelow, xStack, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, tableRegion_eq, names_eq, argAddr0] at h
  obtain ⟨hsp, hn, hT, e0, e1, e2, e3, e4, e5, e6⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  exact ⟨w, hv, f₁ w hv hh, h₂.2 w hv ((hT _ _ rfl rfl _ (List.mem_map_of_mem hv)).mp hh),
    hsp, e0, e1, e2, e3, e4, e5, e6, hn⟩

/-- The contract with the tables of `vs`, given a state that meets it. -/
theorem extract_implies (hO : OK vs) (hsat : ∃ s, (specExtract vs).pre s) :
    (extractTab vs).Implies (specExtract vs) := by
  refine ⟨fun s h => ?_, fun s s' h hp => ?_, fun s₁ s₂ h₁ h₂ hp =>
    extract_pub (extract_pre hO h₁) (extract_pre hO h₂) hp, hsat⟩
  · obtain ⟨⟨w, hv, hh⟩, f⟩ := extract_pre hO h
    exact ⟨w, hv, f w hv hh⟩
  · sig_post [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPost,
      Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, stackBelow, xStack, String.reduceEq,
      Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
      List.append_nil, tableRegion_eq, names_eq, argAddr0]
    exact fun H F a b => hp H F a b

/-- `extract`'s arguments: the salt and the input keying material (16 bytes
each) at `0x1000` and `0x2000`. -/
def extractG : Reg → BitVec 32
  | .r0 => 0x1000
  | .r1 => 16
  | .r2 => 0x2000
  | .r3 => 16
  | _ => 0

/-- A state meeting the contract, with the table of a variant `w` of `vs`:
`PRK` at `0x3000`. -/
def extractSat (vs : List HVar) (w : HVar) : State :=
  satS vs w extractG (put3w (fun _ => 0) 0x3000 (BitVec.ofNat 32 w.F.H.D) 0x300000)
    [⟨0x1000, 16⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩, ⟨0x9000, 12⟩] [⟨0x3000, w.F.H.D⟩]

theorem extract_sat (hO : OK vs) : ∃ s, (specExtract vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hD := Expand.D_le w
  refine ⟨extractSat vs w, ?_⟩
  have hG := satS_hash vs w extractG (put3w (fun _ => 0) 0x3000 (BitVec.ofNat 32 w.F.H.D) 0x300000)
    [⟨0x1000, 16⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩, ⟨0x9000, 12⟩] [⟨0x3000, w.F.H.D⟩]
  have hh := satS_held vs w extractG (put3w (fun _ => 0) 0x3000 (BitVec.ofNat 32 w.F.H.D) 0x300000)
    [⟨0x1000, 16⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩, ⟨0x9000, 12⟩] [⟨0x3000, w.F.H.D⟩]
  have a0 : stackArg (extractSat vs w) 0 = 0x3000 := by
    rw [extractSat, satS_arg _ _ _ _ _ _ (by decide), put3w_0]
  have a1 : stackArg (extractSat vs w) 1 = BitVec.ofNat 32 w.F.H.D := by
    rw [extractSat, satS_arg _ _ _ _ _ _ (by decide), put3w_1]
  have a2 : stackArg (extractSat vs w) 2 = 0x300000 := by
    rw [extractSat, satS_arg _ _ _ _ _ _ (by decide), put3w_2]
  have hDn : (BitVec.ofNat 32 w.F.H.D).toNat = w.F.H.D := by rw [BitVec.toNat_ofNat]; omega_using [hD]
  have hsp : (extractSat vs w).sp = 0x9000 := rfl
  have hsy : (extractSat vs w).syms = symT vs := rfl
  have hm : (extractSat vs w).mem = tabMem vs w (put3w (fun _ => 0) 0x3000 (BitVec.ofNat 32 w.F.H.D) 0x300000) :=
    rfl
  sig_pre [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, stackBelow, xStack, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, tableRegion_eq, names_eq, argAddr0, a0, a1, a2, hsp, hsy]
  have hA : State.addr (0x9000 : BitVec 32) = 0x9000 := by decide
  simp only [extractSat, satS, extractG, hA] at hG hh a0 a1 a2 ⊢
  simp only [a0, a1, a2, hDn]
  sig_and_intros
  all_goals first
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, hh⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, BitVec.reduceSetWidth,
          BitVec.reduceSub, BitVec.reduceToNat]
        omega_using [hD])
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨w.glen.symm, by rw [w.hmac]; rfl⟩)

/-- `vg_hkdf_extract`, with the tables of `vs`, meets `Spec.Hkdf.extractContract`. -/
theorem extract_spec (hO : OK vs) : Verified Arm.target (extract (fnsOf vs)) (specExtract vs) :=
  Verified.of_correct (fun _ h => extractT_ok hO h) (extractT_ct hO) (extract_implies hO (extract_sat hO))

end

/-! ## `vg_hkdf_expand` -/

open Expand (expandR eStack ep_of)

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specExpand (vs : List HVar) : Contract isa :=
  Spec.Hkdf.expandContract (Arm.abi.withTables Spec.Hkdf.expandSig [("hmac", tables vs)]) eStack

/-- The contract with the table of `w`, and its index. -/
def ExpandW (vs : List HVar) (w : HVar) (s : State) : Prop :=
  (expandR w (fnsOf vs) (names vs) eStack).pre s ∧ IdxW (stackArg s 1) w s

/-- The contract with whichever of the tables of `vs` the table, the second
stack argument, is. -/
def expandTab (vs : List HVar) : Contract isa where
  pre s := ∃ w ∈ vs, ExpandW vs w s
  post s s' := ∀ H S prk, Spec.HmacTable.hashAt 32 s.mem (State.addr (stackArg s 1)) = some H →
    Spec.Hkdf.streamingOf H = some S → Spec.Hkdf.Keyed S s.mem (State.addr (s.gpr .r0)) prk →
    Spec.Hkdf.expand S.H H.len prk (Spec.Sha256.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
      (stackArg s 0).toNat = some (Spec.Sha256.bytesAt s'.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
  pub s₁ s₂ := ∃ w ∈ vs, ExpandW vs w s₁ ∧ ExpandW vs w s₂ ∧ (expandR w (fnsOf vs) (names vs) eStack).pub s₁ s₂

section
variable {vs : List HVar}

theorem expandT_ok (hO : OK vs) (hS : Streams vs) {s : State} (h : (expandTab vs).pre s) :
    ∃ t s', Exec isa (expand (fnsOf vs)) s t s' ∧ abiPreserved s s' ∧ (expandTab vs).post s s' := by
  obtain ⟨w, hv, hp, hix⟩ := h
  have nt := (ep_of hp).nt
  obtain ⟨t, s', he, hg, hpost⟩ := Expand.expand_correct (hO.2.2.2 w hv) hp
  refine ⟨t, s', he, hg, fun H S prk hH hSt hK => ?_⟩
  obtain rfl := streams_of hS hv nt hix hH hSt
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf nt hix))
  rw [w.glen]
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
def ExpandFacts (vs : List HVar) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW (stackArg s 1) w s) ∧ ∀ w ∈ vs, HeldW (stackArg s 1) w s → ExpandW vs w s

theorem expand_pre (hO : OK vs) {s : State} (h : (specExpand vs).pre s) : ExpandFacts vs s := by
  sig_pre [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig, Spec.Hkdf.expandPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, stackBelow, eStack, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, tableRegion_eq, names_eq, argAddr0] at h
  obtain ⟨hsp, h8, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, d1, d2, d3, d4, k1, k2, k3, k4, k5, n1, n2, n3, n4, hP⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf n4 hheld
  have hG : Spec.HmacTable.hashAt 32 s.mem (State.addr (stackArg s 1)) = some w.G := hashAt_tableOf n4 hh.2.1
  rw [List.append_eq, List.append_nil] at hpw
  exact ⟨⟨hsp, h8, hrd, hwr, d1, d2, d3, d4, k1, k2, k3, k4, k5, n1, n2, n3, n4,
    by rw [← w.glen]; exact (hP _ hG).1, hh.1, hh.2.2.1, hh.2.2.2, tabOK_of hO.1 hpw hv⟩, hh.2.1⟩

theorem expand_pub {s₁ s₂ : State} (h₁ : ExpandFacts vs s₁) (h₂ : ExpandFacts vs s₂)
    (h : (specExpand vs).pub s₁ s₂) : (expandTab vs).pub s₁ s₂ := by
  sig_pub [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig, Spec.Hkdf.expandPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, stackBelow, eStack, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, tableRegion_eq, names_eq, argAddr0] at h
  obtain ⟨hsp, hn, hT, e0, e1, e2, e3, e4, e5⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  exact ⟨w, hv, f₁ w hv hh, h₂.2 w hv ((hT _ _ rfl rfl _ (List.mem_map_of_mem hv)).mp hh),
    hsp, e0, e1, e2, e3, e4, e5, hn⟩

/-- The contract with the tables of `vs`, given a state that meets it. -/
theorem expand_implies (hO : OK vs) (hsat : ∃ s, (specExpand vs).pre s) :
    (expandTab vs).Implies (specExpand vs) := by
  refine ⟨fun s h => ?_, fun s s' h hp => ?_, fun s₁ s₂ h₁ h₂ hp =>
    expand_pub (expand_pre hO h₁) (expand_pre hO h₂) hp, hsat⟩
  · obtain ⟨⟨w, hv, hh⟩, f⟩ := expand_pre hO h
    exact ⟨w, hv, f w hv hh⟩
  · sig_post [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig, Spec.Hkdf.expandPost,
      Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, stackBelow, eStack, String.reduceEq,
      Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
      List.append_nil, tableRegion_eq, names_eq, argAddr0]
    exact fun H S prk a b c => hp H S prk a b c

/-- `expand`'s arguments: the states at `0x1000`, `info` (16 bytes) at
`0x2000`, `out` at `0x3000`. -/
def expandG : Reg → BitVec 32
  | .r0 => 0x1000
  | .r1 => 0x2000
  | .r2 => 16
  | .r3 => 0x3000
  | _ => 0

/-- A state meeting the contract, with the table of a variant `w` of `vs`:
16 bytes of `out`. -/
def expandSat (vs : List HVar) (w : HVar) : State :=
  satS vs w expandG (put2w (fun _ => 0) 16 0x300000)
    [⟨0x1000, 384⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩, ⟨0x9000, 8⟩] [⟨0x3000, 16⟩]

theorem expand_sat (hO : OK vs) (hS : Streams vs) : ∃ s, (specExpand vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hD0 := w.ok.hH.hD0
  refine ⟨expandSat vs w, ?_⟩
  have hG := satS_hash vs w expandG (put2w (fun _ => 0) 16 0x300000)
    [⟨0x1000, 384⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩, ⟨0x9000, 8⟩] [⟨0x3000, 16⟩]
  have hh := satS_held vs w expandG (put2w (fun _ => 0) 16 0x300000)
    [⟨0x1000, 384⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩, ⟨0x9000, 8⟩] [⟨0x3000, 16⟩]
  have a0 : stackArg (expandSat vs w) 0 = 16 := by
    rw [expandSat, satS_arg _ _ _ _ _ _ (by decide), put2w_0]
  have a1 : stackArg (expandSat vs w) 1 = 0x300000 := by
    rw [expandSat, satS_arg _ _ _ _ _ _ (by decide), put2w_1]
  have hsp : (expandSat vs w).sp = 0x9000 := rfl
  have hsy : (expandSat vs w).syms = symT vs := rfl
  sig_pre [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig, Spec.Hkdf.expandPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, stackBelow, eStack, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, tableRegion_eq, names_eq, argAddr0, a0, a1, hsp, hsy]
  have hA : State.addr (0x9000 : BitVec 32) = 0x9000 := by decide
  simp only [expandSat, satS, expandG, hA] at hG hh a0 a1 ⊢
  simp only [a0, a1]
  sig_and_intros
  all_goals first
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, hh⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, BitVec.reduceSetWidth,
          BitVec.reduceSub, BitVec.reduceToNat]
        omega_using [])
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       have h16 : (16 : BitVec 32).toNat = 16 := rfl
       exact ⟨by rw [h16, w.glen]; omega_using [hD0], by rw [hS w hv]; rfl⟩)

/-- `vg_hkdf_expand`, with the tables of `vs`, meets `Spec.Hkdf.expandContract`. -/
theorem expand_spec (hO : OK vs) (hS : Streams vs) : Verified Arm.target (expand (fnsOf vs)) (specExpand vs) :=
  Verified.of_correct (fun _ h => expandT_ok hO hS h) (expandT_ct hO) (expand_implies hO (expand_sat hO hS))

end

end VG.Proof.Hkdf.Arm
