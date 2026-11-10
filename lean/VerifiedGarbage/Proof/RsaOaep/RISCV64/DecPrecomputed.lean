module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Inst
public import VerifiedGarbage.Proof.Framework.RISCV64.AppendSlice
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_oaep_decrypt_precomputed` on RISC-V

`vg_rsa_oaep_decrypt`'s code, which ignores the key's precomputed values
`pre` (`Spec/Rsa/PrivatePrecompute.lean` lets an implementation ignore them),
proven against `vg_rsa_oaep_decrypt_precomputed`'s contract from its own
(`verified_withSlice_tables`), with a state that meets it (`preSat`): that of
`Dc/Verified.lean`, with `p`, `q`, `dP`, `dQ` and `qInv` of 32 bytes and a
real key (`Proof/Rsa/PreKey.lean`).
-/

@[expose] public section
namespace VG.Proof.RsaOaep.RISCV64.Dec
open VG VG.RISCV64
open VG.Proof.MdHashTable.RISCV64 (MVar tables names fns3 withTable withTable_below tableOf held_twL twL
  twL_room)
open VG.Proof.HashTable (putWs add8_toNat)
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-- The contract, with the tables `ts`. -/
abbrev pspec (ts : List FnTable) : Contract isa :=
  Spec.RsaOaep.decryptPrecomputedMdTablesContract
    (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", ts), ("mgf1", ts)]) stackBytes

/-! ## A state that meets the contract -/

theorem putWs_byte {a : Addr} : ∀ {ws : List (BitVec 64)} {m : Mem} {p : Addr},
    a.toNat < p.toNat → p.toNat + 8 * ws.length < 2 ^ 64 → putWs m p ws a = m a
  | [], _, _, _, _ => rfl
  | w :: ws, m, p, ha, hp => by
    simp only [List.length_cons] at hp
    have e := add8_toNat (p := p) (by omega)
    simp only [putWs]
    rw [putWs_byte (by rw [e]; omega) (by rw [e]; omega)]
    simp only [Mem.writeW, Mem.write]
    split
    · rename_i hh
      rw [BitVec.toNat_sub] at hh
      omega
    · rfl

/-- The stack arguments of `preState`: `p`'s length, `q` at `0x4300`, `dp`,
`dq` and `qinv` at `0x4400`, `0x4500` and `0x4600`, an empty label, the
input at `0x4100`, `scratch` at `0x20000`, both tables at `0x300000`, `pre`
at `0x4800`. -/
def preArgs : List Nat := [32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x4700, 0, 0x4100, 64,
  0x20000, 2080, 0x300000, 0x300000, 0x4800, 24]

/-- The memory of `preState`: the stack arguments at `0x10000`, and the key
(`keyMem`: `n` at `0x2000`, `p` at `0x4200`, `q` and `pre`). -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10000 i && Nat.blt i 0x10098 then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x10000) / 8) 0 / 256 ^ ((i - 0x10000) % 8))
  else bif keyIn i then keyMem a else 0

/-- The state, but for the table: `out` at `0x1000`, the message's length at
`0x1800`, `n` (64 bytes) at `0x2000`, `e` at `0x3000`, `p` at `0x4200`, the
stack arguments at `sp = 0x10000`. -/
def preState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x1800 | .a3 => 0x2000 | .a4 => 64 | .a5 => 0x3000 | .a6 => 1
    | .a7 => 0x4200 | _ => 0
  sp := 0x10000
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x4800, 192⟩, ⟨0x300000, 88⟩, ⟨0x300000, 88⟩, ⟨0x10000, 152⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

section
variable {vs : List MVar} {w : MVar}

theorem stackArgAddr_psat (j : Nat) (hj : j < 19) : (stackArgAddr preState j).toNat + 8 ≤ 0x300000 := by
  revert j; decide

theorem stackArg_psat {j : Nat} {v : Addr} (hj : j < 19) (e : stackArg preState j = v) :
    stackArg (withTable preState vs w) j = v :=
  (withTable_below _ _ _ (stackArgAddr_psat j hj)).trans e

theorem stackArgs_nineteen (s : State) :
    List.map (stackArg s) (List.range 19) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16, stackArg s 17,
      stackArg s 18] := rfl

theorem psat_args :
    stackArg (withTable preState vs w) 0 = 32 ∧ stackArg (withTable preState vs w) 1 = 0x4300 ∧
    stackArg (withTable preState vs w) 2 = 32 ∧ stackArg (withTable preState vs w) 3 = 0x4400 ∧
    stackArg (withTable preState vs w) 4 = 32 ∧ stackArg (withTable preState vs w) 5 = 0x4500 ∧
    stackArg (withTable preState vs w) 6 = 32 ∧ stackArg (withTable preState vs w) 7 = 0x4600 ∧
    stackArg (withTable preState vs w) 8 = 32 ∧ stackArg (withTable preState vs w) 9 = 0x4700 ∧
    stackArg (withTable preState vs w) 10 = 0 ∧ stackArg (withTable preState vs w) 11 = 0x4100 ∧
    stackArg (withTable preState vs w) 12 = 64 ∧ stackArg (withTable preState vs w) 13 = 0x20000 ∧
    stackArg (withTable preState vs w) 14 = 2080 ∧ stackArg (withTable preState vs w) 15 = 0x300000 ∧
    stackArg (withTable preState vs w) 16 = 0x300000 ∧ stackArg (withTable preState vs w) 17 = 0x4800 ∧
    stackArg (withTable preState vs w) 18 = 24 :=
  ⟨stackArg_psat (by decide) (by decide), stackArg_psat (by decide) (by decide),
    stackArg_psat (by decide) (by decide), stackArg_psat (by decide) (by decide),
    stackArg_psat (by decide) (by decide), stackArg_psat (by decide) (by decide),
    stackArg_psat (by decide) (by decide), stackArg_psat (by decide) (by decide),
    stackArg_psat (by decide) (by decide), stackArg_psat (by decide) (by decide),
    stackArg_psat (by decide) (by decide), stackArg_psat (by decide) (by decide),
    stackArg_psat (by decide) (by decide), stackArg_psat (by decide) (by decide),
    stackArg_psat (by decide) (by decide), stackArg_psat (by decide) (by decide),
    stackArg_psat (by decide) (by decide), stackArg_psat (by decide) (by decide),
    stackArg_psat (by decide) (by decide)⟩

theorem preState_key :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTable preState vs w).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTable preState vs w).mem 0x4200 32)
      (Spec.Rsa.bytesAt (withTable preState vs w).mem 0x4300 32) =
        some (Spec.Rsa.wordsAt (withTable preState vs w).mem 0x4800 24) := by
  refine key_pre_of fun a ha => ?_
  have hlt : a.toNat < 0x10000 := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
  have hs : (Nat.ble 0x10000 a.toNat && Nat.blt a.toNat 0x10098) = false := by
    refine Bool.eq_false_iff.mpr fun h => ?_
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    omega
  show putWs preMem 0x300000 (twL vs w) a = _
  rw [putWs_byte (by simp; omega) (twL_room vs w)]
  show (bif _ then _ else _) = _
  rw [hs, Bool.cond_false, ha, Bool.cond_true]

/-- A state meeting the contract, with both tables that of `w`, at
`0x300000`. -/
theorem preSat (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 32) : ∃ s, (pspec (tables vs)).pre s := by
  refine ⟨withTable preState vs w, ?_⟩
  have hK := preState_key (vs := vs) (w := w)
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ :=
    psat_args (vs := vs) (w := w)
  have e : stackArgAddr (withTable preState vs w) 0 = 0x10000 := show stackArgAddr preState 0 = _ by decide
  have e3472 : stackBytes = 3471 + 1 := rfl
  unfold pspec
  rw [e3472]
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount,
    Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    stackArgs_nineteen, List.append_eq, List.range, List.range.loop]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
    a13, a14, a15, a16, a17, a18, e]
  sig_and_intros
  rotate_right 6
  · exact hK
  all_goals first
    | exact ⟨tableOf w, List.mem_map_of_mem hw, held_twL _ _ _ rfl⟩
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.HashTable.symsOf_distinct2 hl
    | (unfold Spec.Rsa.lenValid; decide)
    | (unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords; decide)

end

/-! ## The code -/

theorem stackVals_dec (s : State) : stackVals 25 s = [s.gpr .a0, s.gpr .a1, s.gpr .a2, s.gpr .a3, s.gpr .a4,
    s.gpr .a5, s.gpr .a6, s.gpr .a7, stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4,
    stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11,
    stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16] := rfl

theorem stackVals_decP (s : State) : stackVals (25 + 2) s = stackVals 25 s ++ [stackArg s 17, stackArg s 18] :=
  rfl

/-- `Spec.RsaOaep.decryptMdTablesSig.words 64`. -/
abbrev sigWords : List ArgWord :=
  [.addr, .int 64, .addr, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64,
    .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .int 64, .addr, .addr]

theorem decPrecomputed_verified {vs : List MVar} (hok : OK vs) :
    Verified target (Impl.RsaOaep.RISCV64.Dec.decrypt (fns3 vs)) (pspec (tables vs)) := by
  refine verified_withSlice_tables (sig := Spec.RsaOaep.decryptMdTablesSig) (nm := "pre") (e := .u64)
    (ln := "pre_len")
    (fun u hu => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> exact ⟨_, rfl, by decide⟩)
    (by decide) (by decide) (Proof.RsaOaep.RISCV64.dec_ok vs hok) ?_ ?_ ?_
    (let ⟨_, hw⟩ := hok.mem; preSat hw hok.2.1)
  · intro s h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -, -⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  · intro s m' v hp hq
    exact hq
  · intro s₁ s₂ _ _ hpo h
    have e4 := hpo 4 (by decide)
    have e6 := hpo 6 (by decide)
    have hl : (Spec.RsaOaep.decryptMdTablesSig.words 64).length = 25 := by decide
    simp only [hl, stackVals_decP, stackVals_dec, List.cons_append, List.nil_append] at h e4 e6 ⊢
    change Curry.apply (α := Mem → List Nat) (sigWords ++ [.addr, .int 64]) _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) (sigWords ++ [.addr, .int 64]) _ _ s₂.mem at h
    change Curry.apply (α := Mem → List Nat) sigWords _ _ s₁.mem =
      Curry.apply (α := Mem → List Nat) sigWords _ _ s₂.mem
    change (s₁.gpr .a4).setWidth 64 = (s₂.gpr .a4).setWidth 64 at e4
    change (s₁.gpr .a6).setWidth 64 = (s₂.gpr .a6).setWidth 64 at e6
    dsimp only [sigWords, List.cons_append, List.nil_append, Curry.apply, ArgWord.ofRaw] at h ⊢
    refine List.append_inj_left h ?_
    simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', e4, e6]

end VG.Proof.RsaOaep.RISCV64.Dec
