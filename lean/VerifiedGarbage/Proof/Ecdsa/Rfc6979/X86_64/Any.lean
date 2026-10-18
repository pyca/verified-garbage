module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.AnyPre
public import VerifiedGarbage.Proof.Framework.Dispatch
public import VerifiedGarbage.Proof.Framework.X86_64.Dispatch
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# Deterministic ECDSA on x86-64, for any hash function: correctness

For a curve `A.R` and an instance `A.I` of the contract,
`vg_ecdsa_<curve>_rfc6979_sign` (`signAny`) moves `scratch` to `rcx`, `hash`
to `rax` and the table's three addresses to `r9`, `r10` and `r11` (`ent_ok`:
`Ent`), then runs `sign` of the configuration of the hash function `hash`
names (`Dispatch.X86_64.chain`), which is `cfgOf` of the hash function
`A.hashOf` (`case_ok`): from `Ent`, the precondition of `rfcX86_64` holds
(`body_pre`, with the table and the stack argument as further readable
regions) and the streaming functions at those addresses meet their
contracts in the entry (`body_in`), so `sign_ok` gives the result, which is
`anyResult`'s (`anyResult_eq`): `any_correct`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

/-- A curve and an instance of the contract, for RFC 6979 with any hash
function on x86-64: the instance's curve, at least one candidate and as many
as a 32-bit immediate holds, and 8 KiB of `scratch`. -/
structure RfcAny where
  R : RfcCurve
  I : Spec.Ecdsa.Rfc6979.Instance
  ecdsa : I.ecdsa = R.inst
  tries_pos : 0 < I.tries
  tries_lt : I.tries < 2 ^ 32
  scratch : I.scratchWords = 1024

/-- The hash function the number `k` names: its streaming functions, its HMAC
and its output length. -/
theorem hash_facts {k : Nat} (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds) :
    ∃ T, Spec.HashFns.streaming k = some T ∧ Spec.HashId.hmac k = some T.S.H ∧
      ∃ H, Spec.HashId.mgf1 k = some H ∧ H.len = T.S.digestBytes := by
  simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl, _, rfl, rfl⟩

namespace RfcAny

variable (A : RfcAny)

/-- The comb's tables. -/
abbrev cs : List (String × List (BitVec 64)) := A.R.E.combConsts

/-- The instance with the hash function `T`'s HMAC and output length. -/
def instOf (T : Spec.HashFns.Streaming) : Spec.Ecdsa.Rfc6979.Instance :=
  { A.I with hash := T.S.H, hashLen := T.S.digestBytes }

/-- The hash function the number `k` names, as the proof of `sign` has it. -/
def hashOf {k : Nat} {T : Spec.HashFns.Streaming} (hT : Spec.HashFns.streaming k = some T)
    (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds) : RfcHash :=
  ⟨A.R, A.instOf T, k, T, hT, hk, A.ecdsa, rfl, rfl, A.tries_pos, A.tries_lt⟩

/-- The code. -/
abbrev code : Prog isa := signAny (A.R.cc A.I.tries)

theorem hashOf_sign {k : Nat} {T : Spec.HashFns.Streaming} (hT : Spec.HashFns.streaming k = some T)
    (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds) :
    (cfgOf (A.hashOf hT hk)).sign = (Cfg.ofCurve (A.R.cc A.I.tries) k).sign := by
  rw [cfgOf_eq]; rfl

end RfcAny

/-! ## The entry -/

/-- The state the entry blocks leave, from the entry `e`: `scratch` in `rcx`,
`hash` in `rax`, the table's words in `r9`, `r10` and `r11`, all else of `e`
but the flags. -/
structure Ent (e s : State) : Prop where
  mem : s.mem = e.mem
  rd : s.rd = e.rd
  wr : s.wr = e.wr
  syms : s.syms = e.syms
  funs : s.funs = e.funs
  cs : ∀ r ∈ calleeSaved, s.gpr r = e.gpr r
  rdi : s.gpr .rdi = e.gpr .rdi
  rsi : s.gpr .rsi = e.gpr .rsi
  rdx : s.gpr .rdx = e.gpr .rdx
  rcx : s.gpr .rcx = e.gpr .r8
  rax : s.gpr .rax = e.gpr .r9
  r9 : s.gpr .r9 = e.mem.readW (stackArg e 0) 64
  r10 : s.gpr .r10 = e.mem.readW (stackArg e 0 + 8) 64
  r11 : s.gpr .r11 = e.mem.readW (stackArg e 0 + 16) 64

theorem Ent.flags {e s s' : State} (h : Ent e s) (hf : Proof.Dispatch.X86_64.FlagsOnly s s') : Ent e s' := by
  obtain ⟨c, o, z, f, rfl⟩ := hf
  exact ⟨h.mem, h.rd, h.wr, h.syms, h.funs, h.cs, h.rdi, h.rsi, h.rdx, h.rcx, h.rax, h.r9, h.r10, h.r11⟩

section
variable {I : Spec.Ecdsa.Rfc6979.Instance} {cs : List (String × List (BitVec 64))} {e : State}

theorem rsp8 (e : State) : e.gpr .rsp + BitVec.ofNat 64 8 = stackArgAddr e 0 := rfl

/-- `scratch` to `rcx`, the table's address to `r10`, `hash` to `rax`. -/
theorem entry_ok (hp : APre I cs e) :
    WP isa (.block entry) e fun s => s = ((e.setReg .rcx (e.gpr .r8)).setReg .r10 (stackArg e 0)).setReg .rax
      (e.gpr .r9) := by
  have hin : InRegions (e.rd ++ e.wr) (stackArgAddr e 0) 8 :=
    ⟨argR e, by rw [hp.rd]; simp, Region.contains_self _ _⟩
  apply WP.of_runBlock
  simp only [entry, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, rsp8, hin, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left', reduceCtorEq, ite_false]
  rfl

theorem tab_in (hp : APre I cs e) {d : Nat} (hd : d + 8 ≤ 24) :
    InRegions (e.rd ++ e.wr) (stackArg e 0 + BitVec.ofNat 64 d) 8 :=
  ⟨tabR e, by rw [hp.rd]; simp, Offset.contains_base _ (by have := hp.bT; omega) (by omega)⟩

/-- The table's words to `r9`, `r11` and `r10`. -/
theorem entryFns_ok (hp : APre I cs e) :
    WP isa (.block entryFns) (((e.setReg .rcx (e.gpr .r8)).setReg .r10 (stackArg e 0)).setReg .rax (e.gpr .r9))
      (Ent e) := by
  apply WP.of_runBlock
  simp only [entryFns, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, tab_in hp (d := 0) (by omega),
    tab_in hp (d := 8) (by omega), tab_in hp (d := 16) (by omega), ite_true, Option.map_some, Option.some.injEq,
    exists_eq_left', reduceCtorEq, ite_false]
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [RegUpd.gpr_setReg]
  all_goals simp [RegUpd.gpr_setReg, BitVec.add_zero]

end

/-! ## The case of the hash function -/

namespace RfcAny

variable (A : RfcAny) {e s : State} {k : Nat} {T : Spec.HashFns.Streaming}

theorem len_eq (hp : APre A.I A.cs e) (hT : Spec.HashFns.streaming k = some T) (hk' : (e.gpr .r9).toNat = k) :
    (e.gpr .rcx).toNat = T.S.digestBytes := by
  obtain ⟨T', hT', -, H, hH, hHl⟩ := hash_facts (hk' ▸ hp.hk)
  rw [hT] at hT'
  cases hT'
  rw [hp.dl H (hk' ▸ hH), hHl]

/-- The precondition of `sign` of the hash function's configuration. -/
theorem body_pre (hp : APre A.I A.cs e) (he : Ent e s) (hT : Spec.HashFns.streaming k = some T)
    (hk' : (e.gpr .r9).toNat = k) :
    (rfcX86_64 A.cs (A.instOf T) 408 [tabR e, argR e]).pre s := by
  have hl := A.len_eq hp hT hk'
  have hsp := he.cs .rsp (by decide)
  simp only [rfcX86_64, TblsOk, he.rdi, he.rsi, he.rdx, he.rcx, hsp, he.rd, he.wr, he.mem, he.syms]
  rw [show (A.instOf T).hashLen = (e.gpr .rcx).toNat from hl.symm,
    show (A.instOf T).ecdsa = A.I.ecdsa from rfl, show (8192 : Nat) = A.I.scratchWords * 8 by rw [A.scratch]]
  refine ⟨hp.sp, by rw [hp.rd]; rfl, hp.wr, hp.oD, hp.oG, hp.oS, hp.dS, hp.gS, hp.rO, hp.rD, hp.rG, hp.rS,
    hp.kO, hp.kD, hp.kG, hp.kS, hp.bO, hp.bD, hp.bG, hp.bS, hp.held, fun t ht => ⟨(hp.tbl t ht).1, ?_⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hp.tbl t ht).2.1 _ (by rw [hp.wr]; simp)
  · exact (hp.tbl t ht).2.1 _ (by rw [hp.wr]; simp)
  · exact (hp.tbl t ht).2.2.1
  · exact (hp.tbl t ht).2.2.2

/-- The streaming functions at the addresses the entry blocks load meet their
contracts in the entry, which holds the comb's tables, and is like `E`. -/
theorem body_in (hp : APre A.I A.cs e) (he : Ent e s) (hT : Spec.HashFns.streaming k = some T)
    (hk' : (e.gpr .r9).toNat = k) {E : State} (hl : Like E e) : BodyIn A.cs T E s := by
  have ht := hp.fns
  rw [hk'] at ht
  simp only [Spec.HashFns.tableOf, hT, Spec.HashFns.table] at ht
  obtain ⟨h₀, h₁, h₂⟩ := ht
  refine ⟨e, ⟨he.funs, he.syms, fun x _ => by rw [he.mem]⟩, ⟨?_, ?_, ?_, hp.held, fun t ht => ⟨(hp.tbl t ht).1,
    (hp.tbl t ht).2.1, fun r hr => ?_⟩⟩, hl, he.wr.symm, (he.cs .rsp (by decide)).symm⟩
  · rw [he.r9]; exact h₀
  · rw [he.r10]; exact h₁
  · rw [he.r11]; exact h₂
  · simp only [abi, stackBelow, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.tbl t ht).2.2.1
    · exact (hp.tbl t ht).2.2.2

theorem anyResult_eq (hm : Spec.HashId.hmac k = some T.S.H) (m : Mem) (d dg : Addr) {dl : Nat}
    (hdl : dl = T.S.digestBytes) : A.I.anyResult m d dg dl k = some (result (A.instOf T) m d dg) := by
  subst hdl
  unfold Spec.Ecdsa.Rfc6979.Instance.anyResult
  rw [hm]
  rfl

end RfcAny

/-- The shared contract's postcondition, from the signature's. -/
theorem any_post {I : Spec.Ecdsa.Rfc6979.Instance} {cs : List (String × List (BitVec 64))} {e s' : State}
    (h : match I.anyResult e.mem (e.gpr .rsi) (e.gpr .rdx) (e.gpr .rcx).toNat (e.gpr .r9).toNat with
      | some (some rs, _) => (s'.gpr .rax).setWidth 32 = 1 ∧
        Spec.Ecdsa.bytesAt s'.mem (e.gpr .rdi) (2 * I.ecdsa.curve.len) = Spec.Ecdsa.encode I.ecdsa.curve rs
      | _ => (s'.gpr .rax).setWidth 32 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (e.gpr .rdi) (2 * I.ecdsa.curve.len) =
          List.replicate (2 * I.ecdsa.curve.len) 0) :
    (I.signAnyContract (abi.withConsts cs) 408).post e s' := by
  cases cs <;>
  sig_post [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig, abi, argRegs,
    Abi.withConsts, stackArgs_one] <;>
  exact h

namespace RfcAny

variable (A : RfcAny) {e s : State}

/-- `sign` of the configuration of the hash function `hash` names, from a
state the entry blocks leave. -/
theorem case_ok (hp : APre A.I A.cs e) (he : Ent e s) :
    WP isa (Cfg.ofCurve (A.R.cc A.I.tries) (e.gpr .r9).toNat).sign s fun s' =>
      gprPreserved e s' ∧ (A.I.signAnyContract (abi.withConsts A.cs) 408).post e s' := by
  obtain ⟨T, hT, hm, -⟩ := hash_facts hp.hk
  rw [← A.hashOf_sign hT hp.hk]
  have hsp := he.cs .rsp (by decide)
  refine WP.mono (sign_ok (P := A.hashOf hT hp.hk) (A.body_pre hp he hT rfl) (A.body_in hp he hT rfl ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩))
    fun s' ⟨⟨hg₁, hg₂⟩, hq⟩ => ⟨⟨fun r hr => (hg₁ r hr).trans (he.cs r hr), by rw [← hsp, hg₂, he.mem]⟩, ?_⟩
  refine any_post ?_
  have hres := A.anyResult_eq hm e.mem (e.gpr .rsi) (e.gpr .rdx) (A.len_eq hp hT rfl)
  rw [hres]
  have hq' : match (result (A.instOf T) e.mem (e.gpr .rsi) (e.gpr .rdx)).1 with
      | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧
        Spec.Ecdsa.bytesAt s'.mem (e.gpr .rdi) (2 * A.I.ecdsa.curve.len) = Spec.Ecdsa.encode A.I.ecdsa.curve rs
      | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.Ecdsa.bytesAt s'.mem (e.gpr .rdi) (2 * A.I.ecdsa.curve.len) =
          List.replicate (2 * A.I.ecdsa.curve.len) 0 := by
    have := hq
    simp only [rfcX86_64, he.mem, he.rsi, he.rdx, he.rdi] at this
    exact this
  rcases hr : result (A.instOf T) e.mem (e.gpr .rsi) (e.gpr .rdx) with ⟨_ | rs, n⟩ <;>
    simp only [hr] at hq' ⊢ <;> exact hq'

theorem keys_any (g : Nat → Prog isa) : Proof.Dispatch.keys (hashIds.map fun k => (k, g k)) = hashIds := rfl

/-- The whole function, from its precondition. -/
theorem any_wp (hp : APre A.I A.cs e) :
    WP isa A.code e fun s' => gprPreserved e s' ∧ (A.I.signAnyContract (abi.withConsts A.cs) 408).post e s' := by
  refine WP.seq (WP.mono (entry_ok hp) fun s hs => ?_)
  subst hs
  refine WP.seq (WP.mono (entryFns_ok hp) fun s he => ?_)
  have hk : (e.gpr .r9).toNat ∈ hashIds := hp.hk
  refine Proof.Dispatch.chain_wp Proof.Dispatch.X86_64.tests _ (by rw [keys_any]; decide)
    (by rw [keys_any]; show (s.gpr .rax).toNat ∈ hashIds; rw [he.rax]; exact hk) (by rw [keys_any]; decide)
    fun c' hc s' hf hsel => ?_
  obtain ⟨k, -, hkc⟩ := List.mem_map.mp hc
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkc
  have he' := he.flags hf
  have hk' : (s.gpr .rax).toNat = (e.gpr .r9).toNat := by rw [he.rax]
  show WP isa (Cfg.ofCurve (A.R.cc A.I.tries) (s.gpr .rax).toNat).sign s' _
  rw [hk']
  exact A.case_ok hp he'

theorem code_fine : Instrs.Fine A.code := Instrs.signAny_fine _ A.R.coreMx A.R.coreSp

/-- `vg_ecdsa_<curve>_rfc6979_sign` meets the shared contract's precondition
and postcondition, and keeps what the calling convention keeps. -/
theorem any_correct (s : State) (h : (A.I.signAnyContract (abi.withConsts A.cs) 408).pre s) :
    ∃ t s', Exec isa A.code s t s' ∧ abiPreserved s s' ∧
      (A.I.signAnyContract (abi.withConsts A.cs) 408).post s s' := by
  obtain ⟨t, s', he, hg, hq⟩ := A.any_wp (apre_of h)
  exact ⟨t, s', he, abiPreserved_of_ctl (ctlOk_of_ctlC A.code_fine.1) he hg, hq⟩

/-- It writes `rsp` only in its frames' pushes and pops. -/
theorem any_spSafe : A.code.all (fun i => !isa.writesSp i) = true := A.code_fine.2

end RfcAny

end VG.Proof.Ecdsa.Rfc6979.X86_64
