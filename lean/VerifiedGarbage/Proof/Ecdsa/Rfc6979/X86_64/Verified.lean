module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.CT
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Deterministic ECDSA on x86-64: `Verified`

The code for a curve and a tier of hash functions (`RfcAny`) is that of
`cfgOf P` for each hash function `P` of the tier (`RfcAny.at`), proven for
each against `rfcX86_64` with that hash function's number: `sign_ok` gives
the postcondition and keeps the callee-saved registers and the return
address, and `sign_ct` constant time up to the number of candidates. The
contract `signAnyContract` is, for each value of its public argument `hash`,
that contract (`any_pre`, `any_post`, `any_pub`), so the code meets it
(`Verified.of_family`).

No instruction of the function or of those it calls loads MXCSR (`sign_mx`),
so it is kept too (`abiPreserved`), and none writes `rsp` but the frame's
push and pop (`sign_spSafe`): the functions it calls by what the tier's
hash functions and the curve know of them, the blocks that depend on the
curve as the curve checks them (`CurveInstrs`), and the rest, which depend
on neither but for their immediates, by evaluation (`GenOk`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (Tier MdHash core_hmacInit core_hmacFin core_updC)

/-! ## A curve and a tier of hash functions -/

/-- A curve and a tier of hash functions, for RFC 6979 on x86-64 with the
hash function as an argument. -/
structure RfcAny where
  /-- The curve. -/
  R : RfcCurve
  /-- The hash functions' implementations. -/
  T : Tier
  /-- The curve's instance of RFC 6979 (whose hash function is not used). -/
  I0 : Spec.Ecdsa.Rfc6979.Instance
  /-- The instance is of the curve, tries at least one candidate, as many as
  a 32-bit immediate holds, and has 8 KiB of working space. -/
  ecdsa : I0.ecdsa = R.inst
  tries_pos : 0 < I0.tries
  tries_lt : I0.tries < 2 ^ 32
  scratch : I0.scratchWords = 1024

/-- The code for the curve `R`, the tier `T` and at most `tries` candidates. -/
def cfgRT (R : RfcCurve) (T : Tier) (tries : Nat) : Cfg where
  hs := hsOf T
  w := R.E.n
  len := R.E.C.len
  wide := R.wide
  sh := R.sh
  n := R.E.C.n
  tries := tries
  coreN := R.coreN
  coreC := R.coreC

theorem cfgOf_eq (P : RfcHash) : cfgOf P = cfgRT P.R P.T P.I0.tries := rfl

theorem tier_lt {T : Tier} {k : Nat} (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds) : k < T.hashes.length := by
  rw [tier_length]; exact hashIds_lt hk

namespace RfcAny

variable (A : RfcAny)

/-- The hash function `k` of the tier. -/
def hashAt (k : Nat) (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds) : RfcHash where
  R := A.R
  T := A.T
  I0 := A.I0
  k := k
  v := A.T.hashes[k]'(tier_lt hk)
  hv := List.getElem?_eq_getElem (tier_lt hk)
  hk := hk
  ecdsa := A.ecdsa
  tries_pos := A.tries_pos
  tries_lt := A.tries_lt

/-- The code. -/
abbrev code : Prog isa := (cfgRT A.R A.T A.I0.tries).sign

/-- The contract, for the comb's tables and 544 bytes of stack. -/
abbrev contract : Contract isa := A.I0.signAnyContract (X86_64.abi.withConsts A.R.E.combConsts) 544

end RfcAny

/-! ## Every instruction -/

theorem ai_seq {p : Instr → Bool} {a b : Prog isa} (ha : a.allInstrs p = true) (hb : b.allInstrs p = true) :
    (Code.seq a b).allInstrs p = true := by
  show (a.allInstrs p && b.allInstrs p) = true; rw [ha, hb]; rfl

theorem ai_ite {p : Instr → Bool} {c : Cond} {a b : Prog isa} (ha : a.allInstrs p = true)
    (hb : b.allInstrs p = true) : (Code.ite c a b).allInstrs p = true := by
  show (a.allInstrs p && b.allInstrs p) = true; rw [ha, hb]; rfl

theorem ai_if {p : Instr → Bool} {c : Prop} [Decidable c] {a b : Prog isa} (ha : a.allInstrs p = true)
    (hb : b.allInstrs p = true) : (if c then a else b).allInstrs p = true := by
  split
  · exact ha
  · exact hb

theorem ai_frame {p : Instr → Bool} {i j : Instr} {b : Prog isa} (hi : p i = true) (hb : b.allInstrs p = true)
    (hj : p j = true) : (Code.frame i b j).allInstrs p = true := by
  show (p i && b.allInstrs p && p j) = true; rw [hi, hb, hj]; rfl

theorem ai_block {p : Instr → Bool} {is : List Instr} (h : is.all p = true) :
    (Code.block is : Prog isa).allInstrs p = true := by
  rw [Code.allInstrs_eq]; exact h

theorem allInstrs_imp {p q : Instr → Bool} (h : ∀ i, p i = true → q i = true) {c : Prog isa}
    (hc : c.allInstrs p = true) : c.allInstrs q = true := by
  rw [Code.allInstrs_eq, List.all_eq_true] at hc ⊢
  exact fun i hi => h i (hc i hi)

/-- An instruction that does not clobber `rsp` does not write it. -/
theorem noSp_of_ns (i : Instr) (h : (!Taint.clobbers i .rsp) = true) : (!isa.writesSp i) = true := by
  cases i with
  | mulx hi lo s =>
    simp only [Taint.clobbers, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    show (!(hi == .rsp || lo == .rsp)) = true
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨fun e => h.1 e.symm, fun e => h.2 e.symm⟩
  | pop r k => simp [Taint.clobbers] at h
  | _ => first | rfl | (simp only [Taint.clobbers, Taint.dstOf] at h; simp only [Instr.dst]; exact h)

/-- A dispatch: its tests and its cases. -/
theorem chain_allInstrs {p : Instr → Bool}
    (ht : ∀ k, (Code.block (Impl.Dispatch.X86_64.test k) : Prog isa).allInstrs p = true) :
    ∀ cs : List (Nat × Prog isa), (∀ c ∈ cs, c.2.allInstrs p = true) →
      (Impl.Dispatch.X86_64.chain cs).allInstrs p = true
  | [], _ => rfl
  | [(_, _)], h => h _ (List.mem_singleton_self _)
  | (k, _) :: c' :: cs, h =>
    ai_seq (ht k) (ai_ite (h _ List.mem_cons_self)
      (chain_allInstrs ht (c' :: cs) fun d hd => h d (List.mem_cons_of_mem _ hd)))

/-- The cases of a dispatch on the hash function, each the code `f` makes
of a hash function of the tier. -/
theorem cases_all {T : Tier} {α : Type} {g : α → Prog isa} {f : Impl.Pbkdf2.Md.X86_64.Hash → α}
    {p : Instr → Bool}
    (h : ∀ k v, k ∈ Spec.Ecdsa.Rfc6979.hashIds → T.hashes[k]? = some v → (g (f v.H)).allInstrs p = true) :
    ∀ c ∈ (hsOf T).map (fun q => (q.1, g (f q.2))), c.2.allInstrs p = true := by
  intro c hc
  obtain ⟨⟨i, H⟩, hm, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hi, v, hv, rfl⟩ := mem_hsOf.mp hm
  exact h i v hi hv

/-- What a property of instructions must hold of in the functions called and
the blocks that depend on the curve. -/
structure InstrsOk (R : RfcCurve) (T : Tier) (p : Instr → Bool) : Prop where
  hash : ∀ k v, k ∈ Spec.Ecdsa.Rfc6979.hashIds → T.hashes[k]? = some v →
    v.H.hmacInit.allInstrs p = true ∧ v.H.updC.allInstrs p = true ∧ v.H.hmacFin.allInstrs p = true
  core : R.coreC.allInstrs p = true
  curve : CurveInstrs (cfgC R.E R.wide R.sh) p

/-- The blocks that depend on neither the curve nor the hash function but for
their immediates, each closed by evaluation for a property that does not
read them. -/
structure GenOk (p : Instr → Bool) : Prop where
  test : ∀ k, (Code.block (Impl.Dispatch.X86_64.test k) : Prog isa).allInstrs p = true
  entry : (Code.block Cfg.entry : Prog isa).allInstrs p = true
  sizes : ∀ D B, (Code.block (Cfg.sizes D B) : Prog isa).allInstrs p = true
  push : p (.push Cfg.pushRs) = true
  pop : p (.pop .rcx 65) = true
  a₁ : (Code.block Cfg.hmacArgs₁ : Prog isa).allInstrs p = true
  a₂V : ∀ e, (Code.block (Cfg.hmacArgs₂ (Cfg.fr .rdx fV) e) : Prog isa).allInstrs p = true
  a₂M : ∀ e, (Code.block (Cfg.hmacArgs₂ (Cfg.scr .rdx sMsg) e) : Prog isa).allInstrs p = true
  a₃ : ∀ e dst, (Code.block (Cfg.hmacArgs₃ e dst) : Prog isa).allInstrs p = true
  ptrs : (Code.block Cfg.msgPtrs : Prog isa).allInstrs p = true
  dg : (Code.block Cfg.digestPtr : Prog isa).allInstrs p = true
  zero₀ : (Code.block ([.alu32 .xor .rcx (.reg .rcx)] ++
    (List.range 9).map (fun j => .store (stk (fY + 8 * j)) .rcx) ++ Cfg.selLd) : Prog isa).allInstrs p = true
  zero₁ : (Code.block ([.alu32 .xor .rcx (.reg .rcx)] ++
    (List.range 18).map (fun j => .store (stk (fY + 8 * j)) .rcx) ++ Cfg.selLd) : Prog isa).allInstrs p = true
  kv : (Code.block Cfg.initKV : Prog isa).allInstrs p = true
  cnt : ∀ c : Cfg, (Code.block c.initCnt : Prog isa).allInstrs p = true
  offI : (Code.block Cfg.offInit : Prog isa).allInstrs p = true
  offL : (Code.block Cfg.offLd : Prog isa).allInstrs p = true
  scrP : (Code.block Cfg.scrPtr : Prog isa).allInstrs p = true
  args : (Code.block Cfg.coreArgs : Prog isa).allInstrs p = true
  go : (Code.block Cfg.goOn : Prog isa).allInstrs p = true
  again : (Code.block Cfg.again : Prog isa).allInstrs p = true
  stop : (Code.block Cfg.stop : Prog isa).allInstrs p = true
  wipe : (Code.block Cfg.wipe : Prog isa).allInstrs p = true

theorem dims_mem' {T : Tier} {k : Nat} {v : MdHash} (hv : T.hashes[k]? = some v)
    (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds) : v.H.D ∈ [20, 28, 32, 48, 64] := by
  rcases tier_dims hv hk with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide

/-- Every instruction of the code, and of the functions it calls. -/
theorem sign_allInstrs (R : RfcCurve) (T : Tier) (tries : Nat) {p : Instr → Bool} (hI : InstrsOk R T p)
    (hG : GenOk p) : (cfgRT R T tries).sign.allInstrs p = true := by
  have hcv := hI.curve
  have callH : ∀ (f : Impl.Pbkdf2.Md.X86_64.Hash → String × Prog isa),
      (∀ k v, k ∈ Spec.Ecdsa.Rfc6979.hashIds → T.hashes[k]? = some v → (f v.H).2.allInstrs p = true) →
      ((cfgRT R T tries).callH f).allInstrs p = true := fun f h =>
    chain_allInstrs hG.test _ (cases_all (g := fun x : String × Prog isa => Code.call x.1 x.2) h)
  have hmac : ∀ dataA e dst, (Code.block (Cfg.hmacArgs₂ dataA e) : Prog isa).allInstrs p = true →
      ((cfgRT R T tries).hmac dataA e dst).allInstrs p = true := fun _ e dst h₂ =>
    ai_seq hG.a₁ (ai_seq (callH _ fun k v hk hv => (hI.hash k v hk hv).1) (ai_seq h₂
      (ai_seq (callH _ fun k v hk hv => (hI.hash k v hk hv).2.1) (ai_seq (hG.a₃ e dst)
        (callH _ fun k v hk hv => (hI.hash k v hk hv).2.2)))))
  have hmacV : (cfgRT R T tries).hmacV.allInstrs p = true := hmac _ 0 fV (hG.a₂V 0)
  have rekeyF : ∀ b, (Cfg.msg R.E.C.len b true).all p = true →
      ((cfgRT R T tries).rekeyFull b).allInstrs p = true := fun b h =>
    ai_seq hG.ptrs (ai_seq (ai_block h) (ai_seq (hmac _ _ _ (hG.a₂M _)) hmacV))
  have rekey : (cfgRT R T tries).rekey.allInstrs p = true :=
    ai_seq hG.ptrs (ai_seq (ai_block hcv.2.2.1) (ai_seq (hmac _ _ _ (hG.a₂M _)) hmacV))
  have candStep : (cfgRT R T tries).candStep.allInstrs p = true :=
    ai_seq hmacV (ai_seq hG.offL (ai_block hcv.2.2.2.2.2.1))
  have cand : (cfgRT R T tries).cand.allInstrs p = true :=
    ai_seq hG.offI (ai_if candStep (ai_seq candStep (ai_seq hG.scrP (ai_block hcv.2.2.2.2.2.2))))
  have zero : (Code.block (cfgRT R T tries).prepZero : Prog isa).allInstrs p = true := by
    unfold Cfg.prepZero
    split
    · exact hG.zero₁
    · exact hG.zero₀
  have prep : (cfgRT R T tries).prep.allInstrs p = true :=
    ai_seq zero (ai_seq (chain_allInstrs hG.test _ (cases_all (g := fun x : List Instr => Code.block x)
      (f := fun H => (cfgRT R T tries).prepCase H.D) fun k v hk hv => ai_block (hcv.1 _ (dims_mem' hv hk)))) (ai_block hcv.2.1))
  have tryOne : (cfgRT R T tries).tryOne.allInstrs p = true :=
    ai_seq cand (ai_seq hG.args (ai_seq hI.core (ai_seq hG.go (ai_ite (ai_seq rekey hG.again) hG.stop))))
  exact ai_seq hG.entry (ai_seq (chain_allInstrs hG.test _ (cases_all (g := fun x : List Instr => Code.block x)
    (f := fun H => Cfg.sizes H.D H.P.B) fun _ _ _ _ => hG.sizes _ _)) (ai_frame hG.push (ai_seq hG.dg (ai_seq prep (ai_seq hG.kv
      (ai_seq (rekeyF 0 hcv.2.2.2.1) (ai_seq (rekeyF 1 hcv.2.2.2.2.1) (ai_seq (hG.cnt _)
        (ai_seq tryOne hG.wipe))))))) hG.pop))

theorem genMx : GenOk fun i => !loadsMxcsr i where
  test _ := rfl
  entry := rfl
  sizes _ _ := rfl
  push := rfl
  pop := rfl
  a₁ := rfl
  a₂V _ := rfl
  a₂M _ := rfl
  a₃ _ _ := rfl
  ptrs := rfl
  dg := rfl
  zero₀ := rfl
  zero₁ := rfl
  kv := rfl
  cnt _ := rfl
  offI := rfl
  offL := rfl
  scrP := rfl
  args := rfl
  go := rfl
  again := rfl
  stop := rfl
  wipe := rfl

theorem genSp : GenOk fun i => !isa.writesSp i where
  test _ := rfl
  entry := rfl
  sizes _ _ := rfl
  push := rfl
  pop := rfl
  a₁ := rfl
  a₂V _ := rfl
  a₂M _ := rfl
  a₃ _ _ := rfl
  ptrs := rfl
  dg := rfl
  zero₀ := rfl
  zero₁ := rfl
  kv := rfl
  cnt _ := rfl
  offI := rfl
  offL := rfl
  scrP := rfl
  args := rfl
  go := rfl
  again := rfl
  stop := rfl
  wipe := rfl

/-- No instruction loads MXCSR. -/
theorem sign_mx (A : RfcAny) : A.code.allInstrs (fun i => !loadsMxcsr i) = true :=
  sign_allInstrs A.R A.T A.I0.tries
    ⟨fun _ v _ _ => ⟨core_hmacInit v.K.cMx v.K.iMx v.C.hinitMx, core_updC v.K.cMx v.C.updMx,
      core_hmacFin v.K.cMx v.C.hfinMx⟩, A.R.coreMx, A.R.blks.mx⟩ genMx

/-- No instruction writes `rsp` but the frame's push and pop. -/
theorem sign_spSafe (A : RfcAny) : A.code.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (sign_allInstrs A.R A.T A.I0.tries
    ⟨fun _ v _ _ => ⟨core_hmacInit v.K.cSp v.K.iSp v.C.hinitSp,
      allInstrs_imp noSp_of_ns (core_updC v.K.cNs v.C.updNs), core_hmacFin v.K.cSp v.C.hfinSp⟩,
      A.R.coreSp, A.R.blks.sp⟩ genSp)

/-! ## The contract, for each hash function -/

/-- `Verified` from a family of contracts `K i`, each of which the code meets
(correct and constant time), when each state the contract permits is one of
some `K i`'s, whose postcondition implies the contract's, and two states
whose public data agree under the contract are both of the same `K i`'s,
with public data that agree under it. -/
theorem Verified.of_family {T : Target} {c : Prog T.isa} {k : Contract T.isa} {ι : Type}
    (K : ι → Contract T.isa)
    (hc : ∀ i s, (K i).pre s → ∃ t s', Exec T.isa c s t s' ∧ T.abiPreserved s s' ∧ (K i).post s s')
    (hct : ∀ i, ConstantTime T.isa (K i).pre (K i).pub c)
    (hpre : ∀ s, k.pre s → ∃ i, (K i).pre s ∧ ∀ s', (K i).post s s' → k.post s s')
    (hpub : ∀ s₁ s₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ →
      ∃ i, (K i).pre s₁ ∧ (K i).pre s₂ ∧ (K i).pub s₁ s₂)
    (hsat : ∃ s, k.pre s) : Verified T c k := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨i, hi, hpost⟩ := hpre s hs
    obtain ⟨t, s', he, ha, hq⟩ := hc i s hi
    exact ⟨t, s', he, ha, hpost s' hq⟩
  · obtain ⟨i, p₁, p₂, hq⟩ := hpub s₁ s₂ h₁ h₂ hp
    exact hct i s₁ s₂ t₁ t₂ s₁' s₂' p₁ p₂ hq e₁ e₂

namespace RfcAny

variable (A : RfcAny)

/-- The contract for the hash function `k`. -/
abbrev K (k : Nat) (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds) : Contract isa :=
  rfcX86_64 A.R.E.combConsts (A.hashAt k hk).I k 544

theorem code_eq (k : Nat) (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds) : A.code = (cfgOf (A.hashAt k hk)).sign := rfl

/-- The code meets the contract for each hash function. -/
theorem correct (k : Nat) (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds) (s : State) (h : (A.K k hk).pre s) :
    ∃ t s', Exec isa A.code s t s' ∧ abiPreserved s s' ∧ (A.K k hk).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sign_ok (P := A.hashAt k hk) h
  exact ⟨t, s', he, abiPreserved_of_exec (sign_mx A) he hg, hp⟩

theorem ct (k : Nat) (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds) :
    ConstantTime isa (A.K k hk).pre (A.K k hk).pub A.code :=
  sign_ct (P := A.hashAt k hk)

/-- The hash function of a call: `hash`'s 32 bits. -/
abbrev hashOf (s : State) : Nat := ((s.gpr .r9).setWidth 32).toNat

/-- `anyResult` is, for the hash function `k`, the instance's result. -/
theorem anyResult_eq {k : Nat} (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds) (m : Mem) (d dg : Addr) :
    A.I0.anyResult m d dg (A.hashAt k hk).H.D k = some (result (A.hashAt k hk).I m d dg) := by
  have h : some (A.hashAt k hk).ok.SH.H = Spec.HashId.hmac k := (A.hashAt k hk).hmac_eq
  simp only [Spec.Ecdsa.Rfc6979.Instance.anyResult, ← h, Option.map_some]
  rfl

theorem digestLen {k : Nat} (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds) {x : Nat}
    (h : ∀ H, Spec.HashId.mgf1 k = some H → x = H.len) : x = (A.hashAt k hk).H.D := by
  have hm := (A.hashAt k hk).mgf_eq
  rw [h _ hm.symm]
  exact (A.hashAt k hk).v.mgf.len


/-- The tactic arguments that evaluate the contract. -/
macro "any_eval" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| sig_pre [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig,
    X86_64.abi, X86_64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] $[$loc]?)

/-- The comb's one table, or none (the curves without a comb). -/
def TblShape (cs : List (String × List (BitVec 64))) : Prop := cs = [] ∨ ∃ n W, cs = [(n, W)]

/-- The contract permits only the numbers of `hashIds`. -/
theorem any_hash (hcs : TblShape A.R.E.combConsts) {s : State} (h : A.contract.pre s) :
    hashOf s ∈ Spec.Ecdsa.Rfc6979.hashIds := by
  unfold RfcAny.contract at h
  rcases hcs with h0 | ⟨n, W, h0⟩ <;> rw [h0] at h <;> any_eval at h <;>
    repeat (first | exact h.1 | replace h := h.2)

/-- The digest is the hash function's output length. -/
theorem any_len (hcs : TblShape A.R.E.combConsts) {s : State} (h : A.contract.pre s) {k : Nat}
    (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds) (hks : hashOf s = k) :
    (s.gpr .rcx).toNat = (A.hashAt k hk).H.D := by
  have hl : ∀ H, Spec.HashId.mgf1 (hashOf s) = some H → (s.gpr .rcx).toNat = H.len := by
    unfold RfcAny.contract at h
    rcases hcs with h0 | ⟨n, W, h0⟩ <;> rw [h0] at h <;> any_eval at h <;>
      repeat (first | exact h | replace h := h.2)
  rw [hks] at hl
  exact A.digestLen hk hl

theorem r9_eq {s : State} {k : Nat} (hks : hashOf s = k) : (s.gpr .r9).setWidth 32 = BitVec.ofNat 32 k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, ← hks]
  exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm

theorem any_pre (hcs : TblShape A.R.E.combConsts) {s : State} {k : Nat} (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds)
    (hks : hashOf s = k) (h : A.contract.pre s) : (A.K k hk).pre s := by
  have hD := A.any_len hcs h hk hks
  have hsc := A.scratch
  unfold RfcAny.contract at h
  unfold RfcAny.K rfcX86_64
  rcases hcs with h0 | ⟨n, W, h0⟩ <;> rw [h0] at h ⊢ <;> any_eval at h
  · obtain ⟨hsp, hrd, hw, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc, no, nd, ng, nc, -, -⟩ := h
    rw [hD] at hrd og gc rg kg ng
    simp only [hsc, Nat.reduceMul] at hw oc dc gc rc kc nc
    refine ⟨r9_eq hks, hsp, by rw [hrd, Abi.constRegions_nil]; rfl, hw, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd,
      kg, kc, no, nd, ng, nc, fun c hc => absurd hc List.not_mem_nil, ?_⟩
    rw [Abi.constRegions_nil]
    exact fun t ht => absurd ht List.not_mem_nil
  · obtain ⟨hsp, hd, hheld, hfit, hdw, hdr, hds, ht, hw, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc, no, nd,
      ng, nc, -, -⟩ := h
    rw [hD] at ht og gc rg kg ng
    simp only [hsc, Nat.reduceMul] at hw oc dc gc rc kc nc
    refine ⟨r9_eq hks, hsp, ?_, hw, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc, no, nd, ng, nc, ?_, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd, Abi.constRegions_cons, Abi.constRegions_nil]
      rfl
    · intro c hc
      simp only [List.mem_singleton] at hc; subst hc; exact hheld
    · rw [Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
      refine ⟨hfit, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; exact List.mem_cons_self ..)
      · exact hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
      · exact hdr
      · exact hds

theorem any_post (hcs : TblShape A.R.E.combConsts) {s s' : State} {k : Nat}
    (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds) (hks : hashOf s = k) (hD : (s.gpr .rcx).toNat = (A.hashAt k hk).H.D)
    (h : (A.K k hk).post s s') : A.contract.post s s' := by
  dsimp only [RfcAny.K, rfcX86_64] at h
  revert h
  unfold RfcAny.contract
  rcases hcs with h0 | ⟨n, W, h0⟩ <;> rw [h0] <;>
    sig_post [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig,
      X86_64.abi, X86_64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] <;>
    rw [show ((s.gpr .r9).setWidth 32).toNat = k from hks, hD, A.anyResult_eq hk] <;>
    generalize result (A.hashAt k hk).I s.mem (s.gpr .rsi) (s.gpr .rdx) = r <;>
    obtain ⟨o, c⟩ := r <;> cases o <;> exact id

theorem any_res {s₁ s₂ : State} {k : Nat} (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds) (hk₁ : hashOf s₁ = k)
    (hk₂ : hashOf s₂ = k) (hD₁ : (s₁.gpr .rcx).toNat = (A.hashAt k hk).H.D)
    (hD₂ : (s₂.gpr .rcx).toNat = (A.hashAt k hk).H.D)
    (hl : [(Option.map (fun x => x.snd) (A.I0.anyResult s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx) (s₁.gpr .rcx).toNat
        ((s₁.gpr .r9).setWidth 32).toNat)).getD 0] =
      [(Option.map (fun x => x.snd) (A.I0.anyResult s₂.mem (s₂.gpr .rsi) (s₂.gpr .rdx) (s₂.gpr .rcx).toNat
        ((s₂.gpr .r9).setWidth 32).toNat)).getD 0]) :
    (result (A.hashAt k hk).I s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx)).2 =
      (result (A.hashAt k hk).I s₂.mem (s₂.gpr .rsi) (s₂.gpr .rdx)).2 := by
  rw [show ((s₁.gpr .r9).setWidth 32).toNat = k from hk₁, show ((s₂.gpr .r9).setWidth 32).toNat = k from hk₂,
    hD₁, hD₂, A.anyResult_eq hk, A.anyResult_eq hk] at hl
  exact (List.cons.inj hl).1

theorem any_pub (hcs : TblShape A.R.E.combConsts) {s₁ s₂ : State} (h₁ : A.contract.pre s₁)
    (h₂ : A.contract.pre s₂) (hp : A.contract.pub s₁ s₂) :
    ∃ hk : hashOf s₁ ∈ Spec.Ecdsa.Rfc6979.hashIds, (A.K _ hk).pre s₁ ∧ (A.K _ hk).pre s₂ ∧ (A.K _ hk).pub s₁ s₂ := by
  have hk := A.any_hash hcs h₁
  have p₁ := A.any_pre hcs hk rfl h₁
  have hD₁ := A.any_len hcs h₁ hk rfl
  unfold RfcAny.contract at hp
  unfold RfcAny.K rfcX86_64
  rcases hcs' : hcs with h0 | ⟨n, W, h0⟩ <;> rw [h0] at hp <;>
    sig_pub [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig,
      X86_64.abi, X86_64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at hp
  · obtain ⟨hsp, hl, hdi, hsi, hdx, -, h8, h9⟩ := hp
    have hks : hashOf s₂ = hashOf s₁ := by show ((s₂.gpr .r9).setWidth 32).toNat = _; rw [← h9]
    exact ⟨hk, p₁, A.any_pre hcs hk hks h₂, hsp, hdi, hsi, hdx, h8,
      A.any_res hk rfl hks hD₁ (A.any_len hcs h₂ hk hks) hl, fun c hc => by rw [h0] at hc; cases hc⟩
  · obtain ⟨hsp, hsy, hl, hdi, hsi, hdx, -, h8, h9⟩ := hp
    have hks : hashOf s₂ = hashOf s₁ := by show ((s₂.gpr .r9).setWidth 32).toNat = _; rw [← h9]
    refine ⟨hk, p₁, A.any_pre hcs hk hks h₂, hsp, hdi, hsi, hdx, h8,
      A.any_res hk rfl hks hD₁ (A.any_len hcs h₂ hk hks) hl, fun c hc => ?_⟩
    rw [h0] at hc
    simp only [List.mem_singleton] at hc; subst hc; exact hsy

/-- The contract's precondition, from the one for the hash function `k`
with a digest of its output length: for a state that shows it satisfiable. -/
theorem any_pre_of (hcs : TblShape A.R.E.combConsts) {s : State} {k : Nat} (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds)
    (hD : (s.gpr .rcx).toNat = (A.hashAt k hk).H.D) (h : (A.K k hk).pre s) : A.contract.pre s := by
  have hsc := A.scratch
  have hks : hashOf s = k := by
    have h9 : (s.gpr .r9).setWidth 32 = BitVec.ofNat 32 k := h.1
    show ((s.gpr .r9).setWidth 32).toNat = k
    rw [h9, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (hashIds_lt hk) (by decide))
  have hl : ∀ H, Spec.HashId.mgf1 k = some H → (A.hashAt k hk).H.D = H.len := fun H hH => by
    rw [← (A.hashAt k hk).v.mgf.len]
    exact congrArg Spec.Mgf1.Hash.len (Option.some.inj ((A.hashAt k hk).mgf_eq.trans hH))
  unfold RfcAny.K rfcX86_64 at h
  unfold RfcAny.contract
  obtain ⟨-, hsp, hrd, hw, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc, no, nd, ng, nc, held, ht⟩ := h
  rcases hcs with h0 | ⟨n, W, h0⟩ <;> rw [h0] at hrd held ht ⊢ <;> any_eval <;>
    simp only [hsc, Nat.reduceMul, hD, show ((s.gpr .r9).setWidth 32).toNat = k from hks]
  · refine ⟨hsp, by rw [hrd, Abi.constRegions_nil]; rfl, hw, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc, no,
      nd, ng, nc, hk, hl⟩
  · rw [Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single] at ht
    rw [Abi.constRegions_cons, Abi.constRegions_nil] at hrd
    obtain ⟨hfit, hdis⟩ := ht
    refine ⟨hsp, by rw [hrd]; rfl, held _ (List.mem_singleton_self _), hfit, fun r hr => ?_,
      hdis _ (by simp), hdis _ (by simp), by rw [hrd]; rfl, hw, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg,
      kc, no, nd, ng, nc, hk, hl⟩
    rw [hw] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hdis _ (by simp)
    · exact hdis _ (by simp)

/-- The code meets the contract with the hash function as an argument, given
a state the contract permits. -/
theorem verified (hcs : TblShape A.R.E.combConsts) (hsat : ∃ s, A.contract.pre s) :
    Verified X86_64.target A.code A.contract :=
  Verified.of_family (ι := {k // k ∈ Spec.Ecdsa.Rfc6979.hashIds}) (fun i => A.K i.1 i.2)
    (fun i => A.correct i.1 i.2) (fun i => A.ct i.1 i.2)
    (fun _ h => ⟨⟨_, A.any_hash hcs h⟩, A.any_pre hcs _ rfl h,
      fun _ hp => A.any_post hcs _ rfl (A.any_len hcs h _ rfl) hp⟩)
    (fun _ _ h₁ h₂ hp => let ⟨hk, p₁, p₂, q⟩ := A.any_pub hcs h₁ h₂ hp; ⟨⟨_, hk⟩, p₁, p₂, q⟩) hsat

end RfcAny

end VG.Proof.Ecdsa.Rfc6979.X86_64
