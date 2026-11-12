module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecPCall
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Verified
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PreWords
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Sp

/-!
# `vg_rsa_oaep_decrypt_precomputed` on x86-64

`decryptP` calls `vg_rsa_private_checked_precomputed` with the key's
precomputed values `pre` (`DecPCall.lean`). It is constant time but for its
public data, which are `vg_rsa_oaep_decrypt`'s, and `pre`'s address and
length and the modulus' values in it (`pdecK`): the pieces of `DecCT.lean`,
with entry states that also agree on those (`XD`), and the call's
(`callP_ct`). With a state that meets the contract (`preSat`: that of
`Verified.lean`, with a real key, `Proof/Rsa/PreKey.lean`), it meets
`vg_rsa_oaep_decrypt_precomputed`'s contract (`decPrecomputed_ok`); and what
its registration's scrub needs of the contract (`decPrecomputed_postOut`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.Rsa.X86_64 (CrtImpl chkContract chkContractP)
open VG.Proof.RsaPkcs1Enc.X86_64 (privStack privK privNameP privCodeP privCodeP_ok privCodeP_ct privCodeP_spSafe
  privCodeP_depth)
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.HashTable.X86_64 (tables fnsOf names Coh tableOf tabOK_of held_tableOf)
open VG.Proof.HashTable (symsOf_distinct2 putWs add8_toNat)
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-! ## The contract -/

/-- `vg_rsa_oaep_decrypt_precomputed`'s contract on the registers: its
precondition, `decK`'s postcondition, and `decK`'s public data with `pre`,
`pre_len` and the modulus' values in `pre`. -/
def pdecK (ts : List FnTable) : Contract isa where
  pre := (pdspec ts).pre
  post := (decK ts).post
  pub s₁ s₂ := (decK ts).pub s₁ s₂ ∧ stackArg s₁ 19 = stackArg s₂ 19 ∧ stackArg s₁ 20 = stackArg s₂ 20 ∧
    Spec.Rsa.privatePrecomputedLeak s₁.mem (stackArg s₁ 19) (s₁.gpr .r8).toNat =
      Spec.Rsa.privatePrecomputedLeak s₂.mem (stackArg s₂ 19) (s₂.gpr .r8).toNat

/-- What entry states agree on with `a` besides `decK`'s public data. -/
def XD (a s : State) : Prop :=
  PreP s ∧ stackArg s 19 = stackArg a 19 ∧ stackArg s 20 = stackArg a 20 ∧
    Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 19) (s.gpr .r8).toNat =
      Spec.Rsa.privatePrecomputedLeak a.mem (stackArg a 19) (a.gpr .r8).toNat

variable {vs : List MdHash} (hc : Coh vs)

/-! ## The call -/

/-- The modulus' values in `pre`, at the call. -/
theorem leak_entry {s t : State} (hq : PreP s) (he : EnvD s t) (rd wr : List Region) :
    Spec.Rsa.privatePrecomputedLeak (t.callEntry.withRegions rd wr).mem (stackArg s 19) (s.gpr .r8).toNat =
      Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 19) (s.gpr .r8).toNat := by
  have hle : Spec.Rsa.precomputedWords (s.gpr .r8).toNat ≤ (stackArg s 20).toNat := by
    rw [hq.hpl]; unfold Spec.Rsa.privatePrecomputedWords; omega
  simp only [Spec.Rsa.privatePrecomputedLeak, State.withRegions_mem]
  rw [← VG.Proof.Rsa.wordsAt_take _ _ hle, ← VG.Proof.Rsa.wordsAt_take _ _ hle,
    wordsP_of_frame hq (frD_entry he)]

/-- At the call, with the tables and `PreP`. -/
def JPC (w₁ w : MdHash) (s t : State) : Prop :=
  ((DCall s (privWP s) t ∧ HS (tableOf w) s t) ∧ HL (tableOf w₁) s) ∧ PreP s

/-- After the call. -/
def JPR (w₁ w : MdHash) (s t : State) : Prop :=
  ((EnvD s t ∧ ∃ V, Rep t.mem (fb s) (stackArg s 15) V (privWP s)) ∧ HS (tableOf w) s t) ∧ HL (tableOf w₁) s

theorem callP_ct (c : CrtImpl) {w₁ w : MdHash} :
    RelCT isa (Two (DAt (tables vs) XD (JPC w₁ w))) (.call (privNameP c) (privCodeP c))
      (Two (DAt (tables vs) XD (JPR w₁ w))) := by
  refine two_post (RelCT.callEx (k := chkContractP) (privCodeP_ok c) (privCodeP_ct c)
    fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_) fun a t ⟨s, S, j⟩ => ?_
  · obtain ⟨⟨⟨h₁, -⟩, -⟩, q₁⟩ := j₁
    obtain ⟨⟨⟨h₂, -⟩, -⟩, q₂⟩ := j₂
    have hp₁ := S₁.1.1.1
    have hp₂ := S₂.1.1.1
    obtain ⟨r₁, g₁, n₁, e₁⟩ := privD_view S₁ h₁
    obtain ⟨r₂, g₂, n₂, e₂⟩ := privD_view S₂ h₂
    obtain ⟨c₁, w₁'⟩ := privDP_covers hp₁ q₁ h₁
    obtain ⟨c₂, w₂'⟩ := privDP_covers hp₂ q₂ h₂
    have e : ∀ {s t : State}, DPre s → DCall s (privWP s) t → ∀ i, i < 16 → 14 ≤ i →
        stackArg (t.callEntry.withRegions (privRdDP s) (privWrD s)) i = stackArg s (i + 5) := fun hp h i hi hi' => by
      rw [privDP_args hp h _ _ hi]
      rcases (show i = 14 ∨ i = 15 by omega) with rfl | rfl <;> simp [privWP, upd]
    have kx : ∀ {s t : State}, DCall s (privWP s) t →
        (t.callEntry.withRegions (privRdDP s) (privWrD s)).gpr .rcx = s.gpr .r8 := fun h => by
      rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h.rcx]
    exact ⟨privRdDP s₁, privWrD s₁, privRdDP s₂, privWrD s₂, privDP_pre hp₁ q₁ h₁, privDP_pre hp₂ q₂ h₂,
      ⟨⟨List.map_inj_left.mp (r₁.trans r₂.symm), g₁.trans g₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩,
        by rw [e hp₁ h₁ 14 (by decide) (by decide), e hp₂ h₂ 14 (by decide) (by decide), S₁.1.2.2.1, S₂.1.2.2.1],
        by rw [e hp₁ h₁ 15 (by decide) (by decide), e hp₂ h₂ 15 (by decide) (by decide), S₁.1.2.2.2.1,
          S₂.1.2.2.2.1],
        by rw [e hp₁ h₁ 14 (by decide) (by decide), e hp₂ h₂ 14 (by decide) (by decide), kx h₁, kx h₂,
          leak_entry q₁ h₁.he, leak_entry q₂ h₂.he, S₁.1.2.2.2.2, S₂.1.2.2.2.2]⟩,
      c₁, w₁', c₂, w₂', by rw [h₁.he.rsp, h₂.he.rsp, S₁.fb, S₂.fb]⟩
  · obtain ⟨⟨⟨h, hs⟩, hl⟩, q⟩ := j
    exact X86_64.WP.mono_syms (privDP_call c S.1.1.1 q h) fun u ⟨he, R, _⟩ sy =>
      ⟨s, S, ⟨⟨he, _, R⟩, hs.1, sy.trans hs.2⟩, hl⟩

/-! ## The function -/

include hc in
theorem decBodyP_ct (c : CrtImpl) {w₁ w : MdHash} (hw₁ : w₁ ∈ vs) (hw : w ∈ vs) :
    RelCT isa (Two (DAt (tables vs) XD fun s t => ((JA s t ∧ HS (tableOf w) s t) ∧ HL (tableOf w₁) s) ∧ PreP s))
      (decBodyP (fnsOf vs) (privNameP c) (privCodeP c)) fun _ _ => True := by
  unfold decBodyP Impl.Mgf1.X86_64.seqs Impl.Mgf1.X86_64.seqs Impl.Mgf1.X86_64.seqs
  obtain ⟨_, hH⟩ := dHeadP_taint
  refine RelCT.seq (d_post (J' := JPC w₁ w)
    (two_taint [.rsp] (d_pins_rsp fun s t _ h => by rw [h.1.1.1]; rfl) hH)
    fun s t hs h => by
      obtain ⟨⟨⟨rfl, hs'⟩, hl⟩, q⟩ := h
      exact X86_64.WP.mono_syms (decHeadP_ok hs.1 q) fun _ e sy => ⟨⟨⟨e, hs'.1, sy.trans hs'.2⟩, hl⟩, q⟩) ?_
  refine RelCT.seq (callP_ct c) ?_
  -- `scratch` back to `sScr`, and the table of the label's hash function to its slot.
  refine RelCT.seq (d_post (J' := fun s t => (JS s t ∧ HS (tableOf w) s t) ∧ HL (tableOf w₁) s)
    (two_taintF [] [] fb (fun a => [outR a, mlR a, scrD a]) (fun _ _ => 0)
      (fun a t ⟨s, S, ⟨⟨he, _⟩, _⟩, _⟩ => by
        rw [← S.fb, ← S.out_eq, ← S.ml_eq, ← S.scr_eq]
        exact ⟨he.frv S.1.1.1, fun k hk => by cases hk⟩)
      nopin (by decide) dRestore_taint)
    fun s t hs h => ?_) (decAfterTab_ct hc hw₁ hw)
  obtain ⟨⟨⟨he, V, R⟩, hs'⟩, hl⟩ := h
  have hp := hs.1
  obtain ⟨-, -, hd⟩ := hs.2
  obtain ⟨hmL, -, hDmL⟩ := held_tableOf hl
  exact WP.mono (restoreTab_ok hp he hs'.2 R (tabOK_of hc hd hw₁) hmL hDmL)
    fun t' ⟨he', L', R', sy', _⟩ => ⟨⟨⟨he', L', V, _, ArgsD_privWP s, R'⟩, hs'.1, sy'⟩, hl⟩

include hc in
theorem decP_constantTime (c : CrtImpl) :
    ConstantTime isa (pdecK (tables vs)).pre (pdecK (tables vs)).pub
      (decryptP (fnsOf vs) (privNameP c) (privCodeP c)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  obtain ⟨p₁, q₁⟩ := preDP_of h₁
  obtain ⟨p₂, q₂⟩ := preDP_of h₂
  obtain ⟨⟨T₁, hT₁, hheld₁⟩, ⟨T, hT, hheld⟩, -⟩ := p₁.2
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨hpub, h19, h20, hl⟩ := hpub
  have key := relCT_alloc (P := fun x y => (DPreT (tables vs) x ∧ PreP x) ∧ (DPreT (tables vs) y ∧ PreP y) ∧
      ((decK (tables vs)).pub x y ∧ stackArg x 19 = stackArg y 19 ∧ stackArg x 20 = stackArg y 20 ∧
        Spec.Rsa.privatePrecomputedLeak x.mem (stackArg x 19) (x.gpr .r8).toNat =
          Spec.Rsa.privatePrecomputedLeak y.mem (stackArg y 19) (y.gpr .r8).toNat) ∧
      Abi.tableHeld 64 x.mem (stackArg x 17) (FnTable.words isa x (tableOf w₁)) ∧
      Abi.tableHeld 64 x.mem (stackArg x 18) (FnTable.words isa x (tableOf w)))
    ((decBodyP_ct hc c hw₁ hw).mono (fun _ _ ⟨x, y, ⟨⟨hx, qx⟩, ⟨hy, qy⟩, ⟨hxy, x19, x20, xl⟩, hh₁, hh⟩, ex, ey⟩ =>
      ⟨x, ⟨x, ⟨⟨hx, qx, rfl, rfl, rfl⟩, decPub_refl _ x⟩, ⟨⟨ex, hh, by rw [ex]; rfl⟩, hh₁⟩, qx⟩,
        ⟨y, ⟨⟨hy, qy, x19.symm, x20.symm, xl.symm⟩, hxy⟩, ⟨⟨ey, (hxy.2.2.2.2.2.2 _ (List.mem_map_of_mem hw)).mp hh,
          by rw [ey]; rfl⟩, (hxy.2.2.2.2.2.1 _ (List.mem_map_of_mem hw₁)).mp hh₁⟩, qy⟩⟩) fun _ _ h => h)
  exact (key _ _ _ _ _ _ ⟨⟨p₁, q₁⟩, ⟨p₂, q₂⟩, ⟨hpub, h19, h20, hl⟩, hheld₁, hheld⟩ e₁ e₂).1

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

/-- The stack arguments of `preState`; the key (`keyMem`) has `n` at
`0x2000`, `p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgs : List Nat :=
  [1, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x4700, 0, 0x4100, 64, 0x20000, 0x820, 0x300000,
    0x300000, 0x4800, 24]

/-- The memory of `preState`: the stack arguments from `0x10008`, and the
key. -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10008 i && Nat.blt i 0x100B0 then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x10008) / 8) 0 / 256 ^ ((i - 0x10008) % 8))
  else bif keyIn i then keyMem a else 0

/-- `decSatBase` with the key and its precomputed values. -/
def preState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x1800 | .rcx => 0x2000 | .r8 => 64 | .r9 => 0x3000
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x4800, 192⟩, ⟨0x300000, 88⟩, ⟨0x300000, 88⟩, ⟨0x10008, 168⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 2080 * 8⟩]

theorem preState_key (vs : List MdHash) (w : MdHash) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTable preState vs w).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTable preState vs w).mem 0x4200 32)
      (Spec.Rsa.bytesAt (withTable preState vs w).mem 0x4300 32) =
        some (Spec.Rsa.wordsAt (withTable preState vs w).mem 0x4800 24) := by
  refine key_pre_of fun a ha => ?_
  have hlt : a.toNat < 0x10000 := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
  have hs : (Nat.ble 0x10008 a.toNat && Nat.blt a.toNat 0x100B0) = false := by
    refine Bool.eq_false_iff.mpr fun h => ?_
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    omega
  show putWs preMem 0x300000 (twL vs w) a = _
  rw [putWs_byte (by simp; omega) (twL_room vs w)]
  show (bif _ then _ else _) = _
  rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem pre_args : ∀ j < 21, stackArg preState j = BitVec.ofNat 64 (preArgs.getD j 0) := by decide

/-- The precondition, from the facts of a state. -/
theorem dec_pre_of {ts : List FnTable} {s : State} (hg : s.gpr = preState.gpr)
    (ha : ∀ j < 21, stackArg s j = BitVec.ofNat 64 (preArgs.getD j 0))
    (hrd : s.rd = preState.rd) (hwr : s.wr = preState.wr)
    (hH : ∃ T ∈ ts, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hsy : ((ts.map (·.fns)).flatten ++ (ts.map (·.fns)).flatten).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hK : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem 0x2000 64) (Spec.Rsa.bytesAt s.mem 0x4200 32)
      (Spec.Rsa.bytesAt s.mem 0x4300 32) = some (Spec.Rsa.wordsAt s.mem 0x4800 24)) :
    (pdspec ts).pre s := by
  have hsp : s.gpr .rsp = 0x10000 := by rw [hg]; rfl
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (8 * (j + 1)) := fun j => by
    simp only [stackArgAddr, hsp]
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, decStack, RsaPkcs1Enc.X86_64.privStack,
    Impl.RsaOaep.X86_64.frameBytes, stackArgs_twentyone, List.append_eq]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide),
    ha 16 (by decide), ha 17 (by decide), ha 18 (by decide), ha 19 (by decide), ha 20 (by decide), preArgs,
    List.getD_cons_succ, List.getD_cons_zero, hg, hrd, hwr, hA]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, decStack, RsaPkcs1Enc.X86_64.privStack,
    Impl.RsaOaep.X86_64.frameBytes, stackArgs_twentyone, List.append_eq]
  sig_and_intros
  all_goals first
    | exact hK
    | exact hH
    | exact hsy
    | exact Region.disjoint_of_sep (by decide)
    | (simp only [Spec.Rsa.lenValid]; decide)
    | rfl
    | decide

theorem preSat {vs : List MdHash} {w : MdHash} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 32) :
    ∃ s, (pdspec (tables vs)).pre s := by
  have hA : ∀ j < 21, (stackArgAddr preState j).toNat + 8 ≤ 0x300000 := fun j hj => by
    have c0 : (0x10000 : Addr).toNat = 65536 := rfl
    simp only [stackArgAddr, preState, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  exact ⟨withTable preState vs w, dec_pre_of rfl
    (fun j hj => (withTable_arg _ vs w (hA j hj)).trans (pre_args j hj)) rfl rfl
    ⟨tableOf w, List.mem_map_of_mem hw, withTable_held _ vs w⟩ (symsOf_distinct2 hl) (preState_key vs w)⟩


theorem pdec_implies (ts : List FnTable) (hsat : ∃ s, (pdspec ts).pre s) : (pdecK ts).Implies (pdspec ts) where
  pre := fun _ h => h
  post := by sig_implies_post [Spec.RsaOaep.decryptPrecomputedMdTablesContract,
      Spec.RsaOaep.decryptPrecomputedMdTablesSig, Spec.RsaOaep.decryptSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex,
      abi, argRegs, pdecK, decK, decStack, privStack, Impl.RsaOaep.X86_64.frameBytes, stackArgs_twentyone,
      List.append_eq, tabL, tabR, tabFns]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
      Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
      Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, decStack, privStack,
      Impl.RsaOaep.X86_64.frameBytes, stackArgs_twentyone, List.append_eq, tabL, tabR, tabFns] at h
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero,
      Option.some.injEq] at h
    obtain ⟨hsp, hsy, htab, htab', hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
      a13, a14, a15, a16, a17, a18, a19, a20, -⟩ := h
    obtain ⟨hne, hlk⟩ := List.append_inj hl (by
      simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', h8, a0])
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, h8]) hne
    refine ⟨⟨?_, by simp only [stackArgs_nineteen, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
      a15, a16, a17, a18], hn, he, fun f hf => hsy f (List.mem_append_left _ hf),
      fun T hT => htab _ _ rfl rfl T hT, fun T hT => htab' _ _ rfl rfl T hT⟩, a19, a20, hlk⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := hsat

/-- It writes `rsp` only in its frame's push and pop, and its callees in
theirs. -/
theorem decP_spSafe (vs : List MdHash) (c : CrtImpl) :
    (decryptP (fnsOf vs) (privNameP c) (privCodeP c)).all (fun i => !isa.writesSp i) = true := by
  obtain ⟨hgi, hgu, hgf⟩ := Proof.HashTable.X86_64.fnsGood_of vs
  simp only [decryptP, decBodyP, byLen, lens, decTail, decMain, mgfT, Impl.Mgf1.X86_64.seqs, Code.all,
    decFail_good.all, (hashLabelT_good hgi hgu hgf oLh).all, (Table.mgfT_good hgi hgu hgf _).all,
    (accLh_good _).all, (scan_good _).all, (clearBuf_good _).all, copyT_good.all, shift_good.all,
    outLoop_good.all, privCodeP_spSafe c]
  rfl

/-- `vg_rsa_oaep_decrypt_precomputed`, with the tables of `vs`, calling
`vg_rsa_private_checked_precomputed` for the implementation `c` of the
CRT. -/
theorem decPrecomputed_ok (vs : List MdHash) (h : OK vs) (c : CrtImpl) :
    Verified target (decryptP (fnsOf vs) (privNameP c) (privCodeP c)) (pdspec (tables vs)) :=
  Verified.of_correct (k := pdecK (tables vs)) (decP_correct h.1 c) (decP_constantTime h.1 c)
    (pdec_implies _ (let ⟨_, hw⟩ := h.mem; preSat hw h.2.1))

/-! ## Without secret residue -/

/-- `vg_rsa_oaep_decrypt_precomputed`'s postcondition reads the memory on
return only in `out` and `msg_len`. -/
theorem decPrecomputed_postOut (ts : List FnTable) :
    VG.X86_64.Scrub.PostOut (pdspec ts) (Spec.RsaOaep.decryptPrecomputedMdTablesSig.retBits 64) :=
  VG.X86_64.Scrub.postOut_of_local_pre (leak := some _) (VG.X86_64.Scrub.ScrubAbi.plain.tables _ _)
    fun vs m m₁ m₂ r hlen hpre hb h => by
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 26) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨outLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨msgLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨nLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨e, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨eLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨p, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨q, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨qLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dp, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dpLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dq, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dqLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨qinv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨qinvLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨label, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨labelLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ctLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨scratch, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨scratchLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨hash, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨mgf1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pre, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨preLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp only [Spec.RsaOaep.decryptPrecomputedMdTablesSig, Spec.RsaOaep.decryptSig, List.cons_append,
      List.nil_append, Sig.bufs, List.mem_cons, forall_eq_or_imp] at hb
    have hol : outLen.toNat = nLen.toNat := hpre.2.1
    have hby : Spec.Rsa.bytesAt m₂ out nLen.toNat = Spec.Rsa.bytesAt m₁ out nLen.toNat :=
      VG.Proof.Rsa.X86_64.bytesAt_agree (by simp only [Elem.size]; omega)
        (by have := outLen.isLt; simp only [Elem.size]; omega) hb.1
    have hw : m₂.readW msgLen 64 = m₁.readW msgLen 64 := VG.Proof.Rsa.X86_64.readW_agree (by decide) (by decide) hb.2.1
    intro H G hH hG
    have h' : Spec.RsaOaep.writtenDecrypt m₁ out msgLen nLen.toNat r _ := h H G hH hG
    show Spec.RsaOaep.writtenDecrypt m₂ out msgLen nLen.toNat r _
    revert h'
    generalize Spec.RsaOaep.decrypt _ _ _ _ _ _ _ _ _ _ _ = o
    cases o <;> simp only [Spec.RsaOaep.writtenDecrypt, hby, hw] <;> exact id

end VG.Proof.RsaOaep.X86_64
