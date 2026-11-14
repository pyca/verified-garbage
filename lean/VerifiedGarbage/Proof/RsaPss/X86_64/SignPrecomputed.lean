module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SignPCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCt
public import VerifiedGarbage.Proof.RsaPss.X86_64.Sat
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCFixed
import VerifiedGarbage.Proof.RsaPss.X86_64.Instances
import VerifiedGarbage.Proof.Rsa.PreWords
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame

/-!
# `vg_rsa_pss_sign_precomputed` on x86-64

`signCP` calls `vg_rsa_private_checked_precomputed` with the key's
precomputed values `pre` (`SignPCall.lean`). It is constant time but for its
public data, which are `vg_rsa_pss_sign`'s, and `pre`'s address and length
and the modulus' values in it (`psignK`): the pieces of `SignCCt.lean`, with
entry states that also agree on those (`XP`), and the call's (`scallP_ct`).
With a state that meets the contract (`preSat`: that of `Sat.lean`, with `p`,
`q`, `dP`, `dQ` and `qInv` of 32 bytes and a real key, `Proof/Rsa/PreKey.lean`),
it meets `vg_rsa_pss_sign_precomputed`'s contract (`signPrecomputed_ok`); and
what its registration's scrub needs of the contract
(`signPrecomputed_postOut`).
-/

@[expose] public section
namespace VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (CrtImpl chkContract chkContractP)
open VG.Proof.RsaPkcs1Enc.X86_64 (privNameP privCodeP privCodeP_ok privCodeP_ct privCodeP_spSafe privCodeP_depth)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.HashTable (symsOf symsOf_distinct)
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-! ## The contract -/

/-- `vg_rsa_pss_sign_precomputed`'s contract on the registers: its
precondition, `signK`'s postcondition, and `signK`'s public data with `pre`,
`pre_len` and the modulus' values in `pre`. -/
def psignK (tsH tsG : List FnTable) : Contract isa where
  pre := (pspec tsH tsG).pre
  post := (signK tsH tsG).post
  pub s₁ s₂ := (signK tsH tsG).pub s₁ s₂ ∧ stackArg s₁ 18 = stackArg s₂ 18 ∧ stackArg s₁ 19 = stackArg s₂ 19 ∧
    Spec.Rsa.privatePrecomputedLeak s₁.mem (stackArg s₁ 18) (s₁.gpr .rcx).toNat =
      Spec.Rsa.privatePrecomputedLeak s₂.mem (stackArg s₂ 18) (s₂.gpr .rcx).toNat

/-- What entry states agree on with `a` besides `signK`'s public data. -/
def XP (a s : State) : Prop :=
  PreP s ∧ stackArg s 18 = stackArg a 18 ∧ stackArg s 19 = stackArg a 19 ∧
    Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 18) (s.gpr .rcx).toNat =
      Spec.Rsa.privatePrecomputedLeak a.mem (stackArg a 18) (a.gpr .rcx).toNat

variable {tsH tsG : List FnTable} {H : Hash}

/-! ## The call -/

/-- Before the call. -/
def SJPP (H : Hash) (s t : State) : Prop :=
  SS H s t [] [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    (∀ i < 16, word t.mem (fb s) (8 * i) = pArgP s i) ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rcx ∧
    t.gpr .rdx = s.gpr .rdx ∧ t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9

theorem sjp_of {s t : State} (h : SJPP H s t) : SJP H s t :=
  let ⟨v, hrd, hM, ha, di, si, dx, cx, r8, r9⟩ := h
  ⟨v, hrd, hM, fun i hi => by rw [ha i (by omega_using [hi])]; simp only [pArgP, hi, ↓reduceIte], di, si, dx, cx, r8, r9⟩

theorem cprivP_ct : RelCT isa (Two fun a t => SAt tsH tsG XP (CJT H) a t ∧ isa.eval .e t = some false)
    (.block privArgsP) (Two (SAt tsH tsG XP (SJPP H))) := by
  obtain ⟨_, hc⟩ := privArgsP_fixed
  refine two_post (stwo (H := H) [] [] (fun _ => [])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, _⟩ => ?_
  obtain ⟨v, hrd, hM, _⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  exact X86_64.WP.mono_syms (WP.keepIn (by decide) (by exact Nat.zero_le 16)
    (privArgsP_ok hp S.x.1 v.L hrd v.wr hM R (hw 16 (by decide)) (hw 17 (by decide)) (hw 18 (by decide))
      (hw 19 (by decide)) (hw 20 (by decide)) (hw 22 (by decide))))
    fun u ⟨⟨k', L', ⟨W', R', ha, _⟩, di, si, dx, cx, r8, r9⟩, f⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' (fun _ h => by cases h) trivial sy, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f,
      fun i hi => (R'.fr i (by unfold nW frameBytes; omega_arith)).trans (ha i hi), di, si, dx, cx, r8, r9⟩

/-- The memory at the call's entry, as on ours but where we write. -/
theorem frame_entry {s t : State} (hsp : t.gpr .rsp = fb s) (hM : Frame (wrR s) s.mem t.mem) :
    Frame (wrR s) s.mem t.callEntry.mem := by
  have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  exact hM.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret8_sub s⟩)

/-- The modulus' values in `pre`, at the call. -/
theorem leak_entry {s t : State} (hq : PreP s) (hsp : t.gpr .rsp = fb s) (hM : Frame (wrR s) s.mem t.mem)
    (rd wr : List Region) :
    Spec.Rsa.privatePrecomputedLeak (t.callEntry.withRegions rd wr).mem (stackArg s 18) (s.gpr .rcx).toNat =
      Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 18) (s.gpr .rcx).toNat := by
  have hle : Spec.Rsa.precomputedWords (s.gpr .rcx).toNat ≤ (stackArg s 19).toNat := by
    rw [hq.hpl]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
  simp only [Spec.Rsa.privatePrecomputedLeak, State.withRegions_mem]
  rw [← VG.Proof.Rsa.wordsAt_take _ _ hle, ← VG.Proof.Rsa.wordsAt_take _ _ hle,
    wordsP_of_frame hq (frame_entry hsp hM)]

theorem scallP_ct (c : CrtImpl) :
    RelCT isa (Two (SAt tsH tsG XP (SJPP H))) (.call (privNameP c) (privCodeP c)) (Two (SAt tsH tsG XP (SJR H))) := by
  refine two_post (RelCT.callEx (k := chkContractP) (privCodeP_ok c) (privCodeP_ct c)
    fun t₁ t₂ ⟨a, ⟨s₁, S₁, h₁⟩, ⟨s₂, S₂, h₂⟩⟩ => ?_) fun a t ⟨s, S, h⟩ => ?_
  · obtain ⟨c₁, w₁⟩ := privP_covers S₁.ps S₁.x.1 h₁.2.1 h₁.1.wr
    obtain ⟨c₂, w₂⟩ := privP_covers S₂.ps S₂.x.1 h₂.2.1 h₂.1.wr
    have hpub := scall_pub S₁ (sjp_of h₁) S₂ (sjp_of h₂)
    obtain ⟨v₁, -, hM₁, ha₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ := h₁
    obtain ⟨v₂, -, hM₂, ha₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ := h₂
    have e : ∀ {s t : State}, SPre tsH tsG s → SS H s t [] [] (fun _ _ => True) →
        (∀ i < 16, word t.mem (fb s) (8 * i) = pArgP s i) → ∀ i, i < 16 → 14 ≤ i →
        stackArg (t.callEntry.withRegions (pRdP s) (pWr s)) i = stackArg s (i + 4) := fun hp v ha i hi hi' => by
      rw [stackArg_call hp v.L.rsp _ _ hi, ha i hi]; simp only [pArgP]; rw [ifn (by omega_using [hi'])]
    have kx : ∀ {s t : State}, t.gpr .rcx = s.gpr .rcx →
        (t.callEntry.withRegions (pRdP s) (pWr s)).gpr .rcx = s.gpr .rcx := fun h => by
      rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h]
    exact ⟨_, _, _, _, privP_pre S₁.ps S₁.x.1 v₁.L.rsp hM₁ ha₁ di₁ si₁ dx₁ cx₁ r8₁ r9₁,
      privP_pre S₂.ps S₂.x.1 v₂.L.rsp hM₂ ha₂ di₂ si₂ dx₂ cx₂ r8₂ r9₂,
      ⟨hpub, by rw [e S₁.ps v₁ ha₁ 14 (by decide) (by decide), e S₂.ps v₂ ha₂ 14 (by decide) (by decide),
          S₁.x.2.1, S₂.x.2.1],
        by rw [e S₁.ps v₁ ha₁ 15 (by decide) (by decide), e S₂.ps v₂ ha₂ 15 (by decide) (by decide),
          S₁.x.2.2.1, S₂.x.2.2.1],
        by rw [e S₁.ps v₁ ha₁ 14 (by decide) (by decide), e S₂.ps v₂ ha₂ 14 (by decide) (by decide), kx cx₁, kx cx₂,
          leak_entry S₁.x.1 v₁.L.rsp hM₁, leak_entry S₂.x.1 v₂.L.rsp hM₂, S₁.x.2.2.2, S₂.x.2.2.2]⟩,
      c₁, w₁, c₂, w₂, by rw [v₁.L.rsp, v₂.L.rsp, S₁.fb, S₂.fb]⟩
  · obtain ⟨v, hrd, hM, ha, di, si, dx, cx, r8, r9⟩ := h
    obtain ⟨V, W, R, hw, -⟩ := v.W
    have hp := S.ps
    obtain ⟨hc, hcw⟩ := privP_covers hp S.x.1 hrd v.wr
    have h14 : ∀ i < 14, word t.mem (fb s) (8 * i) = pArg s i := fun i hi => by
      rw [ha i (by omega_using [hi])]; simp only [pArgP, hi, ↓reduceIte]
    refine X86_64.WP.mono_syms (privWith_call (k := chkContractP) (fun _ _ h => h) (privCodeP_ok c)
      (SpSafe.of_all (privCodeP_spSafe c)) (privCodeP_depth c) hp v.L.rsp hM h14 di dx cx r8 r9
      (privP_pre hp S.x.1 v.L.rsp hM ha di si dx cx r8 r9) hc hcw)
      fun u ⟨rd', wr', cs', _, _, hk', _⟩ sy => ?_
    have R' := R.of_keep v.L.geo fun x hx => hk' x hx
    exact ⟨s, S, v.next (v.L.of_rep' R R' rfl (cs' .rsp (by decide)) wr') wr' R' hw trivial sy⟩

/-! ## The function -/

variable {f : MdFns} {g : Impl.Mgf1.X86_64.Table.Fns}
  (hsel : ∀ a, SPre tsH tsG a → ∃ T Hs Gs, SGood (tsH := tsH) (tsG := tsG) f g a T Hs Gs)
  (hspE : ∀ i ∈ idxs, SpSafe (encode f (ofIdx i) g))
  (hdE : ∀ i ∈ idxs, (encode f (ofIdx i) g).x86_64Depth ≤ encStack)

include hsel hspE hdE in
/-- `signCP` is constant time. -/
theorem signCP_ct (c : CrtImpl) (H : Hash) :
    ConstantTime isa (psignK tsH tsG).pre (psignK tsH tsG).pub (signCP f g (privNameP c) (privCodeP c)) :=
  RelCT.constantTime (valloc ((scbodyWith_ct (Xs := XP) hsel hspE hdE H
      (cprivP_ct.seq (scallP_ct c))).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub, h18, h19, hl⟩, e₁, e₂⟩ => by
      obtain ⟨p₁, q₁⟩ := preSP_of h₁
      obtain ⟨p₂, q₂⟩ := preSP_of h₂
      obtain ⟨T, Hs, Gs, G⟩ := hsel s₁ p₁
      have hi : idxWord s₂ = idxWord s₁ := by
        have e₂' := (G.sel s₂ hpub p₂).idx
        have e₁' := (G.sel s₁ (spub_refl tsH tsG s₁) p₁).idx
        exact e₂'.trans e₁'.symm
      exact ⟨s₁, ⟨s₁, ⟨p₁, spub_refl tsH tsG s₁, p₁, rfl, q₁, rfl, rfl, rfl⟩, e₁⟩,
        ⟨s₂, ⟨p₁, hpub, p₂, hi, q₂, h18.symm, h19.symm, hl.symm⟩, e₂⟩⟩)
    fun _ _ h => h))

theorem signCP_spAll (hE : ∀ i ∈ idxs, SpSafe (encode f (ofIdx i) g))
    (hdE : ∀ i ∈ idxs, (encode f (ofIdx i) g).x86_64Depth ≤ encStack) {privN : String} {privC : Prog isa}
    (hC : SpSafe privC) :
    (signCP f g privN privC).allInstrs (fun i => !isa.writesSp i) = true := by
  simp only [signCP, signCBodyWith, seqs, Code.allInstrs, (enc_calls hE hdE).1, spAll_of hC, rec_all,
    List.all_append, signFail, Bool.and_true, Bool.true_and]
  rfl

theorem signCP_depth {privN : String} {privC : Prog isa} :
    (signCP f g privN privC).x86_64Depth = (Impl.RsaPss.X86_64.signC f g privN privC).x86_64Depth := by
  simp only [signCP, Impl.RsaPss.X86_64.signC, signCBody, signCBodyWith, seqs, Code.x86_64Depth]

theorem signCP_xd (hdE : ∀ i ∈ idxs, (encode f (ofIdx i) g).x86_64Depth ≤ encStack)
    (hE : ∀ i ∈ idxs, SpSafe (encode f (ofIdx i) g)) {privN : String} {privC : Prog isa}
    (hd : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes) :
    (signCP f g privN privC).x86_64Depth ≤ signStack :=
  signCP_depth ▸ signC_xd hdE hE hd

include hsel hspE hdE in
theorem signCP_correct (c : CrtImpl) (s : State) (h : (psignK tsH tsG).pre s) :
    ∃ t s', Exec isa (signCP f g (privNameP c) (privCodeP c)) s t s' ∧ abiPreserved s s' ∧
      (psignK tsH tsG).post s s' := by
  obtain ⟨hp, hq⟩ := preSP_of h
  obtain ⟨T, Hs, Gs, G⟩ := hsel s hp
  have hC : SpSafe (privCodeP c) := SpSafe.of_all (privCodeP_spSafe c)
  have hsp : SpSafe (signCP f g (privNameP c) (privCodeP c)) := by
    have h := signCP_spAll hspE hdE (privN := privNameP c) hC
    rw [Code.allInstrs_eq] at h
    intro i hi
    simpa using List.all_eq_true.mp h i hi
  exact signCode_correct hsp (signCP_xd hdE hspE (privCodeP_depth c)) hp
    (signCP_ok hspE hdE (privCodeP_ok c) hC (privCodeP_depth c) hp hq (G.sel s (spub_refl tsH tsG s) hp))

theorem psign_implies (hsat : ∃ s, (pspec tsH tsG).pre s) : (psignK tsH tsG).Implies (pspec tsH tsG) where
  pre := fun _ h => h
  post := by sig_implies_post [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
      Spec.MdHashTable.param, Abi.withTables, Sig.wordIndex, abi, argRegs, psignK, signK, signStack, stackArgs_twenty,
      List.append_eq, tabFns]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.MdHashTable.param,
      Abi.withTables, Sig.wordIndex, abi, argRegs, signStack, stackArgs_twenty, List.append_eq, tabFns] at h
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero,
      Option.some.injEq] at h
    obtain ⟨hsp, hsy, htab, htab', hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
      a13, a14, a15, a16, a17, a18, a19, -⟩ := h
    obtain ⟨hne, hlk⟩ := List.append_inj hl (by
      simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', hcx, h9])
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hne
    refine ⟨⟨?_, by simp only [stackArgs_eighteen, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
      a15, a16, a17], hn, he, hsy, fun T hT => htab _ _ rfl rfl T hT, fun T hT => htab' _ _ rfl rfl T hT⟩,
      a18, a19, hlk⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := hsat

/-! ## A state that meets the contract -/

/-- The stack arguments of `preState D`; the key (`keyMem`) has `n` at
`0x2000`, `p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgs (D : Nat) : List Nat :=
  [0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x5000, D, 0x5100, 0, 0x20000, 2080, 0x300000,
    0x300100, 0x4800, 24]

/-- The memory of `preState D`: the stack arguments from `0x10008`, and the
key. -/
def preMem (D : Nat) (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10008 i && Nat.blt i 0x100A8 then
    BitVec.ofNat 8 ((preArgs D).getD ((i - 0x10008) / 8) 0 / 256 ^ ((i - 0x10008) % 8))
  else bif keyIn i then keyMem a else 0

/-- `signSatBase D` with the key (`keyMem`) and its precomputed values. -/
def preState (D : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := preMem D
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x5000, D⟩, ⟨0x5100, 0⟩, ⟨0x4800, 192⟩, ⟨0x300000, 88⟩, ⟨0x300100, 88⟩, ⟨0x10008, 160⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 2080 * 8⟩]

/-- Its stack arguments. -/
def preArgW (D : Nat) (j : Nat) : BitVec 64 := BitVec.ofNat 64 ((preArgs D).getD j 0)

theorem preState_key (D : Nat) (a : Addr) (ha : keyIn a.toNat = true) : (preState D).mem a = keyMem a := by
  have hs : (Nat.ble 0x10008 a.toNat && Nat.blt a.toNat 0x100A8) = false := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
    refine Bool.eq_false_iff.mpr fun h => ?_
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    omega
  show (bif _ then _ else _) = _
  rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem withTabs_key {vs : List MdHash} {w : MdHash} (s : State)
    (h : ∀ a : Addr, keyIn a.toNat = true → s.mem a = keyMem a) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTabs s vs w).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTabs s vs w).mem 0x4200 32)
      (Spec.Rsa.bytesAt (withTabs s vs w).mem 0x4300 32) =
        some (Spec.Rsa.wordsAt (withTabs s vs w).mem 0x4800 24) := by
  refine key_pre_of fun a ha => ?_
  have hlt : a.toNat < 0x300000 := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
  simp only [withTabs, tabMem, Nat.blt_eq.mpr hlt, Bool.cond_true]
  exact h a ha

theorem pre_args (D : Nat) : ∀ j < 20, (stackArgAddr (preState D) j).toNat + 8 ≤ 0x300000 := fun j hj => by
  have c0 : (0x10000 : Addr).toNat = 65536 := rfl
  simp only [stackArgAddr, preState, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem pre_b16 : ∀ j < 20, stackArg (preState 16) j = preArgW 16 j := by decide
theorem pre_b20 : ∀ j < 20, stackArg (preState 20) j = preArgW 20 j := by decide
theorem pre_b28 : ∀ j < 20, stackArg (preState 28) j = preArgW 28 j := by decide
theorem pre_b32 : ∀ j < 20, stackArg (preState 32) j = preArgW 32 j := by decide
theorem pre_b48 : ∀ j < 20, stackArg (preState 48) j = preArgW 48 j := by decide
theorem pre_b64 : ∀ j < 20, stackArg (preState 64) j = preArgW 64 j := by decide

/-- The precondition, from the facts of a state. -/
theorem psign_pre_of {tsH tsG : List FnTable} {D : Nat} (hD : D ≤ 64) {s : State}
    (hg : s.gpr = (preState D).gpr) (ha : ∀ j < 20, stackArg s j = preArgW D j)
    (hrd : s.rd = (preState D).rd) (hwr : s.wr = (preState D).wr)
    (hH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : (tabFns tsH ++ tabFns tsG).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hd : Spec.RsaPss.digestLenOk 64 s.mem 0x300000 (BitVec.ofNat 64 D))
    (hK : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem 0x2000 64) (Spec.Rsa.bytesAt s.mem 0x4200 32)
      (Spec.Rsa.bytesAt s.mem 0x4300 32) = some (Spec.Rsa.wordsAt s.mem 0x4800 24)) :
    (pspec tsH tsG).pre s := by
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, signStack, stackArgs_twenty, List.append_eq, Sig.tableRegion]
  have hsp : s.gpr .rsp = 0x10000 := by rw [hg]; rfl
  have hD' : (BitVec.ofNat 64 D).toNat = D := by rw [BitVec.toNat_ofNat]; omega_using [hD]
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (8 * (j + 1)) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide),
    ha 16 (by decide), ha 17 (by decide), ha 18 (by decide), ha 19 (by decide), hg, hrd, hwr, hA, preArgW,
    preArgs, List.getD_cons_succ, List.getD_cons_zero]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, signStack, stackArgs_twenty, List.append_eq, Sig.tableRegion]
  sig_and_intros
  all_goals first
    | with_reducible exact hK
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact hH
    | exact hG
    | exact hsy
    | exact hd
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hD']; rfl)
    | (rw [hD']; apply Region.disjoint_of_sep; simp [Region.sep]; omega_using [hD])
    | (rw [hD']; simp; omega_using [hD])
    | (simp; omega)
    | skip

variable {vs : List MdHash}

theorem psign_sat_of {w : MdHash} (hw : w ∈ vs) (hl : (allNames vs).length < 2 ^ 32)
    {D : Nat} (hD : D ≤ 64) (hlen : w.mgf.G.len = D) (hb : ∀ j < 20, stackArg (preState D) j = preArgW D j) :
    (pspec (MdHashTable.X86_64.tables vs) (MdHashTable.X86_64.tables vs)).pre (withTabs (preState D) vs w) :=
  psign_pre_of hD rfl (fun j hj => (withTabs_arg _ vs w (pre_args D j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _ vs w⟩ ⟨_, List.mem_map_of_mem hw, withTabs_heldG _ vs w⟩
    (symsOf_distinct hl) (fun H hH => by
      have hA := MdHashTable.X86_64.hashAt_tableOf
        (MdHashTable.X86_64.held_tableOf (withTabs_heldH (preState D) vs w)).2.2.2.1
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hD]), hlen])
    (withTabs_key _ (preState_key D))

theorem preSat (hok : OK vs) : ∃ s, (pspec (MdHashTable.X86_64.tables vs) (MdHashTable.X86_64.tables vs)).pre s := by
  obtain ⟨w, hw, -⟩ := hok.2.2.2.1 0 (by decide)
  have hl := hok.2.2.2.2
  have hm := w.mgf.mem
  simp only [Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e
  · exact ⟨_, psign_sat_of hw hl (by decide) (by rw [e]; rfl) pre_b16⟩
  · exact ⟨_, psign_sat_of hw hl (by decide) (by rw [e]; rfl) pre_b20⟩
  · exact ⟨_, psign_sat_of hw hl (by decide) (by rw [e]; rfl) pre_b28⟩
  · exact ⟨_, psign_sat_of hw hl (by decide) (by rw [e]; rfl) pre_b32⟩
  · exact ⟨_, psign_sat_of hw hl (by decide) (by rw [e]; rfl) pre_b48⟩
  · exact ⟨_, psign_sat_of hw hl (by decide) (by rw [e]; rfl) pre_b64⟩
  · exact ⟨_, psign_sat_of hw hl (by decide) (by rw [e]; rfl) pre_b28⟩
  · exact ⟨_, psign_sat_of hw hl (by decide) (by rw [e]; rfl) pre_b32⟩


/-! ## The function, with the tables of `vs` -/

/-- `vg_rsa_pss_sign_precomputed`, with the tables of `vs`, calling
`vg_rsa_private_checked_precomputed` for the implementation `c` of the
CRT. -/
theorem signPrecomputed_ok (hok : OK vs) (c : CrtImpl) :
    Verified X86_64.target
      (signCP (MdHashTable.X86_64.fnsOf vs) (HashTable.X86_64.fnsOf vs) (privNameP c) (privCodeP c))
      (pspec (MdHashTable.X86_64.tables vs) (MdHashTable.X86_64.tables vs)) :=
  Verified.of_correct (k := psignK _ _)
    (signCP_correct (fun _ h => sgood_of hok h) (fun i hi => (enc_safe hok i hi).1)
      (fun i hi => (enc_safe hok i hi).2) c)
    (signCP_ct (fun _ h => sgood_of hok h) (fun i hi => (enc_safe hok i hi).1) (fun i hi => (enc_safe hok i hi).2) c
      (ckH Impl.Md5.X86_64.Stream.params 16))
    (psign_implies (preSat hok))

/-! ## Without secret residue -/

/-- `vg_rsa_pss_sign_precomputed`'s postcondition reads the memory on return
only in `out`. -/
theorem signPrecomputed_postOut (tsH tsG : List FnTable) :
    VG.X86_64.Scrub.PostOut (pspec tsH tsG) (Spec.RsaPss.signPrecomputedMdTableSig.retBits 64) :=
  VG.X86_64.Scrub.postOut_of_local_pre (leak := some _) (VG.X86_64.Scrub.ScrubAbi.plain.tables _ _)
    fun vs m m₁ m₂ r hlen hpre hb h => by
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 25) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨outLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
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
    obtain ⟨digest, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨digestLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨salt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨saltLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
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
    simp only [Spec.RsaPss.signPrecomputedMdTableSig, Sig.bufs, List.mem_cons, forall_eq_or_imp] at hb
    have hol : outLen.toNat = nLen.toNat := hpre.2.1
    have hby : Spec.Rsa.bytesAt m₂ out nLen.toNat = Spec.Rsa.bytesAt m₁ out nLen.toNat :=
      VG.Proof.Rsa.X86_64.bytesAt_agree (by simp only [Elem.size]; omega_using [hol])
        (by have := outLen.isLt; simp only [Elem.size]; omega_using []) hb.1
    intro H G hH hG
    have h' : Spec.Rsa.writtenOutcome m₁ out nLen.toNat r _ := h H G hH hG
    show Spec.Rsa.writtenOutcome m₂ out nLen.toNat r _
    revert h'
    generalize Spec.RsaPss.sign _ _ _ _ _ _ _ _ _ _ _ = o
    cases o <;> simp only [Spec.Rsa.writtenOutcome, hby] <;> exact id


end VG.Proof.RsaPss.X86_64
