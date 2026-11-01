module

import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFn
public import VerifiedGarbage.Proof.Framework.Inline

/-!
# Montgomery multiplication on PPC64LE: the shared contract

`mul` is proven against `fnContract`, with the scratch buffer where it saves
the nonvolatile registers as a sixth argument; that is `mulContract` with
the buffer appended (`scratch_verified`), and `withStackScratch` allocates
the buffer in a frame of its own (`mul_verified`), as the contract's
precondition, postcondition and leak read memory only within the working
space when the precondition holds (`pre_local`, `post_local`, `leak_local`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE VG.Impl.Bignum
open VG.Proof.Rsa.Mont (numAt wOf wordAt Layout Operand Keeps arrAt aM minvWord)

/-- `mulContract`'s precondition. -/
def mulPre : Curry (Proof.Rsa.Mont.sig.words abi.ptrBits) (Mem → Prop) := fun ws wsLen o a b m =>
  let w := wOf m ws
  Layout m ws wsLen.toNat ∧ Operand o.toNat ∧ Operand a.toNat ∧ Operand b.toNat ∧
    ((m.readW (ws + BitVec.ofNat 64 (arrAt w aM)) 64).toNat * (wordAt m ws minvWord).toNat + 1) %
      2 ^ 64 = 0 ∧
    numAt m ws w b.toNat < numAt m ws w aM

/-- `mulContract`'s postcondition. -/
def mulPost : Proof.Rsa.Mont.sig.Post abi.ptrBits := fun ws wsLen o a b m m' _ =>
  let w := wOf m ws
  let M := numAt m ws w aM
  numAt m' ws w o.toNat < M ∧
    numAt m' ws w o.toNat * 2 ^ (64 * w) % M = numAt m ws w a.toNat * numAt m ws w b.toNat % M ∧
    Keeps ws wsLen.toNat w o.toNat m m'

/-- `mulContract`'s leak. -/
def mulLeak : Curry (Proof.Rsa.Mont.sig.words abi.ptrBits) (Mem → List Nat) :=
  fun ws _ _ _ _ m => [wOf m ws]

theorem mulContract_eq (stack : Nat) :
    Proof.Rsa.Mont.mulContract abi stack =
      Proof.Rsa.Mont.sig.contract abi mulPre mulPost false stack (some mulLeak) := rfl

/-- `mulContract` with the 72-byte scratch buffer as a sixth argument. -/
abbrev scratchContract : Contract isa :=
  Sig.scratchContract abi Proof.Rsa.Mont.sig "scratch" .u64 9 mulPre mulPost false 0 (some mulLeak)

/-! ## Satisfiability -/

/-- The words of a working space of `w = 2` at `0x1000`: the header, then the
modulus 1 in array 0 and zeros. -/
def satWord (k : Nat) : BitVec 64 :=
  if k = 6 then 2 else if k = 7 then 0xFFFFFFFFFFFFFFFF
  else if 8 ≤ k ∧ k < 16 then BitVec.ofNat 64 (0x1100 + (k - 8) * 32)
  else if k = 32 then 1 else 0

def satMem : Mem := fun x =>
  let i := (x - 0x1000).toNat
  if i < 512 then (satWord (i / 8)).extractLsb' (8 * (i % 8)) 8 else 0

/-- A state meeting `scratchContract`: `w = 2`, the working space at
`0x1000`, `o = a = b = 1`, the scratch buffer at `0x2000`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 1 | .r6 => 1 | .r7 => 1 | .r8 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem := satMem
  rd := []
  wr := [⟨0x1000, 512⟩, ⟨0x2000, 72⟩]

/-- `satState` without the scratch buffer: a state meeting `mulContract`. -/
def satState₀ : State := { satState with wr := [⟨0x1000, 512⟩] }

theorem fn_implies : fnContract.Implies scratchContract where
  pre := by
    sig_implies_pre [scratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Proof.Rsa.Mont.sig, mulPre, mulPost, mulLeak, fnContract, abi, argRegs]
  post := by
    sig_implies_post [scratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Proof.Rsa.Mont.sig, mulPre, mulPost, mulLeak, fnContract, abi, argRegs]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [scratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Proof.Rsa.Mont.sig, mulPre, mulPost, mulLeak, fnContract, abi, argRegs] at h
    obtain ⟨hsp, hw, hdi, hsi, hdx, hcx, h8, h9⟩ := h
    exact ⟨hsp, hdi, hsi, hdx, hcx, h8, h9, List.singleton_inj.mp hw⟩
  sat := by
    sig_implies_sat [scratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Proof.Rsa.Mont.sig, mulPre, mulPost, mulLeak, abi, argRegs] [satState] using satState

theorem scratch_verified : Verified target mul scratchContract :=
  Verified.of_correct fn_correct fn_ct fn_implies

/-! ## Reading memory within the working space -/

theorem agree_read {m₁ m₂ : Mem} {ws : Addr} {L d k : Nat}
    (h : ∀ a, (⟨ws, L⟩ : Region).Contains a 1 → m₁ a = m₂ a) (hk : d + k ≤ L) (hk' : d + k < 2 ^ 64) :
    m₁.read (ws + BitVec.ofNat 64 d) k = m₂.read (ws + BitVec.ofNat 64 d) k :=
  Mem.read_congr fun i hi => h _ (by
    simp only [Region.Contains]
    rw [Offset.add_add, Mem.sub_ofNat_toNat _ (by omega_arith)]
    omega_arith)

theorem agree_readW {m₁ m₂ : Mem} {ws : Addr} {L d : Nat}
    (h : ∀ a, (⟨ws, L⟩ : Region).Contains a 1 → m₁ a = m₂ a) (hk : d + 8 ≤ L) (hk' : d + 8 < 2 ^ 64) :
    m₁.readW (ws + BitVec.ofNat 64 d) 64 = m₂.readW (ws + BitVec.ofNat 64 d) 64 := by
  simp only [Mem.readW, agree_read h hk hk']

/-- What the reads of the contract see agrees, within a working space that
the layout of `m₂` fills. -/
structure Same (ws : Addr) (L : Nat) (m₁ m₂ : Mem) : Prop where
  w : wOf m₁ ws = wOf m₂ ws
  word : ∀ i < 16, wordAt m₁ ws i = wordAt m₂ ws i
  num : ∀ j < 8, numAt m₁ ws (wOf m₂ ws) j = numAt m₂ ws (wOf m₂ ws) j
  m0 : m₁.readW (ws + BitVec.ofNat 64 (arrAt (wOf m₂ ws) aM)) 64 =
    m₂.readW (ws + BitVec.ofNat 64 (arrAt (wOf m₂ ws) aM)) 64
  byte : ∀ i < L, m₁ (ws + BitVec.ofNat 64 i) = m₂ (ws + BitVec.ofNat 64 i)

theorem same_of {m₁ m₂ : Mem} {ws : Addr} {L : Nat}
    (h : ∀ a, (⟨ws, L⟩ : Region).Contains a 1 → m₁ a = m₂ a) (hl : Layout m₂ ws (L / 8)) :
    Same ws L m₁ m₂ := by
  obtain ⟨h2, h31, h8, -⟩ := hl
  have h8' : arrAt (wOf m₂ ws) 8 ≤ L := by omega_arith
  have hz : arrAt (wOf m₂ ws) 8 < 2 ^ 64 := by unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  have hd : ∀ j < 8, arrAt (wOf m₂ ws) j + 8 * (wOf m₂ ws) ≤ arrAt (wOf m₂ ws) 8 := fun j hj => by
    unfold arrAt
    have := Nat.mul_le_mul_right (8 * (wOf m₂ ws + 2)) (show j + 1 ≤ 8 by omega_arith)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega_arith
  have hword : ∀ i < 16, wordAt m₁ ws i = wordAt m₂ ws i := fun i hi =>
    agree_readW h (by unfold arrAt Proof.Rsa.Mont.hdrBytes at h8'; omega_arith) (by omega_arith)
  have h0 := hd aM (by decide)
  refine ⟨?_, hword, fun j hj => ?_, agree_readW h (by omega_arith) (by omega_arith), fun i hi => h _ ?_⟩
  · simp only [wOf, Proof.Rsa.Mont.wWord, hword 6 (by decide)]
  · simp only [numAt]
    rw [agree_read h (by have := hd j hj; omega_arith) (by have := hd j hj; omega_arith)]
  · simp only [Region.Contains]
    have : (ws + BitVec.ofNat 64 i - ws).toNat ≤ i := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]; exact Nat.mod_le _ _
    omega_arith

/-- The contract's arguments, as `Curry.apply` passes them. -/
theorem words_eq : Proof.Rsa.Mont.sig.words abi.ptrBits = [.addr, .int 64, .int 32, .int 32, .int 32] := rfl

theorem pre_local : ∀ vs m₁ m₂, vs.length = (Proof.Rsa.Mont.sig.words abi.ptrBits).length →
    (∀ b ∈ Sig.bufs Proof.Rsa.Mont.sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Proof.Rsa.Mont.sig.words abi.ptrBits) mulPre vs m₁ →
      Curry.apply (Proof.Rsa.Mont.sig.words abi.ptrBits) mulPre vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  rw [words_eq] at hlen
  match vs, hlen with
  | [ws, l, o, a, b], _ =>
  simp only [Proof.Rsa.Mont.sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    Elem.size] at hb
  change Curry.apply [ArgWord.addr, .int 64, .int 32, .int 32, .int 32] mulPre _ m₁ at h
  change Curry.apply [ArgWord.addr, .int 64, .int 32, .int 32, .int 32] mulPre _ m₂
  dsimp only [Curry.apply, mulPre, ArgWord.ofRaw] at h ⊢
  simp only [BitVec.setWidth_eq] at h ⊢
  obtain ⟨hl, ho, ha, hb', hinv, hB⟩ := h
  have hl' : Layout m₁ ws (l.toNat * 8 / 8) := by rw [Nat.mul_div_cancel _ (by decide)]; exact hl
  have hS := same_of (fun x hx => (hb x hx).symm) (m₁ := m₂) (m₂ := m₁) hl'
  obtain ⟨h2, h31, h8, harr⟩ := hl
  refine ⟨⟨by rw [hS.w]; exact h2, by rw [hS.w]; exact h31, by rw [hS.w]; exact h8, fun j hj => by
    rw [hS.word _ (by unfold Proof.Rsa.Mont.arrWord; omega_arith), hS.w]; exact harr j hj⟩,
    ho, ha, hb', ?_, ?_⟩
  · rw [hS.w, hS.m0, hS.word _ (by decide)]; exact hinv
  · rw [hS.w, hS.num _ hb'.1, hS.num _ (by decide)]; exact hB

theorem post_local : ∀ vs m₁ m₂ m' r, vs.length = (Proof.Rsa.Mont.sig.words abi.ptrBits).length →
    Curry.apply (Proof.Rsa.Mont.sig.words abi.ptrBits) mulPre vs m₂ →
    (∀ b ∈ Sig.bufs Proof.Rsa.Mont.sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Proof.Rsa.Mont.sig.words abi.ptrBits) mulPost vs m₁ m' r →
      Curry.apply (Proof.Rsa.Mont.sig.words abi.ptrBits) mulPost vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hp hb h
  rw [words_eq] at hlen
  match vs, hlen with
  | [ws, l, o, a, b], _ =>
  simp only [Proof.Rsa.Mont.sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    Elem.size] at hb
  change Curry.apply [ArgWord.addr, .int 64, .int 32, .int 32, .int 32] mulPre _ m₂ at hp
  change Curry.apply [ArgWord.addr, .int 64, .int 32, .int 32, .int 32] mulPost _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, .int 64, .int 32, .int 32, .int 32] mulPost _ m₂ m' r
  dsimp only [Curry.apply, mulPre, mulPost, ArgWord.ofRaw] at hp h ⊢
  simp only [BitVec.setWidth_eq] at hp h ⊢
  obtain ⟨hl, -, ⟨ha, -⟩, ⟨hb', -⟩, -⟩ := hp
  have hS := same_of hb (by rw [Nat.mul_div_cancel _ (by decide)]; exact hl)
  obtain ⟨hlt, heq, hk⟩ := h
  rw [hS.w, hS.num _ (by decide), hS.num _ ha, hS.num _ hb'] at *
  refine ⟨hlt, heq, fun i hi hj => ?_⟩
  rw [hk i hi hj, hS.byte i (by rw [Nat.mul_comm]; exact hi)]

theorem leak_local : ∀ f, some mulLeak = some f → ∀ vs m₁ m₂,
    vs.length = (Proof.Rsa.Mont.sig.words abi.ptrBits).length →
    Curry.apply (Proof.Rsa.Mont.sig.words abi.ptrBits) mulPre vs m₂ →
    (∀ b ∈ Sig.bufs Proof.Rsa.Mont.sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply _ f vs m₁ = Curry.apply _ f vs m₂ := by
  intro f hf vs m₁ m₂ hlen hp hb
  cases hf
  rw [words_eq] at hlen
  match vs, hlen with
  | [ws, l, o, a, b], _ =>
  simp only [Proof.Rsa.Mont.sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    Elem.size] at hb
  change Curry.apply [ArgWord.addr, .int 64, .int 32, .int 32, .int 32] mulPre _ m₂ at hp
  change Curry.apply [ArgWord.addr, .int 64, .int 32, .int 32, .int 32] mulLeak _ m₁ =
    Curry.apply [ArgWord.addr, .int 64, .int 32, .int 32, .int 32] mulLeak _ m₂
  dsimp only [Curry.apply, mulPre, mulLeak, ArgWord.ofRaw] at hp ⊢
  simp only [BitVec.setWidth_eq] at hp
  rw [(same_of hb (by rw [Nat.mul_div_cancel _ (by decide)]; exact hp.1)).w]

/-- `vg_rsa_mont_mul` with its scratch buffer in a frame of 112 bytes. -/
theorem mul_verified : Verified target (Impl.StackScratch.PPC64LE.withStackScratch 112 .r8 mul)
    (Proof.Rsa.Mont.mulContract abi 112) :=
  Verified.stackScratchL (sig := Proof.Rsa.Mont.sig) (nm := "scratch") (e := .u64) (n := 9)
    (post := mulPost) (wa := false) (stack := 0) (bytes := 112) scratch_verified (by decide)
    (by decide) pre_local post_local leak_local
    (by sig_implies_sat [Proof.Rsa.Mont.sig, mulPre, mulPost, mulLeak, abi, argRegs] [satState₀]
      using satState₀)

end VG.Proof.Bignum.PPC64LE
