module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.ByRegister
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.PublicKeyCT
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.SignCT
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed25519.WholeLocal
import VerifiedGarbage.Proof.Ed25519.Expanded
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarBase
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Comb
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Whole
public import VerifiedGarbage.Spec.Ed25519.ExpandedKey
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
public import VerifiedGarbage.TCB.Artifact

/-!
# `vg_ed25519_public_key_expanded` and `vg_ed25519_sign_expanded` on RISC-V, verified

Each code meets its contract under `abi.withConsts combConsts` (the comb's
table, which `vg_ed25519_scalar_base` reads) with the frame (18 or 36
doublewords, so aligned as the contract's `u64` buffers are) as one more
argument (`Sig.scratchContract`) and 208 bytes of stack for the callees'
frames: the proof against the contract's facts by register (`pkCE`,
`signCE`: `pkRE`, `signRE` without the table, and what the table adds),
which it implies (`consts_implies`), and a state satisfying it, whose memory
holds a seed's digest at `0x2000`, its public key at `0x2100` (`satMemE`)
and the table at `0x100000` (`tblMem`). In its frame on the stack, which it
wipes before returning (`Verified.stackScratchWipedC`), it meets the
contract itself. Their contracts read the memory on return only at `out`
(`pkEPostOut_local`, `signEPostOut_local`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole
open VG.Spec.Ed25519 (bytesAt publicKeyExpandedSig signExpandedSig)
open VG.Impl.Ed25519.RISCV64 (combSym combWords combConsts)
open VG.Proof.Ed25519.RISCV64 (combWords_length)
open VG.Proof.Ed25519.WholeLocal (satSeed satKey bytesAt_congr)

/-! ## The contracts' conditions, and their locality -/

section
variable (pb : Nat)

/-- `publicKeyExpandedContract`'s precondition and postcondition. -/
def pkEPre : Curry (publicKeyExpandedSig.words pb) (Mem → Prop) :=
  fun _out expanded _scratch m =>
    ∃ seed : List Byte, seed.length = 32 ∧ bytesAt m expanded 64 = Spec.Sha512.sha512 seed

def pkEPost : publicKeyExpandedSig.Post pb :=
  fun out expanded _scratch m m' _ =>
    ∀ seed : List Byte, seed.length = 32 → bytesAt m expanded 64 = Spec.Sha512.sha512 seed →
      bytesAt m' out 32 = Spec.Ed25519.publicKey seed

theorem pkEPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (publicKeyExpandedSig.words pb).length →
    (∀ b ∈ Sig.bufs publicKeyExpandedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (publicKeyExpandedSig.words pb) (pkEPost pb) vs m m₁ r →
    Curry.apply (publicKeyExpandedSig.words pb) (pkEPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [o, ex, sc], _ =>
    simp only [publicKeyExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m ex 64 = Spec.Sha512.sha512 seed →
      bytesAt m₁ o 32 = Spec.Ed25519.publicKey seed at h
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m ex 64 = Spec.Sha512.sha512 seed →
      bytesAt m₂ o 32 = Spec.Ed25519.publicKey seed
    intro seed hl hs
    rw [bytesAt_congr hb.1]
    exact h seed hl hs

/-- `signExpandedContract`'s precondition and postcondition. -/
def signEPre : Curry (signExpandedSig.words pb) (Mem → Prop) :=
  fun _out expanded pk _message _len _scratch m =>
    ∃ seed : List Byte, seed.length = 32 ∧ bytesAt m expanded 64 = Spec.Sha512.sha512 seed ∧
      bytesAt m pk 32 = Spec.Ed25519.publicKey seed

def signEPost : signExpandedSig.Post pb :=
  fun out expanded _pk message len _scratch m m' _ =>
    ∀ seed : List Byte, seed.length = 32 → bytesAt m expanded 64 = Spec.Sha512.sha512 seed →
      bytesAt m' out 64 = Spec.Ed25519.sign seed (bytesAt m message len.toNat)

theorem signEPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (signExpandedSig.words pb).length →
    (∀ b ∈ Sig.bufs signExpandedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (signExpandedSig.words pb) (signEPost pb) vs m m₁ r →
    Curry.apply (signExpandedSig.words pb) (signEPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [o, ex, pk, msg, l, sc], _ =>
    simp only [signExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m ex 64 = Spec.Sha512.sha512 seed →
      bytesAt m₁ o 64 = Spec.Ed25519.sign seed (bytesAt m msg (l.setWidth pb).toNat) at h
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m ex 64 = Spec.Sha512.sha512 seed →
      bytesAt m₂ o 64 = Spec.Ed25519.sign seed (bytesAt m msg (l.setWidth pb).toNat)
    intro seed hl hs
    rw [bytesAt_congr hb.1]
    exact h seed hl hs

end

/-! ## A memory with a seed's digest and its public key -/

def satDigestE : List Byte := Spec.Sha512.sha512 satSeed

theorem satSeed_length : satSeed.length = 32 := by
  simp only [satSeed, bytesAt, List.length_map, List.length_range]

/-- The digest of `satSeed` at `0x2000` and its public key at `0x2100`. -/
def satMemE (a : Addr) : Byte :=
  if a.toNat < 0x2000 then 0
  else if a.toNat < 0x2100 then satDigestE[a.toNat - 0x2000]?.getD 0
  else satKey[a.toNat - 0x2100]?.getD 0

theorem sat_digestE : bytesAt satMemE 0x2000 64 = Spec.Sha512.sha512 satSeed := by
  apply List.ext_getElem
  · simp only [bytesAt, List.length_map, List.length_range, Proof.Ed25519.sha512_length]
  · intro i hi hj
    have hi' : i < 64 := by simpa only [bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
      change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
      omega
    simp only [bytesAt, List.getElem_map, List.getElem_range, satMemE, ha,
      show ¬ 0x2000 + i < 0x2000 from by omega, show 0x2000 + i < 0x2100 from by omega, ite_false, ite_true,
      Nat.add_sub_cancel_left, satDigestE, List.getElem?_eq_getElem hj, Option.getD_some]

theorem sat_keyE : bytesAt satMemE 0x2100 32 = satKey := by
  apply List.ext_getElem
  · simp only [bytesAt, List.length_map, List.length_range, Proof.Ed25519.WholeLocal.satKey_length]
  · intro i hi hj
    have hi' : i < 32 := by simpa only [bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x2100 : Addr) + BitVec.ofNat 64 i).toNat = 0x2100 + i := by
      change (0x2100 + i % 2 ^ 64) % 2 ^ 64 = 0x2100 + i
      omega
    simp only [bytesAt, List.getElem_map, List.getElem_range, satMemE, ha,
      show ¬ 0x2100 + i < 0x2000 from by omega, show ¬ 0x2100 + i < 0x2100 from by omega, ite_false,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

/-- The comb's table at `0x100000`. -/
@[irreducible] def tblMem : Mem := constMem 0x100000 combWords

theorem tblMem_held : ∀ i < combWords.length,
    tblMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  have h := constMem_held 0x100000 combWords (by rw [combWords_length]; decide)
  unfold tblMem
  exact h

/-- `satMemE` below `0x100000`, the comb's table above. -/
@[irreducible] def satMemTE : Mem := fun a => if a.toNat < 0x100000 then satMemE a else tblMem a

theorem satMemTE_held : ∀ i < combWords.length,
    satMemTE.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  intro i hi
  rw [combWords_length] at hi
  rw [← tblMem_held i (by rw [combWords_length]; exact hi)]
  refine Mem.readW_congr fun j hj => ?_
  have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat = 0x100000 + 8 * i + j := by
    rw [show (0x100000 : Addr) = BitVec.ofNat 64 0x100000 from rfl]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  simp only [satMemTE, e, show ¬ 0x100000 + 8 * i + j < 0x100000 by omega, ↓reduceIte]

theorem satMemTE_bytes {p : Addr} {n : Nat} (h : p.toNat + n ≤ 0x100000) :
    bytesAt satMemTE p n = bytesAt satMemE p n := by
  unfold bytesAt
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  have e : (p + BitVec.ofNat 64 i).toNat = p.toNat + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  simp only [satMemTE, e, show p.toNat + i < 0x100000 by omega, ↓reduceIte]

theorem satMemTE_pre : ∃ seed : List Byte, seed.length = 32 ∧
    bytesAt satMemTE 0x2000 64 = Spec.Sha512.sha512 seed ∧ bytesAt satMemTE 0x2100 32 = Spec.Ed25519.publicKey seed :=
  ⟨satSeed, satSeed_length, by rw [satMemTE_bytes (by decide), sat_digestE],
    by rw [satMemTE_bytes (by decide), sat_keyE]; rfl⟩

/-! ## `vg_ed25519_public_key_expanded` -/

/-- A state satisfying the precondition, with memory `m`, without the table. -/
def pkSatE (m : Mem) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x4000 | .a3 => 0x8000 | _ => 0
  sp := 0x10000
  mem := m
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8000, 144⟩]

theorem pkRE_implies : pkRE.Implies (Sig.scratchContract RISCV64.abi publicKeyExpandedSig "frame" .u64 18
    (pkEPre RISCV64.abi.ptrBits) (pkEPost RISCV64.abi.ptrBits) true 208) :=
    { pre := by
        sig_implies_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          publicKeyExpandedSig, Spec.Ed25519.scratchWords, pkEPre, pkEPost, pkRE, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          publicKeyExpandedSig, Spec.Ed25519.scratchWords, pkEPre, pkEPost, pkRE, RISCV64.abi,
          RISCV64.argRegs]
      pub := by
        sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          publicKeyExpandedSig, Spec.Ed25519.scratchWords, pkEPre, pkEPost, pkRE, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        obtain ⟨m, hm⟩ : ∃ m : Mem, ∃ seed : List Byte, seed.length = 32 ∧
            bytesAt m 0x2000 64 = Spec.Sha512.sha512 seed :=
          ⟨satMemE, satSeed, satSeed_length, sat_digestE⟩
        refine ⟨pkSatE m, ?_⟩
        sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          publicKeyExpandedSig, Spec.Ed25519.scratchWords, pkEPre, RISCV64.abi, RISCV64.argRegs, pkSatE]
        sig_and_intros
        all_goals first
          | exact hm
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide) }

/-- `pkSatE` with the table. -/
def pkSatCE : State :=
  { pkSatE satMemTE with rd := (pkSatE satMemTE).rd ++ [⟨0x100000, 49152⟩], syms := fun _ => 0x100000 }

theorem pkCE_sat : (Sig.scratchContract (RISCV64.abi.withConsts combConsts) publicKeyExpandedSig "frame" .u64 18
    (pkEPre RISCV64.abi.ptrBits) (pkEPost RISCV64.abi.ptrBits) true 208).pre pkSatCE := by
  have hl := combWords_length
  have held := satMemTE_held
  obtain ⟨seed, hsl, hm, -⟩ := satMemTE_pre
  change (Sig.scratchContract (RISCV64.abi.withConsts [(combSym, combWords)]) publicKeyExpandedSig "frame"
    .u64 18 (pkEPre RISCV64.abi.ptrBits) (pkEPost RISCV64.abi.ptrBits) true 208).pre pkSatCE
  generalize combWords = W' at hl held ⊢
  generalize e : pkSatCE = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    publicKeyExpandedSig, Spec.Ed25519.scratchWords, pkEPre,
    RISCV64.abi, RISCV64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact ⟨seed, hsl, hm⟩
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 32⟩ : Region), ⟨0x4000, 8192⟩, ⟨0x8000, 144⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem pkCE_implies : pkCE.Implies (Sig.scratchContract (RISCV64.abi.withConsts combConsts)
    publicKeyExpandedSig "frame" .u64 18 (pkEPre RISCV64.abi.ptrBits) (pkEPost RISCV64.abi.ptrBits) true 208) :=
  consts_implies (kR := pkRE) pkRE_implies (fun _ _ h => h) (fun _ _ h => h) ⟨pkSatCE, pkCE_sat⟩

theorem publicKeyExpanded_verified :
    Verified RISCV64.target publicKeyExpanded (Sig.scratchContract (RISCV64.abi.withConsts combConsts)
      publicKeyExpandedSig "frame" .u64 18 (pkEPre RISCV64.abi.ptrBits) (pkEPost RISCV64.abi.ptrBits) true 208) :=
  Verified.of_correct (pkE_ok base_ok) (publicKeyExpanded_ct fun _ _ _ _ ⟨⟨h0, h1, h2, h3, hsp⟩, hsy⟩ =>
    ⟨hsp, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption, hsy⟩) pkCE_implies

/-- A state satisfying `vg_ed25519_public_key_expanded`'s precondition, without the frame. -/
def pkFrameSatE : State := { pkSatCE with wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩] }

theorem pkFrameSatE_pre : ∃ s, (Spec.Ed25519.publicKeyExpandedContract (RISCV64.abi.withConsts combConsts)
    (208 + 144)).pre s := by
  refine ⟨pkFrameSatE, ?_⟩
  have hl := combWords_length
  have held := satMemTE_held
  obtain ⟨seed, hsl, hm, -⟩ := satMemTE_pre
  rw [show combConsts = [(combSym, combWords)] from rfl]
  generalize combWords = W' at hl held ⊢
  generalize e : pkFrameSatE = s
  sig_pre [Spec.Ed25519.publicKeyExpandedContract, publicKeyExpandedSig, Spec.Ed25519.scratchWords,
    RISCV64.abi, RISCV64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact ⟨seed, hsl, hm⟩
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 32⟩ : Region), ⟨0x4000, 8192⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

/-- In its frame of 144 bytes, whose first 136 it zeroes before returning. -/
theorem publicKeyExpanded_framed :
    Verified RISCV64.target publicKeyExpandedCode
      (Spec.Ed25519.publicKeyExpandedContract (RISCV64.abi.withConsts combConsts) (208 + 144)) :=
  Verified.stackScratchWipedC (sig := publicKeyExpandedSig) (nm := "frame") (e := .u64) (n := 18)
    (pre := pkEPre RISCV64.abi.ptrBits) (post := pkEPost RISCV64.abi.ptrBits) (wa := true) (stack := 208)
    (bytes := 144) (words := 17) publicKeyExpanded_verified (by decide) (by decide) (by decide)
    (pkEPostOut_local _) pkFrameSatE_pre

/-! ## `vg_ed25519_sign_expanded` -/

/-- A state satisfying the precondition, with memory `m`, without the table. -/
def signSatE (m : Mem) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x2100 | .a3 => 0x3000 | .a5 => 0x4000 | .a6 => 0x8000 | _ => 0
  sp := 0x10000
  mem := m
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 32⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8192⟩, ⟨0x8000, 288⟩]

theorem signRE_implies : signRE.Implies (Sig.scratchContract RISCV64.abi signExpandedSig "frame" .u64 36
    (signEPre RISCV64.abi.ptrBits) (signEPost RISCV64.abi.ptrBits) true 208) :=
    { pre := by
        sig_implies_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          signExpandedSig, Spec.Ed25519.scratchWords, signEPre, signEPost, signRE, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          signExpandedSig, Spec.Ed25519.scratchWords, signEPre, signEPost, signRE, RISCV64.abi,
          RISCV64.argRegs]
      pub := by
        sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          signExpandedSig, Spec.Ed25519.scratchWords, signEPre, signEPost, signRE, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        refine ⟨signSatE satMemTE, ?_⟩
        have hm := satMemTE_pre
        sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          signExpandedSig, Spec.Ed25519.scratchWords, signEPre, RISCV64.abi, RISCV64.argRegs, signSatE]
        sig_and_intros
        all_goals first
          | exact hm
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide) }

/-- `signSatE` with the table. -/
def signSatCE : State :=
  { signSatE satMemTE with rd := (signSatE satMemTE).rd ++ [⟨0x100000, 49152⟩], syms := fun _ => 0x100000 }

theorem signCE_sat : (Sig.scratchContract (RISCV64.abi.withConsts combConsts) signExpandedSig "frame" .u64 36
    (signEPre RISCV64.abi.ptrBits) (signEPost RISCV64.abi.ptrBits) true 208).pre signSatCE := by
  have hl := combWords_length
  have held := satMemTE_held
  have hm := satMemTE_pre
  change (Sig.scratchContract (RISCV64.abi.withConsts [(combSym, combWords)]) signExpandedSig "frame"
    .u64 36 (signEPre RISCV64.abi.ptrBits) (signEPost RISCV64.abi.ptrBits) true 208).pre signSatCE
  generalize combWords = W' at hl held ⊢
  generalize e : signSatCE = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    signExpandedSig, Spec.Ed25519.scratchWords, signEPre,
    RISCV64.abi, RISCV64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact hm
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 64⟩ : Region), ⟨0x4000, 8192⟩, ⟨0x8000, 288⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem signCE_implies : signCE.Implies (Sig.scratchContract (RISCV64.abi.withConsts combConsts)
    signExpandedSig "frame" .u64 36 (signEPre RISCV64.abi.ptrBits) (signEPost RISCV64.abi.ptrBits) true 208) :=
  consts_implies (kR := signRE) signRE_implies (fun _ _ h => h) (fun _ _ h => h) ⟨signSatCE, signCE_sat⟩

theorem signExpanded_verified :
    Verified RISCV64.target signExpanded (Sig.scratchContract (RISCV64.abi.withConsts combConsts)
      signExpandedSig "frame" .u64 36 (signEPre RISCV64.abi.ptrBits) (signEPost RISCV64.abi.ptrBits) true 208) :=
  Verified.of_correct (signE_ok base_ok) (signExpanded_ct fun _ _ _ _ ⟨⟨h0, h1, h2, h3, h4, h5, h6, hsp⟩, hsy⟩ =>
    ⟨hsp, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption, hsy⟩) signCE_implies

/-- A state satisfying `vg_ed25519_sign_expanded`'s precondition, without the frame. -/
def signFrameSatE : State := { signSatCE with wr := [⟨0x1000, 64⟩, ⟨0x4000, 8192⟩] }

theorem signFrameSatE_pre : ∃ s, (Spec.Ed25519.signExpandedContract (RISCV64.abi.withConsts combConsts)
    (208 + 288)).pre s := by
  refine ⟨signFrameSatE, ?_⟩
  have hl := combWords_length
  have held := satMemTE_held
  have hm := satMemTE_pre
  rw [show combConsts = [(combSym, combWords)] from rfl]
  generalize combWords = W' at hl held ⊢
  generalize e : signFrameSatE = s
  sig_pre [Spec.Ed25519.signExpandedContract, signExpandedSig, Spec.Ed25519.scratchWords, RISCV64.abi,
    RISCV64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact hm
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 64⟩ : Region), ⟨0x4000, 8192⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

/-- In its frame of 288 bytes, whose first 224 it zeroes before returning. -/
theorem signExpanded_framed :
    Verified RISCV64.target signExpandedCode
      (Spec.Ed25519.signExpandedContract (RISCV64.abi.withConsts combConsts) (208 + 288)) :=
  Verified.stackScratchWipedC (sig := signExpandedSig) (nm := "frame") (e := .u64) (n := 36)
    (pre := signEPre RISCV64.abi.ptrBits) (post := signEPost RISCV64.abi.ptrBits) (wa := true) (stack := 208)
    (bytes := 288) (words := 28) signExpanded_verified (by decide) (by decide) (by decide)
    (signEPostOut_local _) signFrameSatE_pre

end VG.Proof.Ed25519.RISCV64.Whole
