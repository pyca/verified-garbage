module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.PublicKey
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed25519.WholeLocal
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Comb
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.PublicKey
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Ed25519.WholeLocal
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Whole
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Spec.Ed25519.ExpandedKey
import VerifiedGarbage.Proof.Ed25519.Expanded
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Impl.Ed25519.PPC64LE.Comb
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts

/-!
# `vg_ed25519_public_key_expanded` on PPC64LE, with its frame as an argument, verified

The code meets `publicKeyExpandedContract` under `abi.withConsts combConsts`
(the comb's table, which `vg_ed25519_scalar_base` reads) with the frame as one
more argument (`Sig.scratchContract`), and 48 bytes of stack for the callees'
frames: the proof against the contract's facts by register (`pkCE`: `pkRE`
without the table, and what the table adds), which it implies
(`consts_implies`), and a state satisfying it, with the table at `0x100000`
(`tblMem`) and the digest at `r4` at `0x2000` (`satMemE`, which also holds the
seed's public key, for signing); and, in its frame, the contract itself
(`publicKeyExpanded_framed`). Only the pointers and the table's address are
public: the pointers stay in `r20`–`r23`, which no function called writes, so
the taint analysis (`taint_decide`, under `vectorTaintSym`) sees them public
throughout, callees included.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole
open VG.Spec.Ed25519 (bytesAt)
open VG.Impl.Ed25519.PPC64LE (combSym combWords combConsts)
open VG.Proof.Ed25519.PPC64LE (combWords_length TBL tbl_of_consts rd_of_consts consts_implies base_ok)

/-- The stack the contract reserves. -/
theorem below_reserved (s : State) : below s.sp 48 ∈ PPC64LE.abi.reserved 48 s := by
  show _ ∈ stackBelow s.sp 48
  rw [stackBelow_pos _ (by decide)]; simp

/-- The comb's table at `0x100000`. -/
@[irreducible] def tblMem : Mem := constMem 0x100000 combWords

theorem tblMem_held : ∀ i < combWords.length,
    tblMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  have h := constMem_held 0x100000 combWords (by rw [combWords_length]; decide)
  unfold tblMem
  exact h

/-- The contract by register: `out` in `r3`, the seed's digest at `r4`, `scratch` in `r5`, the
frame in `r6`; without the comb's table. -/
def pkRE : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 32⟩
    let dg : Region := ⟨s.gpr .r4, 64⟩
    let sc : Region := ⟨s.gpr .r5, 8192⟩
    let fr : Region := ⟨s.gpr .r6, 144⟩
    s.rd = [dg] ∧ s.wr = [out, sc, fr] ∧ out.Disjoint dg ∧ out.Disjoint sc ∧ out.Disjoint fr ∧
      dg.Disjoint sc ∧ dg.Disjoint fr ∧ sc.Disjoint fr ∧ 48 ≤ s.sp.toNat ∧
      (below s.sp 48).Disjoint out ∧ (below s.sp 48).Disjoint dg ∧ (below s.sp 48).Disjoint sc ∧
      (below s.sp 48).Disjoint fr ∧
      ∃ seed : List Byte, seed.length = 32 ∧ bytesAt s.mem (s.gpr .r4) 64 = Spec.Sha512.sha512 seed
  post s s' := ∀ seed : List Byte, seed.length = 32 → bytesAt s.mem (s.gpr .r4) 64 = Spec.Sha512.sha512 seed →
    bytesAt s'.mem (s.gpr .r3) 32 = Spec.Ed25519.publicKey seed
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

/-- `pkRE` with the comb's table (`abi.withConsts`): `pkRE` for the state without it, and what the
table adds. -/
def pkCE : Contract isa where
  pre s := pkRE.pre (stripConsts combConsts s) ∧ ConstsOk combConsts 48 s
  post := pkRE.post
  pub s₁ s₂ := pkRE.pub s₁ s₂ ∧ s₁.syms combSym = s₂.syms combSym

theorem pkE_ok (B : BaseOk) (s : State) (hs : pkCE.pre s) :
    ∃ t s', Exec isa publicKeyExpanded s t s' ∧ abiPreserved s s' ∧ pkCE.post s s' := by
  obtain ⟨⟨a, b, c, d, e, f, g, h, i, j, k, l, m, seed, -, hsd⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp, stripConsts_mem] at *
  obtain ⟨-, tfit, words, twr, tres⟩ := tbl_of_consts hk
  have hrd : s.rd = [⟨s.gpr .r4, 64⟩, TBL (s.syms combSym)] := rd_of_consts hk a
  have tW : ∀ r ∈ pkW s, (TBL (s.syms combSym)).Disjoint r := fun r hr => by
    simp only [pkW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact tres _ (below_reserved s)
  obtain ⟨t, s', he, hg, hsp, hlr, hq⟩ :=
    publicKeyExpanded_wp B ⟨hrd, b, c, d, e, f, g, h, i, j, k, l, m, tfit, words, tW⟩ hsd
  refine ⟨t, s', he, ⟨hg, hsp, hlr⟩, fun seed' _ hs' => ?_⟩
  rw [hq]
  exact Proof.Ed25519.publicKey_of_sha512_eq (hsd.symm.trans hs')

theorem pkE_ct : ConstantTime isa pkCE.pre pkCE.pub publicKeyExpanded :=
  VG.Taint.constantTime (A := vectorTaintSym [combSym]) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun s₁ s₂ _ _ ⟨⟨p3, p4, p5, p6, psp⟩, hsy⟩ => ⟨⟨psp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption⟩, fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

/-- `publicKeyExpandedContract`'s precondition and postcondition. -/
def pkEPre (pb : Nat) : Curry (Spec.Ed25519.publicKeyExpandedSig.words pb) (Mem → Prop) :=
  fun _out expanded _scratch m =>
    ∃ seed : List Byte, seed.length = 32 ∧ bytesAt m expanded 64 = Spec.Sha512.sha512 seed

def pkEPost (pb : Nat) : Spec.Ed25519.publicKeyExpandedSig.Post pb :=
  fun out expanded _scratch m m' _ =>
    ∀ seed : List Byte, seed.length = 32 → bytesAt m expanded 64 = Spec.Sha512.sha512 seed →
      bytesAt m' out 32 = Spec.Ed25519.publicKey seed

theorem pkEPre_local (pb : Nat) : ∀ vs m₁ m₂, vs.length = (Spec.Ed25519.publicKeyExpandedSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Ed25519.publicKeyExpandedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Ed25519.publicKeyExpandedSig.words pb) (pkEPre pb) vs m₁ →
    Curry.apply (Spec.Ed25519.publicKeyExpandedSig.words pb) (pkEPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  match vs, hlen with
  | [o, dg, sc], _ =>
    simp only [Spec.Ed25519.publicKeyExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change ∃ seed : List Byte, seed.length = 32 ∧ bytesAt m₁ dg 64 = Spec.Sha512.sha512 seed at h
    change ∃ seed : List Byte, seed.length = 32 ∧ bytesAt m₂ dg 64 = Spec.Sha512.sha512 seed
    rw [Proof.Ed25519.WholeLocal.bytesAt_congr hb.2.1]
    exact h

theorem pkEPost_local (pb : Nat) : ∀ vs m₁ m₂ m' r, vs.length = (Spec.Ed25519.publicKeyExpandedSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Ed25519.publicKeyExpandedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Ed25519.publicKeyExpandedSig.words pb) (pkEPost pb) vs m₁ m' r →
    Curry.apply (Spec.Ed25519.publicKeyExpandedSig.words pb) (pkEPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  match vs, hlen with
  | [o, dg, sc], _ =>
    simp only [Spec.Ed25519.publicKeyExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m₁ dg 64 = Spec.Sha512.sha512 seed →
      bytesAt m' o 32 = Spec.Ed25519.publicKey seed at h
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m₂ dg 64 = Spec.Sha512.sha512 seed →
      bytesAt m' o 32 = Spec.Ed25519.publicKey seed
    rw [Proof.Ed25519.WholeLocal.bytesAt_congr hb.2.1]
    exact h

theorem pkEPostOut_local (pb : Nat) : ∀ vs m m₁ m₂ r,
    vs.length = (Spec.Ed25519.publicKeyExpandedSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Ed25519.publicKeyExpandedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Ed25519.publicKeyExpandedSig.words pb) (pkEPost pb) vs m m₁ r →
    Curry.apply (Spec.Ed25519.publicKeyExpandedSig.words pb) (pkEPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [o, dg, sc], _ =>
    simp only [Spec.Ed25519.publicKeyExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m dg 64 = Spec.Sha512.sha512 seed →
      bytesAt m₁ o 32 = Spec.Ed25519.publicKey seed at h
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m dg 64 = Spec.Sha512.sha512 seed →
      bytesAt m₂ o 32 = Spec.Ed25519.publicKey seed
    rw [Proof.Ed25519.WholeLocal.bytesAt_congr hb.1]
    exact h

/-! ### A memory with a seed's digest and public key

The digest of `WholeLocal.satSeed` at `0x2000`, its public key at `0x2100`. -/

theorem satSeed_length : Proof.Ed25519.WholeLocal.satSeed.length = 32 := by
  simp only [Proof.Ed25519.WholeLocal.satSeed, bytesAt, List.length_map, List.length_range]

def satDigestE : List Byte := Spec.Sha512.sha512 Proof.Ed25519.WholeLocal.satSeed

def satMemE (a : Addr) : Byte :=
  if a.toNat < 0x2000 then 0
  else if a.toNat < 0x2100 then satDigestE[a.toNat - 0x2000]?.getD 0
  else Proof.Ed25519.WholeLocal.satKey[a.toNat - 0x2100]?.getD 0

theorem sat_digestE : bytesAt satMemE 0x2000 64 = satDigestE := by
  apply List.ext_getElem
  · simp only [bytesAt, List.length_map, List.length_range, satDigestE, Proof.Ed25519.sha512_length]
  · intro i hi hj
    have hi' : i < 64 := by simpa only [bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
      change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
      omega
    simp only [bytesAt, List.getElem_map, List.getElem_range, satMemE, ha,
      show ¬ 0x2000 + i < 0x2000 from by omega, show 0x2000 + i < 0x2100 from by omega, ite_false, ite_true,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

theorem sat_keyE : bytesAt satMemE 0x2100 32 = Proof.Ed25519.WholeLocal.satKey := by
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

theorem satMemTE_digest : bytesAt satMemTE 0x2000 64 = Spec.Sha512.sha512 Proof.Ed25519.WholeLocal.satSeed := by
  rw [satMemTE_bytes (by decide), sat_digestE]; rfl

/-! ### The contract -/

/-- A state satisfying the precondition, without the table. -/
def pkSatE : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x4000 | .r6 => 0x8000 | _ => 0
  lr := 0
  sp := 0x10000
  mem := satMemE
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8000, 144⟩]

theorem pkRE_implies : pkRE.Implies (Sig.scratchContract PPC64LE.abi Spec.Ed25519.publicKeyExpandedSig "frame"
    .u8 144 (pkEPre PPC64LE.abi.ptrBits) (pkEPost PPC64LE.abi.ptrBits) true 48) :=
    { pre := by
        sig_implies_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.publicKeyExpandedSig, Spec.Ed25519.scratchWords, pkEPre, pkEPost, pkRE, PPC64LE.abi,
          PPC64LE.argRegs]
      post := by
        sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.publicKeyExpandedSig, Spec.Ed25519.scratchWords, pkEPre, pkEPost, pkRE, PPC64LE.abi,
          PPC64LE.argRegs]
      pub := by
        sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.publicKeyExpandedSig, Spec.Ed25519.scratchWords, pkEPre, pkEPost, pkRE, PPC64LE.abi,
          PPC64LE.argRegs]
      sat := by
        have hd : bytesAt satMemE 0x2000 64 = Spec.Sha512.sha512 Proof.Ed25519.WholeLocal.satSeed := sat_digestE
        refine ⟨pkSatE, ?_⟩
        sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.publicKeyExpandedSig, Spec.Ed25519.scratchWords, pkEPre, PPC64LE.abi, PPC64LE.argRegs,
          pkSatE]
        sig_and_intros
        all_goals first
          | exact ⟨_, satSeed_length, hd⟩
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide) }

/-- `pkSatE` with the table. -/
def pkSatCE : State :=
  { pkSatE with mem := satMemTE, rd := pkSatE.rd ++ [⟨0x100000, 49152⟩], syms := fun _ => 0x100000 }

theorem pkCE_sat : (Sig.scratchContract (PPC64LE.abi.withConsts combConsts) Spec.Ed25519.publicKeyExpandedSig
    "frame" .u8 144 (pkEPre PPC64LE.abi.ptrBits) (pkEPost PPC64LE.abi.ptrBits) true 48).pre pkSatCE := by
  have hl := combWords_length
  have held := satMemTE_held
  have hd := satMemTE_digest
  rw [show combConsts = [(combSym, combWords)] from rfl]
  generalize combWords = W' at hl held ⊢
  generalize e : pkSatCE = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed25519.publicKeyExpandedSig,
    Spec.Ed25519.scratchWords, pkEPre, PPC64LE.abi, PPC64LE.argRegs, Abi.withConsts, Abi.constRegions,
    Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact ⟨_, satSeed_length, hd⟩
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 32⟩ : Region), ⟨0x4000, 8192⟩, ⟨0x8000, 144⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem pkCE_implies : pkCE.Implies (Sig.scratchContract (PPC64LE.abi.withConsts combConsts)
    Spec.Ed25519.publicKeyExpandedSig "frame" .u8 144 (pkEPre PPC64LE.abi.ptrBits) (pkEPost PPC64LE.abi.ptrBits)
    true 48) :=
  consts_implies (kR := pkRE) pkRE_implies (fun _ _ h => h) (fun _ _ h => h) ⟨pkSatCE, pkCE_sat⟩

theorem publicKeyExpanded_verified :
    Verified PPC64LE.target publicKeyExpanded (Sig.scratchContract (PPC64LE.abi.withConsts combConsts)
      Spec.Ed25519.publicKeyExpandedSig "frame" .u8 144 (pkEPre PPC64LE.abi.ptrBits) (pkEPost PPC64LE.abi.ptrBits)
      true 48) :=
  Verified.of_correct (pkE_ok base_ok) pkE_ct pkCE_implies

/-- A state satisfying `vg_ed25519_public_key_expanded`'s precondition, without the frame. -/
def pkFrameSatE : State := { pkSatCE with wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩] }

theorem pkFrameSatE_pre : ∃ s, (Spec.Ed25519.publicKeyExpandedContract (PPC64LE.abi.withConsts combConsts)
    (48 + 176)).pre s := by
  refine ⟨pkFrameSatE, ?_⟩
  have hl := combWords_length
  have held := satMemTE_held
  have hd := satMemTE_digest
  rw [show combConsts = [(combSym, combWords)] from rfl]
  generalize combWords = W' at hl held ⊢
  generalize e : pkFrameSatE = s
  sig_pre [Spec.Ed25519.publicKeyExpandedContract, Spec.Ed25519.publicKeyExpandedSig, Spec.Ed25519.scratchWords,
    PPC64LE.abi, PPC64LE.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact ⟨_, satSeed_length, hd⟩
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 32⟩ : Region), ⟨0x4000, 8192⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

/-- In its frame of 176 bytes, whose first 136 it zeroes before returning. -/
theorem publicKeyExpanded_framed :
    Verified PPC64LE.target publicKeyExpandedCode
      (Spec.Ed25519.publicKeyExpandedContract (PPC64LE.abi.withConsts combConsts) (48 + 176)) :=
  Verified.stackScratchWipedC (c₀ := (combSym, combWords)) (cs := []) (sig := Spec.Ed25519.publicKeyExpandedSig)
    (nm := "frame") (e := .u8) (n := 144) (pre := pkEPre PPC64LE.abi.ptrBits)
    (post := pkEPost PPC64LE.abi.ptrBits) (wa := true) (stack := 48) (bytes := 176)
    (words := 17) publicKeyExpanded_verified (by decide) (by decide) (by decide)
    (pkEPre_local _) (pkEPost_local _) (pkEPostOut_local _) pkFrameSatE_pre

end VG.Proof.Ed25519.PPC64LE.Whole
