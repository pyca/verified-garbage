module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86_64
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.TCB.Sig
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Weierstrass.TCombWords

/-!
# ECDSA verification over brainpoolP384r1 on x86-64: the contract the proof is written against

The facts of `Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP384r1.inst` for x86-64, under the
calling convention with the comb's tables (`Abi.withConsts brainpoolp384r1S.combConsts`),
by name: `vg_ecdsa_brainpoolp384r1_verify(public = rdi, digest = rsi, sig = rdx,
scratch = rcx)`, the result in `eax`, and the tables at the address of the
static `VG_BRAINPOOLP384R1_COMB` (`TblHeld`: held there, not wrapping around,
and apart from the regions written). Only the pointers and the tables'
address are public here: the proof shows that nothing else affects timing,
although the contract would let the contents of the three buffers.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.BrainpoolP384r1

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.X86_64 (brainpoolp384r1S brainpoolp384r1Comb)

/-- The words of the comb's tables. -/
abbrev bpW : List (BitVec 64) := brainpoolp384r1S.combWords brainpoolp384r1Comb

theorem bp_combConsts : brainpoolp384r1S.combConsts = [("VG_BRAINPOOLP384R1_COMB", bpW)] := rfl

/-- The comb's tables at the static `VG_BRAINPOOLP384R1_COMB`, held, not wrapping around,
and apart from the regions `wr`. -/
def TblHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < bpW.length, s.mem.readW (s.syms "VG_BRAINPOOLP384R1_COMB" + BitVec.ofNat 64 (8 * i)) 64 = bpW.getD i 0) ∧
  (s.syms "VG_BRAINPOOLP384R1_COMB").toNat + 8 * bpW.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms "VG_BRAINPOOLP384R1_COMB", 8 * bpW.length⟩ r

theorem bp_tbl_len : Impl.BrainpoolP384r1.comb7.length = 55 := by decide

theorem bp_tbl_lenH : ∀ j < 55, (Impl.BrainpoolP384r1.comb7.getD j []).length = 64 := by decide

/-- `bpW` has `55 · 64 · 12` words. -/
theorem bpW_length : bpW.length = 42240 :=
  (Proof.Weierstrass.tcombWords_length (n := brainpoolp384r1S.n) (R := brainpoolp384r1S.R) (p := brainpoolp384r1S.C.p)
    (H := 64) (tbl := Impl.BrainpoolP384r1.comb7) bp_tbl_len bp_tbl_lenH).trans rfl

theorem constRegions_single (f : String → BitVec 64) (n : String) (w : List (BitVec 64)) :
    Abi.constRegions f [(n, w)] = [⟨f n, 8 * w.length⟩] := rfl

/-- The tables' region, `8 · 42240` bytes at the static's address. The proofs
rewrite with this rather than unfold `Abi.constRegions`: the kernel evaluates
closed arithmetic such as `8 * bpW.length` when it compares two forms of
it, which would build the tables' 42240 words. -/
theorem bp_constRegions (f : String → BitVec 64) :
    Abi.constRegions f [("VG_BRAINPOOLP384R1_COMB", bpW)] = [⟨f "VG_BRAINPOOLP384R1_COMB", 337920⟩] := by
  rw [constRegions_single, bpW_length]

/-- The memory of the contracts' witnesses: the tables at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
tables). -/
@[irreducible] def satMem : Mem := constMem 0x100000 bpW

theorem satMem_held : ∀ i < bpW.length,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = bpW.getD i 0 := by
  unfold satMem
  exact constMem_held _ _ (by rw [bpW_length]; omega)

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.BrainpoolP384r1.curve (bytesAt m pk 97) (hashToInt Spec.BrainpoolP384r1.curve (bytesAt m digest 48)) (bytesAt m sig 96)

def verifyX86_64 : Contract X86_64.isa where
  pre s :=
    let pk : Region := ⟨s.gpr .rdi, 97⟩
    let digest : Region := ⟨s.gpr .rsi, 48⟩
    let sig : Region := ⟨s.gpr .rdx, 96⟩
    let scratch : Region := ⟨s.gpr .rcx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [pk, digest, sig, ⟨s.syms "VG_BRAINPOOLP384R1_COMB", 8 * bpW.length⟩] ∧ s.wr = [scratch] ∧
      pk.Disjoint scratch ∧ digest.Disjoint scratch ∧ sig.Disjoint scratch ∧ ret.Disjoint scratch ∧
      (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [scratch, ret]
  post s s' := (s'.gpr .rax).setWidth 32 = if vf s.mem (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) then 1 else 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.syms "VG_BRAINPOOLP384R1_COMB" = s₂.syms "VG_BRAINPOOLP384R1_COMB"

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x8000
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x1000, 97⟩, ⟨0x2000, 48⟩, ⟨0x3000, 96⟩, ⟨0x100000, 337920⟩]
  wr := [⟨0x8000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .rdi, 97⟩, ⟨s.gpr .rsi, 48⟩, ⟨s.gpr .rdx, 96⟩,
      ⟨s.syms "VG_BRAINPOOLP384R1_COMB", 8 * bpW.length⟩])
    (hw : s.wr = [⟨s.gpr .rcx, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .rdi, 97⟩ ⟨s.gpr .rcx, 8192⟩)
    (h2 : Region.Disjoint ⟨s.gpr .rsi, 48⟩ ⟨s.gpr .rcx, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .rdx, 96⟩ ⟨s.gpr .rcx, 8192⟩)
    (r1 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 97⟩) (r2 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 48⟩)
    (r3 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 96⟩) (r4 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, 8192⟩)
    (f0 : (s.gpr .rdi).toNat + 97 ≤ 2 ^ 64) (f1 : (s.gpr .rsi).toNat + 48 ≤ 2 ^ 64)
    (f2 : (s.gpr .rdx).toNat + 96 ≤ 2 ^ 64) (f3 : (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64)
    (ht : TblHeld s [⟨s.gpr .rcx, 8192⟩, ⟨s.gpr .rsp, 8⟩])
    (hal : (s.syms "VG_BRAINPOOLP384R1_COMB").toNat % 64 = 0) :
    (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP384r1.inst (X86_64.abi.withConsts brainpoolp384r1S.combConsts)).pre s := by
  sig_pre [Spec.Ecdsa.BrainpoolP384r1.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
    Spec.BrainpoolP384r1.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, bp_combConsts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr]),
    hdw _ (by simp), hal, by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, r4, f0, f1, f2, f3⟩

theorem sat_spec : (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP384r1.inst (X86_64.abi.withConsts brainpoolp384r1S.combConsts)).pre
    satState := by
  have hl := bpW_length
  have held : ∀ i < bpW.length, satState.mem.readW (satState.syms "VG_BRAINPOOLP384R1_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = bpW.getD i 0 := satMem_held
  refine spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (by decide) (by decide) (by decide) (by decide) ⟨held, ?_, ?_⟩ (by decide)
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies :
    verifyX86_64.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP384r1.inst (X86_64.abi.withConsts brainpoolp384r1S.combConsts)) where
  pre s h := by
    sig_pre [Spec.Ecdsa.BrainpoolP384r1.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
      Spec.BrainpoolP384r1.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, bp_combConsts,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, hdr, -, ht, hw, h1, h2, h3, -, -, -, r4, -, -, -, f4⟩ := h
    refine ⟨?_, hw, h1, h2, h3, r4, f4, hheld, hfit, fun r hr => ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdr
  post := by
    sig_implies_post [Spec.Ecdsa.BrainpoolP384r1.inst, Proof.Ecdsa.verifyContract,
      Proof.Ecdsa.verifySig, Spec.BrainpoolP384r1.curve, Spec.Ecdsa.scratchWords, X86_64.abi,
      X86_64.argRegs, bp_combConsts, Abi.withConsts, verifyX86_64, vf]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.BrainpoolP384r1.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
      Spec.BrainpoolP384r1.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, bp_combConsts,
      Abi.withConsts] at h
    obtain ⟨h0, hs, -, h1, h2, h3, h4⟩ := h
    exact ⟨h0, h1, h2, h3, h4, hs⟩
  sat := ⟨satState, sat_spec⟩

end VG.Proof.Ecdsa.Verify.X86_64.BrainpoolP384r1
