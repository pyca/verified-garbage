module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Impl.Secp256k1.GTable9

import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Ecdsa.X86_64.Tables
/-!
# ECDSA verification over secp256k1 on x86-64: the contract the proof is written against

The facts of `Spec.Ecdsa.Secp256k1.inst.verifyContract` for x86-64, under the
calling convention with the verifier's table of the generator's multiples
(`Abi.withConsts secp256k1v.combConsts`),
by name: `vg_ecdsa_secp256k1_verify(public = rdi, digest = rsi, sig = rdx,
scratch = rcx)`, the result in `eax`, and the table at the address of the
static `VG_SECP256K1_GTAB`. This adapter supplies the correctness precondition and
postcondition. The timing proof uses the shared contract directly, including
its public input buffers.
-/

section

/-!
# ECDSA verification over secp256k1 on x86-64: the table of the generator's multiples in a static

What the verifier's contract says of its one table, `secp256k1GTab` (`TblHeldG`):
held at the address of the static `VG_SECP256K1_GTAB`, not wrapping around, and
apart from the writable regions and the return address; its length
(`secp256k1GW_length`, from the table's shape alone); and a memory holding it, for
the contract's witness (`satMemG`).
-/

@[expose] public section

namespace VG.Proof.Secp256k1

/-! The shape of the verifier's table of generator multiples: one table of
256 points, what `tcombWords_length` needs to count its words in memory. -/

theorem secp256k1G9_length : Impl.Secp256k1.secp256k1G9.length = 1 := rfl

/-- Its one table has 256 points. -/
theorem secp256k1G9_rows : ∀ j < 1, (Impl.Secp256k1.secp256k1G9.getD j []).length = 256 := by
  intro j hj
  rw [show j = 0 by omega]
  decide +kernel

end VG.Proof.Secp256k1

namespace VG.Proof.Ecdsa.Verify.X86_64.Secp256k1

open VG VG.X86_64
open VG.Impl.Ecdsa.X86_64 (Cfg)
open VG.Impl.Secp256k1.X86_64 (secp256k1v secp256k1GTab)

/-- The words of the verifier's table. -/
abbrev secp256k1GW : List (BitVec 64) := secp256k1v.combWords secp256k1GTab

theorem secp256k1v_gtab : secp256k1v.gtab = some secp256k1GTab := rfl

/-- The field of `secp256k1v` the tables of constants read, rewritten rather than
compared by unfolding (which would evaluate `R`). -/
theorem secp256k1v_comb : secp256k1v.comb = none := rfl

theorem secp256k1v_combConsts : secp256k1v.combConsts = [("VG_SECP256K1_GTAB", secp256k1GW)] := by
  unfold Cfg.combConsts
  rw [secp256k1v_comb, secp256k1v_gtab]
  rfl

/-- The table at the static `VG_SECP256K1_GTAB`, held, not wrapping around, and
apart from the regions `wr`. -/
def TblHeldG (s : State) (wr : List Region) : Prop :=
  (∀ i < secp256k1GW.length, s.mem.readW (s.syms "VG_SECP256K1_GTAB" + BitVec.ofNat 64 (8 * i)) 64 = secp256k1GW.getD i 0) ∧
  (s.syms "VG_SECP256K1_GTAB").toNat + 8 * secp256k1GW.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms "VG_SECP256K1_GTAB", 8 * secp256k1GW.length⟩ r

/-- `secp256k1GW` has `256 · 8` words. -/
theorem secp256k1GW_length : secp256k1GW.length = 2048 :=
  (Proof.Weierstrass.tcombWords_length (n := secp256k1v.n) (R := secp256k1v.R) (p := secp256k1v.C.p)
    (H := 256) (tbl := Impl.Secp256k1.secp256k1G9) Proof.Secp256k1.secp256k1G9_length Proof.Secp256k1.secp256k1G9_rows).trans rfl

/-- The table's region, `8 · 2048` bytes at the static's address (see
`secp256k1_constRegions`). -/
theorem secp256k1G_constRegions (f : String → BitVec 64) :
    Abi.constRegions f [("VG_SECP256K1_GTAB", secp256k1GW)] = [⟨f "VG_SECP256K1_GTAB", 16384⟩] := by
  rw [Proof.Ecdsa.X86_64.constRegions_single, secp256k1GW_length]

/-- The memory of the contract's witness: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def satMemG : Mem := constMem 0x100000 secp256k1GW

theorem satMemG_held : ∀ i < secp256k1GW.length,
    satMemG.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = secp256k1GW.getD i 0 := by
  unfold satMemG
  exact constMem_held _ _ (by rw [secp256k1GW_length]; omega)

end VG.Proof.Ecdsa.Verify.X86_64.Secp256k1
end

end

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.Secp256k1

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Secp256k1.X86_64 (secp256k1v)

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.Secp256k1.curve (bytesAt m pk 65) (hashToInt Spec.Secp256k1.curve (bytesAt m digest 32)) (bytesAt m sig 64)

def verifyX86_64 : Contract X86_64.isa where
  pre s :=
    let pk : Region := ⟨s.gpr .rdi, 65⟩
    let digest : Region := ⟨s.gpr .rsi, 32⟩
    let sig : Region := ⟨s.gpr .rdx, 64⟩
    let scratch : Region := ⟨s.gpr .rcx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [pk, digest, sig, ⟨s.syms "VG_SECP256K1_GTAB", 8 * secp256k1GW.length⟩] ∧ s.wr = [scratch] ∧
      pk.Disjoint scratch ∧ digest.Disjoint scratch ∧ sig.Disjoint scratch ∧ ret.Disjoint scratch ∧
      (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeldG s [scratch, ret]
  post s s' := (s'.gpr .rax).setWidth 32 = if vf s.mem (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) then 1 else 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.syms "VG_SECP256K1_GTAB" = s₂.syms "VG_SECP256K1_GTAB"

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x8000
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemG
  rd := [⟨0x1000, 65⟩, ⟨0x2000, 32⟩, ⟨0x3000, 64⟩, ⟨0x100000, 16384⟩]
  wr := [⟨0x8000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .rdi, 65⟩, ⟨s.gpr .rsi, 32⟩, ⟨s.gpr .rdx, 64⟩,
      ⟨s.syms "VG_SECP256K1_GTAB", 8 * secp256k1GW.length⟩])
    (hw : s.wr = [⟨s.gpr .rcx, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .rdi, 65⟩ ⟨s.gpr .rcx, 8192⟩)
    (h2 : Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rcx, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .rdx, 64⟩ ⟨s.gpr .rcx, 8192⟩)
    (r1 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 65⟩) (r2 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 32⟩)
    (r3 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 64⟩) (r4 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, 8192⟩)
    (f0 : (s.gpr .rdi).toNat + 65 ≤ 2 ^ 64) (f1 : (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64)
    (f2 : (s.gpr .rdx).toNat + 64 ≤ 2 ^ 64) (f3 : (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64)
    (ht : TblHeldG s [⟨s.gpr .rcx, 8192⟩, ⟨s.gpr .rsp, 8⟩])
    (hal : (s.syms "VG_SECP256K1_GTAB").toNat % 64 = 0) :
    (Spec.Ecdsa.Secp256k1.inst.verifyContract (X86_64.abi.withConsts secp256k1v.combConsts)).pre s := by
  sig_pre [Spec.Ecdsa.Secp256k1.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, secp256k1v_combConsts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr]),
    hdw _ (by simp), hal, by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, r4, f0, f1, f2, f3⟩

theorem sat_spec : (Spec.Ecdsa.Secp256k1.inst.verifyContract (X86_64.abi.withConsts secp256k1v.combConsts)).pre
    satState := by
  have hl := secp256k1GW_length
  have held : ∀ i < secp256k1GW.length, satState.mem.readW (satState.syms "VG_SECP256K1_GTAB" +
      BitVec.ofNat 64 (8 * i)) 64 = secp256k1GW.getD i 0 := satMemG_held
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
    verifyX86_64.Implies (Spec.Ecdsa.Secp256k1.inst.verifyContract (X86_64.abi.withConsts secp256k1v.combConsts)) where
  pre s h := by
    sig_pre [Spec.Ecdsa.Secp256k1.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
      Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, secp256k1v_combConsts,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, hdr, -, ht, hw, h1, h2, h3, -, -, -, r4, -, -, -, f4⟩ := h
    refine ⟨?_, hw, h1, h2, h3, r4, f4, hheld, hfit, fun r hr => ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdr
  post := by
    sig_implies_post [Spec.Ecdsa.Secp256k1.inst, Spec.Ecdsa.Instance.verifyContract,
      Spec.Ecdsa.Instance.verifySig, Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, X86_64.abi,
      X86_64.argRegs, secp256k1v_combConsts, Abi.withConsts, verifyX86_64, vf]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.Secp256k1.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
      Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, secp256k1v_combConsts,
      Abi.withConsts] at h
    obtain ⟨h0, hs, -, h1, h2, h3, h4⟩ := h
    exact ⟨h0, h1, h2, h3, h4, hs⟩
  sat := ⟨satState, sat_spec⟩

end VG.Proof.Ecdsa.Verify.X86_64.Secp256k1
