module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Hash
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Hash
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
public import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.X86_64
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.PubVerify
import VerifiedGarbage.Proof.Ecdh.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.JointChecks
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPublic
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.JointErased
import Batteries.Data.List.Lemmas
import VerifiedGarbage.Proof.Framework.LitShare
public import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Front
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
meta import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.X86_64
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
meta import VerifiedGarbage.Proof.Weierstrass.CombW
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.PubVerify
meta import VerifiedGarbage.Proof.Ecdh.X86_64.Main
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.JointChecks
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPublic
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.JointErased
meta import Batteries.Data.List.Lemmas
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Front
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Impl.Secp256k1.GTable9
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Ecdsa.X86_64.Tables
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ecdsa.Secp256k1
meta import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Impl.Secp256k1.GTable9
meta import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Tables

/-! ### `Ecdsa.Verify.X86_64.Secp256k1.Contract`, which only this module used -/

section

/-!
# ECDSA verification over secp256k1 on x86-64: the contract the proof is written against

The facts of `Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst` for x86-64, under the
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
  rw [show j = 0 by omega_using [hj]]
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
  exact constMem_held _ _ (by rw [secp256k1GW_length]; omega_using [])

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
    (Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst (X86_64.abi.withConsts secp256k1v.combConsts)).pre s := by
  sig_pre [Spec.Ecdsa.Secp256k1.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
    Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, secp256k1v_combConsts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr]),
    hdw _ (by simp), hal, by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, r4, f0, f1, f2, f3⟩

theorem sat_spec : (Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst (X86_64.abi.withConsts secp256k1v.combConsts)).pre
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
    verifyX86_64.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst (X86_64.abi.withConsts secp256k1v.combConsts)) where
  pre s h := by
    sig_pre [Spec.Ecdsa.Secp256k1.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
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
    sig_implies_post [Spec.Ecdsa.Secp256k1.inst, Proof.Ecdsa.verifyContract,
      Proof.Ecdsa.verifySig, Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, X86_64.abi,
      X86_64.argRegs, secp256k1v_combConsts, Abi.withConsts, verifyX86_64, vf]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.Secp256k1.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
      Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, secp256k1v_combConsts,
      Abi.withConsts] at h
    obtain ⟨h0, hs, -, h1, h2, h3, h4⟩ := h
    exact ⟨h0, h1, h2, h3, h4, hs⟩
  sat := ⟨satState, sat_spec⟩

end VG.Proof.Ecdsa.Verify.X86_64.Secp256k1

end

end

/-!
# ECDSA verification over secp256k1 on x86-64: `Verified`

secp256k1 is a curve the proof supports (`secp256k1v_ok`, `a = 0` for its
doublings, and `Law` for its group law, its table of the generator's
multiples and `InvSounds` for its inversions, which the registration file
supplies), so `jointVerify_ok` gives the contract's postcondition; the
callee-saved registers are restored, `rsp` is never written, and every store
is to `scratch`, which the return address is apart from (`abiPreserved`).
The timing depends only on what the shared contract makes public: the
pointers, the key, the digest and the signature (`jointVerify_ct`).
-/

@[expose] public section

/-! secp256k1's joint verifier's curve and contract: `secp256k1v` is
`secp256k1` with `pubVerify`, which only verification reads, and with the
table of the generator's multiples: the same curve, layout and
multiplications, so the same facts (`secp256k1v_ok`, from `secp256k1_ok`:
those that do not need `a = -3`), and the contract's precondition gives
theirs (`pre_of`). The shared contract makes the key, the digest and the
signature public (`jointPublic_of_spec`). -/

namespace VG.Proof.Ecdsa.Verify.X86_64.Secp256k1

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Secp256k1.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.Secp256k1 VG.Proof.Weierstrass VG.Proof.Ecdh.X86_64
open VG.Proof.Weierstrass.X86_64 (InvSounds)

theorem secp256k1v_ok (hI : InvSounds) : BaseCfgOk secp256k1v :=
  baseCfgOk_pubVerify_gtab (secp256k1_ok hI) rfl true _

theorem pre_of {s : State} (h : verifyX86_64.pre s) : VPre secp256k1v s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, secp256k1v_combConsts, show secp256k1v.C.len = 32 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h7, ?_⟩
  rw [TblsHeld, secp256k1v_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    simp [hr]

theorem jointPublic_of_spec {a b : State}
    (pub : (Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst (X86_64.abi.withConsts secp256k1v.combConsts)).pub a b) :
    JointPublic secp256k1v secp256k1GTab a b := by
  sig_pub [Spec.Ecdsa.Secp256k1.inst,Proof.Ecdsa.verifyContract,Proof.Ecdsa.verifySig,
    Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,X86_64.abi,X86_64.argRegs,secp256k1v_combConsts,
    Abi.withConsts] at pub
  obtain ⟨_,hsy,inputs,h0,h1,h2,h3⟩ := pub
  have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
  have parts := List.append_inj eqBytes (by simp only [List.length_append,length_bytesAt])
  have kd := List.append_inj parts.1 (by simp only [length_bytesAt])
  have key := kd.1
  rw [peer_bytes _ _ 32,peer_bytes _ _ 32] at key
  obtain ⟨tag,xy⟩ := List.cons.inj key
  have coords := List.append_inj xy (by simp only [length_bytesAt])
  have sig := parts.2
  change Spec.Ecdsa.bytesAt a.mem (a.gpr .rdx) (32+32)=
    Spec.Ecdsa.bytesAt b.mem (b.gpr .rdx) (32+32) at sig
  rw [bytesAt_add,bytesAt_add] at sig
  have rs := List.append_inj sig (by simp only [length_bytesAt])
  refine ⟨Taint.agree_ofRegs ?_,hsy,tag,congrArg Spec.Weierstrass.ofBytes coords.1,
    congrArg Spec.Weierstrass.ofBytes coords.2,
    congrArg (fun bs => Spec.Weierstrass.ofBytes bs >>> secp256k1v.sh) kd.2,
    congrArg Spec.Weierstrass.ofBytes rs.1,congrArg Spec.Weierstrass.ofBytes rs.2⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

end VG.Proof.Ecdsa.Verify.X86_64.Secp256k1

namespace VG.Proof.Secp256k1.X86_64
open VG VG.Impl.Secp256k1.X86_64 VG.Proof.Ecdsa.Verify.X86_64

/-- The joint multiplication's writes are apart from the final check's fixed inputs. -/
theorem joint_frame_layout : JointFrameLayout secp256k1v publicJoint := by
  constructor
  · unfold VG.Proof.Ecdsa.X86_64.FixedOk
    decide +kernel
  · decide +kernel
  · decide +kernel

end VG.Proof.Secp256k1.X86_64

/-! Whole-function timing of secp256k1's joint verification follows the public-input contract. -/

namespace VG.Proof.Ecdsa.Verify.X86_64.Secp256k1
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Secp256k1.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Secp256k1.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

section
variable (hL : Law Spec.Secp256k1.curve)
    (hT : CombOkW Spec.Secp256k1.curve 9 1 Impl.Secp256k1.secp256k1G9 Impl.Secp256k1.secp256k1G9Start)
    (hI : InvSounds)
include hL hT hI

theorem jointVerify_secp256k1_public_ct :
    ConstantTime isa (VPre secp256k1v) (JointPublic secp256k1v secp256k1GTab)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify secp256k1v publicJoint (jointDouble publicJoint.K)).inline := by
  have hc := secp256k1v_ok hI
  refine jointVerify_ct_of_points hc joint_before_ct ?_ joint_after_ct
  intro s₀ t₀ ps pt pub
  exact jointPoints_relCT (j := publicJoint) hc hL (jdblOk_dblJ0 hL secp256k1_a0) (.ofGTab rfl hT (by decide) (by decide) rfl) rfl
    (by decide +kernel) joint_add_layout joint_init_layout joint_prep_layout (joint_doubler hc hL)
    joint_mul_checks (fun h => absurd h (by decide)) ps pt pub

theorem jointVerify_ct :
    ConstantTime isa
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst (X86_64.abi.withConsts secp256k1v.combConsts)).pre
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst (X86_64.abi.withConsts secp256k1v.combConsts)).pub
      Impl.Ecdsa.Verify.X86_64.verifySecp256k1.inline := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_secp256k1_public_ct hL hT hI _ _ _ _ _ _ (pre_of (implies.pre _ pre₁))
    (pre_of (implies.pre _ pre₂)) (jointPublic_of_spec pub) e₁ e₂

end
end VG.Proof.Ecdsa.Verify.X86_64.Secp256k1

namespace VG.Proof.Ecdsa.Verify.X86_64.Secp256k1
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64 VG.Impl.Secp256k1.X86_64
open VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Secp256k1.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

section
variable (hL : Law Spec.Secp256k1.curve)
    (hT : CombOkW Spec.Secp256k1.curve 9 1 Impl.Secp256k1.secp256k1G9 Impl.Secp256k1.secp256k1G9Start)
    (hI : InvSounds)
include hL hT hI

theorem jointVerify_secp256k1_ok {s : State} (hp : VPre secp256k1v s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify secp256k1v publicJoint (jointDouble publicJoint.K)).inline s
      fun t => (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost secp256k1v s t := by
  have hc := secp256k1v_ok hI
  refine jointVerify_ok hc hL rfl (by decide +kernel) (by decide +kernel) hp ?_
  intro a g hM Q hQ hRep
  exact jointPoints_ok (j := publicJoint) hc hL (.ofGTab rfl hT (by decide) (by decide) rfl) rfl
    (jdblOk_dblJ0 hL secp256k1_a0)
    (by decide +kernel) joint_add_layout joint_init_layout joint_prep_layout joint_frame_layout
    (joint_doubler hc hL) (fun h => absurd h (by decide)) hp hM hQ hRep

end

theorem verify_abi_of_wp {code : Prog isa} {s : State} (hs : verifyX86_64.pre s)
    (hw : WP isa code s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ verifyX86_64.post s t)
    (hc : code.allInstrs (fun i => !Taint.clobbers i .rsp && !loadsMxcsr i)=true)
    (hnc : code.noCalls=true) :
    ∃ t s',Exec isa code s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' := by
  obtain ⟨t,s',he,hsv,hpost⟩ := hw
  rw [Code.allInstrs_eq,List.all_eq_true] at hc
  have hsp : ∀ i∈instrs code,Taint.clobbers i .rsp=false := fun i hi => by
    have := hc i hi
    simp only [Bool.and_eq_true,Bool.not_eq_eq_eq_not,Bool.not_true] at this
    exact this.1
  have hmx : code.allInstrs (fun i => !loadsMxcsr i)=true := by
    rw [Code.allInstrs_eq,List.all_eq_true]
    intro i hi
    have := hc i hi
    simp only [Bool.and_eq_true] at this
    exact this.2
  have F := (Exec.regions he hnc).2.2
  obtain ⟨-,hwr,-,-,-,hrs,-,-⟩ := hs
  refine ⟨t,s',he,abiPreserved_of_exec hmx he ⟨fun r hr => ?_,?_⟩,hpost⟩
  · simp only [calleeSaved,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact Exec.gpr hsp he
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
  · rw [hwr] at F
    exact F.readW (r:=⟨s.gpr .rsp,8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      rintro r rfl
      exact hrs) (by decide)

/-- The shared contract, but with `verifyX86_64`'s postcondition: what the
proofs of the inlined code give. -/
def verifyK₀ : Contract isa :=
  { pre := (Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst (X86_64.abi.withConsts secp256k1v.combConsts)).pre
    post := verifyX86_64.post
    pub := (Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst (X86_64.abi.withConsts secp256k1v.combConsts)).pub }

theorem sat_spec8 :
    (Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst (X86_64.abi.withConsts secp256k1v.combConsts) 8).pre
      satState := by
  have held : ∀ i < secp256k1GW.length, satState.mem.readW (satState.syms "VG_SECP256K1_GTAB" +
      BitVec.ofNat 64 (8 * i)) 64 = secp256k1GW.getD i 0 := satMemG_held
  sig_pre [Spec.Ecdsa.Secp256k1.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
    Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, secp256k1v_combConsts,
    Abi.withConsts, secp256k1G_constRegions, Abi.constsHeld, stackBelow]
  sig_and_intros
  all_goals first | exact Region.disjoint_of_sep (by decide) | rfl | exact held | decide

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 :
    verifyK₀.Implies
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst (X86_64.abi.withConsts secp256k1v.combConsts) 8) :=
  ⟨fun _ hs => Sig.pre_stack0 hs, fun s s' hs hp => implies.post s s' (Sig.pre_stack0 hs) hp,
    fun _ _ _ _ hp => hp, ⟨satState, sat_spec8⟩⟩

section
variable (hL : Law Spec.Secp256k1.curve)
    (hT : CombOkW Spec.Secp256k1.curve 9 1 Impl.Secp256k1.secp256k1G9 Impl.Secp256k1.secp256k1G9Start)
    (hI : InvSounds)
include hL hT hI

theorem verify_x86 (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s',Exec isa verifySecp256k1.inline s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' :=
  verify_abi_of_wp hs (jointVerify_secp256k1_ok hL hT hI (pre_of hs))
    (by rw [Code.allInstrs_inline]; exact verify_rspMxcsr) (Code.noCalls_inline verify_inlineOk)

theorem verify_verified : Verified X86_64.target verifySecp256k1
    (Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst (X86_64.abi.withConsts secp256k1v.combConsts) 8) :=
  Verified.of_inline (k₀ := verifyK₀) verify_inlineOk (fun s hs => verify_x86 hL hT hI s (implies.pre _ hs))
    (jointVerify_ct hL hT hI) implies8 (fun _ h => Sig.clear_of_pre_consts h) (fun _ _ _ _ _ hp => hp)
    fun s₁ s₂ h₁ h₂ hp => (implies.pub s₁ s₂ (Sig.pre_stack0 h₁) (Sig.pre_stack0 h₂) hp).1

/-- `vg_ecdsa_secp256k1_verify`, taking the hash function's output: `verify_verified`,
run on the `len` bytes of the hash (`verifyHash_verified_cons`). -/
theorem verifyHash_verified : Verified X86_64.target
    (Impl.Ecdsa.X86_64.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false verifySecp256k1)
    (Spec.Ecdsa.Secp256k1.inst.verifyHashContract (X86_64.abi.withConsts secp256k1v.combConsts) 96) :=
  Hash.verifyHash_verified_cons Proof.Ecdsa.Verify.secp256k1_len (by decide) (verify_verified hL hT hI)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) (by taint_decide)
    (Hash.hashSat_cons (by decide) sat_spec8 (by decide) fun r hr => by
      simp only [satState, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

end
end VG.Proof.Ecdsa.Verify.X86_64.Secp256k1
