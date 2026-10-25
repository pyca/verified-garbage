module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Gather.Contract
public import VerifiedGarbage.Impl.ChaCha20Poly1305.RISCV64.SealGather
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Gather.CT
import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Gather.Fn
import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Sig

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, RISCV64: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_chacha20_poly1305_seal_gather`, with the 640 bytes of stack below the
stack pointer that its frame and its call use
(`Spec.ChaCha20Poly1305.sealGatherContract`), implies the one the proof is
written against (`gatherRISCV64`, `gather_implies`), and so the code, calling
`vg_chacha20_poly1305_seal` by its shared contract (`seal_framed`), is
`Verified` against it (`sealGather_verified`). As on PPC64LE
(`Proof/ChaCha20Poly1305/PPC64LE/Gather/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64.Gather

open VG VG.RISCV64 VG.Impl.ChaCha20Poly1305.RISCV64.SealGather

theorem sealGather_correct (s : State) (hs : gatherRISCV64.pre s) :
    ∃ t s', Exec isa sealGather s t s' ∧ abiPreserved s s' ∧ gatherRISCV64.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := sealGather_wp seal_framed.1 hs
  exact ⟨t, s', he, ha, hp⟩

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl
theorem filter_true' (l : List Region) : l.filter (fun _ => true) = l := List.filter_eq_self.mpr (by simp)
theorem filter_false' (l : List Region) : l.filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)
theorem filterMap_some' {β : Type} (f : Region → β) (l : List Region) :
    l.filterMap (fun x => some (f x)) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]
theorem filterMap_none' {β : Type} (l : List Region) : l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]
theorem pairFacts_ro (l : List (Region × Bool)) (h : ∀ a ∈ l, a.2 = false) : Sig.pairFacts l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [Sig.pairFacts, ih fun b hb => h b (List.mem_cons_of_mem _ hb), List.append_nil]
    refine List.filterMap_eq_nil_iff.mpr fun b hb => ?_
    rw [h a List.mem_cons_self, h b (List.mem_cons_of_mem _ hb)]
    rfl

theorem gatherPre_of_spec {s : State} (h : (Spec.ChaCha20Poly1305.sealGatherContract RISCV64.abi 640).pre s) :
    gatherPre s := by
  sig_pre [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, RISCV64.abi, RISCV64.argRegs, stackArgs_one, List.append_eq] at h
  rw [Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or,
    List.cons_append] at h
  obtain ⟨al, w₁, w₂, rd, wr, ⟨kd, kt, nd, nt, ad, at_, dt, dds, ⟨dl, da⟩, tds, tl, ta⟩,
    bk, bn, ba, bd, bt, ⟨bds, bl, barg⟩, ok, on, oa, od, ot, ⟨ods, ol⟩, hg, hpm⟩ := h
  exact ⟨rd, wr, kd, kt, nd, nt, ad, at_, dds.symm, tds.symm, fun r hr' => ⟨(dl r hr').symm, (tl r hr').symm⟩,
    dt, da, ta, bk, bn, ba, bds, bl, barg, bd, bt, ok, on, oa, ods, ol, od, ot, al, w₁, w₂, hg, hpm⟩

theorem gatherPost_of {s s' : State} (h : gatherPost s s') :
    (Spec.ChaCha20Poly1305.sealGatherContract RISCV64.abi 640).post s s' := by
  sig_post [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPost, RISCV64.abi, RISCV64.argRegs, stackArgs_one, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State}
    (hp : (Spec.ChaCha20Poly1305.sealGatherContract RISCV64.abi 640).pub s₁ s₂) : gatherPub s₁ s₂ := by
  sig_pub [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, RISCV64.abi, RISCV64.argRegs, stackArgs_one, List.append_eq] at hp
  obtain ⟨qsp, q3, q4, q5, q6, q7, q8, q9, q10, a0, hd⟩ := hp
  exact ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, a0, hd⟩

/-- A state satisfying the precondition of `vg_chacha20_poly1305_seal_gather`:
no slices, no additional data or text; the tag at `0x5000`, its address the
stack argument at `sp`. -/
def gatherSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a4 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x50 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9000, 8⟩]
  wr := [⟨0, 0⟩, ⟨0x5000, 16⟩]

theorem gatherSat_pre : ∃ s, (Spec.ChaCha20Poly1305.sealGatherContract RISCV64.abi 640).pre s := by
  sig_implies_sat [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, RISCV64.abi, RISCV64.argRegs, stackArgs_one, List.append_eq]
    [gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.ChaCha20Poly1305.pMax] using gatherSat

theorem gather_implies : gatherRISCV64.Implies (Spec.ChaCha20Poly1305.sealGatherContract RISCV64.abi 640) :=
  ⟨fun _ h => gatherPre_of_spec h, fun _ _ _ h => gatherPost_of h, fun _ _ _ _ h => gatherPub_of h, gatherSat_pre⟩

theorem sealGather_verified :
    Verified RISCV64.target sealGather (Spec.ChaCha20Poly1305.sealGatherContract RISCV64.abi 640) :=
  Verified.of_correct (k := gatherRISCV64) sealGather_correct (sealGather_ct seal_framed.1 seal_framed.2.1)
    gather_implies

end VG.Proof.ChaCha20Poly1305.RISCV64.Gather
