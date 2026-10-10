import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Gather.CT
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Verified
import VerifiedGarbage.Impl.StackScratch.AArch64

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, AArch64: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_chacha20_poly1305_seal_gather`, with the 784 bytes of stack below the
stack pointer that its frame and its call use
(`Spec.ChaCha20Poly1305.sealGatherContract`), implies the one the proof is
written against (`gatherAArch64`, `gather_implies`), and so the code,
calling an implementation of `vg_chacha20_poly1305_seal` by its shared
contract, is `Verified` against it (`sealGather_verified`). The frames of
`vg_chacha20_poly1305_seal` fit in its 768 bytes (`seal_depth`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.AArch64.Gather

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.SealGather

theorem sealGather_correct (F : SealFn) (s : State) (hs : gatherAArch64.pre s) :
    ∃ t s', Exec isa (sealGather F.name F.code) s t s' ∧ abiPreserved s s' ∧ gatherAArch64.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := sealGather_wp F hs
  exact ⟨t, s', he, ha, hp⟩

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl
theorem filter_true' (l : List Region) : l.filter (fun _ => true) = l := List.filter_eq_self.mpr (by simp)
theorem filter_false' (l : List Region) : l.filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)
theorem filterMap_some' {β : Type} (f : Region → β) (l : List Region) :
    l.filterMap (fun x => some (f x)) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.filterMap_cons, ih]
theorem filterMap_none' {β : Type} (l : List Region) : l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.filterMap_cons, ih]
theorem pairFacts_ro (l : List (Region × Bool)) (h : ∀ a ∈ l, a.2 = false) : Sig.pairFacts l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [Sig.pairFacts, ih fun b hb => h b (List.mem_cons_of_mem _ hb), List.append_nil]
    refine List.filterMap_eq_nil_iff.mpr fun b hb => ?_
    rw [h a List.mem_cons_self, h b (List.mem_cons_of_mem _ hb)]
    rfl

theorem gatherPre_of_spec {s : State} (h : (Spec.ChaCha20Poly1305.sealGatherContract AArch64.abi 784).pre s) :
    gatherPre s := by
  sig_pre [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, AArch64.abi, AArch64.argRegs, stackArgs_one, List.append_eq] at h
  rw [Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  trace_state
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kt, nd, nt, ad, at_, dt, dds, ⟨dl, da⟩, tds, tl, ta⟩,
    bk, bn, ba, bd, bt, ⟨bds, bl, barg⟩, ok, on, oa, od, ot, ⟨ods, ol⟩, hg, hpm⟩ := h
  exact ⟨rd, wr, kd, kt, nd, nt, ad, at_, dds.symm, tds.symm, fun r hr' => ⟨(dl r hr').symm, (tl r hr').symm⟩,
    dt, da, ta, bk, bn, ba, bds, bl, barg, bd, bt, ok, on, oa, ods, ol, od, ot, w₁, w₂, hg, hpm⟩

theorem gatherPost_of {s s' : State} (h : gatherPost s s') :
    (Spec.ChaCha20Poly1305.sealGatherContract AArch64.abi 784).post s s' := by
  sig_post [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPost, AArch64.abi, AArch64.argRegs, stackArgs_one, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State} (hp : (Spec.ChaCha20Poly1305.sealGatherContract AArch64.abi 784).pub s₁ s₂) :
    gatherPub s₁ s₂ := by
  sig_pub [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, AArch64.abi, AArch64.argRegs, stackArgs_one, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨qsp, q0, q1, q2, q3, q4, q5, q6, q7, a0, hd⟩ := hp
  exact ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, a0, hd⟩

/-- A state satisfying the precondition of `vg_chacha20_poly1305_seal_gather`:
no slices, no additional data or text; the tag at `0x5000`. -/
def gatherSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x50 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9000, 8⟩]
  wr := [⟨0, 0⟩, ⟨0x5000, 16⟩]

theorem gatherSat_pre : ∃ s, (Spec.ChaCha20Poly1305.sealGatherContract AArch64.abi 784).pre s := by
  sig_implies_sat [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, AArch64.abi, AArch64.argRegs, stackArgs_one, List.append_eq]
    [gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.ChaCha20Poly1305.pMax] using gatherSat

theorem gather_implies : gatherAArch64.Implies (Spec.ChaCha20Poly1305.sealGatherContract AArch64.abi 784) :=
  ⟨fun _ h => gatherPre_of_spec h, fun _ _ _ h => gatherPost_of h, fun _ _ _ _ h => gatherPub_of h, gatherSat_pre⟩

theorem sealGather_verified (F : SealFn) :
    Verified AArch64.target (sealGather F.name F.code) (Spec.ChaCha20Poly1305.sealGatherContract AArch64.abi 784) :=
  Verified.of_correct (k := gatherAArch64) (sealGather_correct F) (sealGather_ct F) gather_implies

theorem depth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

open VG.Impl.ChaCha20Poly1305.AArch64 in
theorem sealCode_noFrames (v : Proof.ChaCha20.AArch64.XorImpl) : (sealCode v.callee v.stitched).noFrames = true := by
  have hv := v.noFrames
  generalize v.stitched = st
  generalize v.callee = c at hv
  have hs : (cryptStitched c.sve true).noFrames = true := by cases c.sve <;> decide +kernel
  cases st <;>
  simp only [sealCode, sealStitched, sealWith, sealMain, sealStitchedMain, sealTail, prologue, macPad, cryptWith,
    absorbLengths, finalizeTag, padTail, Code.noFrames, hv, hs, Bool.and_true, Bool.true_and, Bool.false_eq_true,
    ite_false, ite_true] <;>
  decide +kernel

open VG.Impl.ChaCha20Poly1305.AArch64 in
/-- The frames of `vg_chacha20_poly1305_seal`, in its frame of 768 bytes, use at most those. -/
theorem seal_depth (v : Proof.ChaCha20.AArch64.XorImpl) :
    16 * (Impl.StackScratch.AArch64.withStackScratchWiped 768 .x7 95 (sealCode v.callee v.stitched)).aarch64Depth
      ≤ 768 := by
  simp only [Impl.StackScratch.AArch64.withStackScratchWiped, Impl.StackScratch.AArch64.withStackScratch,
    Code.aarch64Depth, Instr.frameUnits, depth_of_noFrames (sealCode_noFrames v)]
  decide

end VG.Proof.ChaCha20Poly1305.AArch64.Gather
