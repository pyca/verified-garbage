module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Gather.Fn
public import VerifiedGarbage.Impl.ChaCha20Poly1305.PPC64LE.SealGather
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Gather.Fn
meta import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset

/-! ### `ChaCha20Poly1305.PPC64LE.Gather.CT`, which only this module used -/

section

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs whose arguments and
descriptors agree (`gatherPub`) leak the same trace: the frame's push, the
entry, the loads of the call's arguments and of the return address are at
the stack pointer or our frame; the gathering is constant time by
`gather_rel` (`Proof/Gather/PPC64LE/LoopCT.lean`); and the call is constant
time by its callee's contract, whose public arguments agree
(`sealGather_ct`). As on AArch64 (`Proof/ChaCha20Poly1305/AArch64/Gather/CT.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE.Gather

open VG VG.PPC64LE VG.Impl.ChaCha20Poly1305.PPC64LE.SealGather
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_seq rel_taint ct_of gather_rel)

theorem sealGather_ct (hv : SealOk)
    (hct : ConstantTime isa (Spec.ChaCha20Poly1305.sealContract PPC64LE.abi 848).pre
      (Spec.ChaCha20Poly1305.sealContract PPC64LE.abi 848).pub sealCode) :
    ConstantTime isa gatherPre gatherPub sealGather := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, a0, hdesc⟩ := hq
  have hP : Pf σ₁ = Pf σ₂ := by simp only [Pf, Bs, qsp]
  refine (RelCT.alloc (P := Eq2 σ₁ σ₂) (R := TT) (fun a b ⟨ha, hb⟩ => by subst ha hb; exact qsp)
    ((?_ : RelCT isa (Eq2 (allocated 80 σ₁) (allocated 80 σ₂)) _ TT).mono
      (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst hs ht; exact ⟨ha, hb⟩) fun _ _ h => h)).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  -- The entry.
  refine rel_seq (rel_taint [] (show σ₁.sp - BitVec.ofNat 64 80 = σ₂.sp - BitVec.ofNat 64 80 by rw [qsp]) (by simp)
    (by taint_decide)) (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The gathering.
  have g₁ := gatherPre_of h₁ he₁
  have g₂ := gatherPre_of h₂ he₂
  simp only [Src, Dst, Cnt, L, ← q7, ← q8, ← q9, ← q10] at g₂
  have hd : ∀ j < Cnt σ₁ * 16, e₁.mem (Src σ₁ + BitVec.ofNat 64 j) = e₂.mem (Src σ₁ + BitVec.ofNat 64 j) := by
    intro j hj
    have hx : (dsR σ₁).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ hj (by have := h₁.ods; omega_using [hj, this])
    have hx₂ : (dsR σ₂).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 := by
      simp only [dsR, Src, Cnt, ← q7, ← q8]; exact hx
    rw [he₁.mem, he₂.mem, Lay.keepE h₁.bds.symm hx, Lay.keepE h₂.bds.symm hx₂]
    exact hdesc j hj
  refine rel_seq (gather_rel hd g₁ g₂ (by rw [he₁.sp, he₂.sp, hP])) (gathered_wp h₁ he₁) (gathered_wp h₂ he₂)
    fun u₁ u₂ hg₁ hg₂ => ?_
  -- The call's arguments.
  refine rel_seq (rel_taint [.r12] (by rw [hg₁.sp, hg₂.sp, hP]) (by simp [hg₁.r12, hg₂.r12, hP])
    (by taint_decide)) (ready_wp h₁ hg₁) (ready_wp h₂ hg₂) fun c₁ c₂ hc₁ hc₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by simp only [rdC, kR, nR, aR, K, Nn, Ad, AL, q3, q4, q5, q6]
  have hwr : wrC σ₂ = wrC σ₁ := by simp only [wrC, dR, tgR, Dst, L, Tg, q9, q10, a0]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hc₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hc₂.call h₂
  rw [hrd, hwr] at cp₂ cv₂
  rw [hwr] at cw₂
  obtain ⟨r3₁, r4₁, r5₁, r6₁, r7₁, r8₁, r9₁⟩ := hc₁.callGpr
  obtain ⟨r3₂, r4₂, r5₂, r6₂, r7₂, r8₂, r9₂⟩ := hc₂.callGpr
  refine rel_seq (RelCT.call hv hct (rdC σ₁) (wrC σ₁) fun a b ⟨ha, hb⟩ => by
      subst ha hb
      refine ⟨sealSpec_pre cp₁, sealSpec_pre cp₂, sealSpec_pub ?_, cv₁, cw₁, cv₂, cw₂⟩
      simp only [State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, r3₁, r4₁, r5₁, r6₁, r7₁,
        r8₁, r9₁, r3₂, r4₂, r5₂, r6₂, r7₂, r8₂, r9₂, hc₁.sp, hc₂.sp, hP, K, Nn, Ad, Dst, Tg, q3, q4, q5, q6, q9,
        q10, a0, and_self])
    (called_wp hv h₁ hc₁) (called_wp hv h₂ hc₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- The return address.
  exact rel_taint [] (by rw [hz₁.sp, hz₂.sp, hP]) (by simp) (by taint_decide)

end VG.Proof.ChaCha20Poly1305.PPC64LE.Gather

end

end

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_chacha20_poly1305_seal_gather`, with the 928 bytes of stack below the
stack pointer that its frame and its call use
(`Spec.ChaCha20Poly1305.sealGatherContract`), implies the one the proof is
written against (`gatherPPC64LE`, `gather_implies`), and so the code, calling
`vg_chacha20_poly1305_seal` by its shared contract (`seal_framed`), is
`Verified` against it (`sealGather_verified`). As on AArch64
(`Proof/ChaCha20Poly1305/AArch64/Gather/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE.Gather

open VG VG.PPC64LE VG.Impl.ChaCha20Poly1305.PPC64LE.SealGather

theorem sealGather_correct (s : State) (hs : gatherPPC64LE.pre s) :
    ∃ t s', Exec isa sealGather s t s' ∧ abiPreserved s s' ∧ gatherPPC64LE.post s s' := by
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

theorem gatherPre_of_spec {s : State} (h : (Spec.ChaCha20Poly1305.sealGatherContract PPC64LE.abi 928).pre s) :
    gatherPre s := by
  sig_pre [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, PPC64LE.abi, PPC64LE.argRegs, stackArgs_one, List.append_eq] at h
  rw [Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or,
    List.cons_append] at h
  obtain ⟨w₁, w₂, rd, wr, ⟨kd, kt, nd, nt, ad, at_, dt, dds, ⟨dl, da⟩, tds, tl, ta⟩,
    bk, bn, ba, bd, bt, ⟨bds, bl, barg⟩, ok, on, oa, od, ot, ⟨ods, ol⟩, hg, hpm⟩ := h
  exact ⟨rd, wr, kd, kt, nd, nt, ad, at_, dds.symm, tds.symm, fun r hr' => ⟨(dl r hr').symm, (tl r hr').symm⟩,
    dt, da, ta, bk, bn, ba, bds, bl, barg, bd, bt, ok, on, oa, ods, ol, od, ot, w₁, w₂, hg, hpm⟩

theorem gatherPost_of {s s' : State} (h : gatherPost s s') :
    (Spec.ChaCha20Poly1305.sealGatherContract PPC64LE.abi 928).post s s' := by
  sig_post [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPost, PPC64LE.abi, PPC64LE.argRegs, stackArgs_one, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State}
    (hp : (Spec.ChaCha20Poly1305.sealGatherContract PPC64LE.abi 928).pub s₁ s₂) : gatherPub s₁ s₂ := by
  sig_pub [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, PPC64LE.abi, PPC64LE.argRegs, stackArgs_one, List.append_eq] at hp
  obtain ⟨qsp, q3, q4, q5, q6, q7, q8, q9, q10, a0, hd⟩ := hp
  exact ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, a0, hd⟩

/-- A state satisfying the precondition of `vg_chacha20_poly1305_seal_gather`:
no slices, no additional data or text; the tag at `0x5000`, its address the
stack argument at `sp + 96`. -/
def gatherSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r7 => 0x4000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9061 then 0x50 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9060, 8⟩]
  wr := [⟨0, 0⟩, ⟨0x5000, 16⟩]

theorem gatherSat_pre : ∃ s, (Spec.ChaCha20Poly1305.sealGatherContract PPC64LE.abi 928).pre s := by
  sig_implies_sat [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, PPC64LE.abi, PPC64LE.argRegs, stackArgs_one, List.append_eq]
    [gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.ChaCha20Poly1305.pMax] using gatherSat

theorem gather_implies : gatherPPC64LE.Implies (Spec.ChaCha20Poly1305.sealGatherContract PPC64LE.abi 928) :=
  ⟨fun _ h => gatherPre_of_spec h, fun _ _ _ h => gatherPost_of h, fun _ _ _ _ h => gatherPub_of h, gatherSat_pre⟩

theorem sealGather_verified :
    Verified PPC64LE.target sealGather (Spec.ChaCha20Poly1305.sealGatherContract PPC64LE.abi 928) :=
  Verified.of_correct (k := gatherPPC64LE) sealGather_correct (sealGather_ct seal_framed.1 seal_framed.2.1)
    gather_implies

end VG.Proof.ChaCha20Poly1305.PPC64LE.Gather
