module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Generate.CTPoint
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.CT
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.EntropyRequest
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Generate.CTPoint
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.CT
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.EntropyRequest
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset

/-! # The calls' timing (AArch64)

The taint analysis tracks registers only, so a pointer loaded from the frame
is made public by what correctness says of it (`ldf_then`). The prime
search's and the key's arguments are the same in two runs at a point, and so
is what their contracts let their timing depend on — the search's status,
consumption, request and trace, and the key's status, all from the point's
trace.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MillerRabin.AArch64 (RoundImpl)
open VG.Impl.RsaKeyGen.AArch64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-! ## Frame states, and pointers loaded from the frame -/

/-- A frame state of some run with the public descriptor `p`. -/
def AnyFrame (p : GenPublic) (s : State) : Prop := ∃ original used st, GenFrame p original used st s

theorem GenCTL.any {q : GenPoint} {s : State} (h : GenCTL q s) : AnyFrame q.inputs s :=
  let ⟨o, st, _, hl, _⟩ := h; ⟨o, _, st, hl.toGenFrame⟩

theorem no_pins {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ h => absurd h List.not_mem_nil

/-- `Φ` gives frame states of `f a`: `x19` is the frame's base. -/
theorem frame_pins {α : Type} {Φ : α → State → Prop} (f : α → GenPublic)
    (hΦ : ∀ a s, Φ a s → s.gpr .x19 = (f a).F) : Pins Φ [.x19] := by
  intro a s t h₁ h₂ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact (hΦ a s h₁).trans (hΦ a t h₂).symm

theorem AnyFrame.x19 {p : GenPublic} {s : State} (h : AnyFrame p s) : s.gpr .x19 = p.F :=
  let ⟨_, _, _, g⟩ := h; g.x19

/-- Code the taint analysis checks with `x19` public, from frame states. -/
theorem frame_ct {α : Type} {Φ : α → State → Prop} {c : Prog isa} (f : α → GenPublic)
    (hΦ : ∀ a s, Φ a s → s.gpr .x19 = (f a).F) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.x19]) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_taint [.x19] (frame_pins f hΦ) h

/-- A block that first loads `r` from the frame's word `j`, which `Φ a` fixes
as `v a`: the rest is checked with `r` public too. -/
theorem ldf_then {α : Type} {Φ : α → State → Prop} {rest : List Instr} {r : Reg} {j : Nat} (hj : j < 20)
    (F v : α → BitVec 64) (rs : List Reg) (hpin : Pins Φ rs)
    (hld : ∀ a s, Φ a s → s.gpr .x19 = F a ∧ InRegions (s.rd ++ s.wr) (F a + BitVec.ofNat 64 (8 * j)) 8 ∧
      s.mem.readW (F a + BitVec.ofNat 64 (8 * j)) 64 = v a)
    {h₁ : VG.Taint.Hint VG.AArch64.Taint.T} (c₁ : (taint.check (Taint.ofRegs rs) (.block [ldf r j]) h₁).isSome = true)
    {h₂ : VG.Taint.Hint VG.AArch64.Taint.T} (c₂ : (taint.check (Taint.ofRegs (r :: rs)) (.block rest) h₂).isSome = true) :
    RelCT isa (Two Φ) (.block (ldf r j :: rest)) fun _ _ => True := by
  change RelCT isa (Two Φ) (.block ([ldf r j] ++ rest)) _
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun a t => ∃ s, Φ a s ∧ t = s.write .x r (v a))
    rs hpin c₁ fun a s h => ?_) (two_taint (r :: rs) ?_ c₂))
  · obtain ⟨h19, hin, hv⟩ := hld a s h
    have he : exec (ldf r j) s = some (s.write .x r (v a)) := by
      show exec (.ldr .x r .x19 (8 * j)) s = _
      rw [exec_ldr_x' (by omega) (by rw [h19]; exact hin), h19, hv]
    brun [he]
    exact ⟨s, h, rfl⟩
  · rintro a _ _ ⟨s₁, h₁, rfl⟩ ⟨s₂, h₂, rfl⟩ x hx
    rw [RegUpd.gpr_write, RegUpd.gpr_write]
    split
    · rfl
    · exact hpin a _ _ h₁ h₂ x ((List.mem_cons.mp hx).resolve_left (by assumption))

/-- A header word of a frame state. -/
theorem GenFrame.hdr {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {j : Nat} {v : BitVec 64} (hj : (j, v) ∈ p.headers used) (hj' : 8 * j + 8 ≤ 160) :
    s.gpr .x19 = p.F ∧ InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 (8 * j)) 8 ∧
      s.mem.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 = v :=
  ⟨h.x19, h.frame_ld _ hj', h.headers (j, v) hj⟩

/-- The state's pointer, from a frame state. -/
theorem AnyFrame.stp {p : GenPublic} {s : State} (h : AnyFrame p s) :
    s.gpr .x19 = p.F ∧ InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 (8 * 7)) 8 ∧
      s.mem.readW (p.F + BitVec.ofNat 64 (8 * 7)) 64 = p.stp :=
  let ⟨_, _, _, g⟩ := h; g.hdr (by simp [GenPublic.headers]) (by decide)

theorem outOf_ph {p : GenPublic} {st₁ st₂ : KeyProgress} (h : phaseWord st₁.phase = phaseWord st₂.phase) :
    outOf p st₁ = outOf p st₂ := by
  unfold outOf; rw [h]

theorem plenOf_ph {p : GenPublic} {st₁ st₂ : KeyProgress} (h : phaseWord st₁.phase = phaseWord st₂.phase) :
    plenOf p st₁ = plenOf p st₂ := by
  unfold plenOf; rw [h]

/-! ## The prime search -/

/-- The search's entry, before the call. -/
def CallSCT (q : GenPoint) (u : State) : Prop :=
  ∃ original st s, AtPoint q original st ∧ GenLive q.inputs original q.used st s ∧
    word s.mem q.inputs.stp 24 = q.req ∧ SearchRegs q.inputs q.used st u ∧
    u.mem = writeFrame s.mem (callSp q.inputs) (callValues q.inputs q.used) ∧
    Keep searchArgRegs (allocated 32 s) u

/-- The search's exponent and state words at its entry. -/
theorem callS_state {p : GenPublic} {original s u : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s) (hu : u.sp = callSp p) (ha : SearchRegs p used st u)
    (hm : u.mem = writeFrame s.mem (callSp p) (callValues p used)) :
    Search.searchE (callS p used st u) = p.eB ∧
      Spec.Rsa.wordsAt (callS p used st u).mem (stackArg (callS p used st u) 3) 4 =
        [BitVec.ofNat 64 st.remaining, BitVec.ofNat 64 p.L, BitVec.ofNat 64 (primeEntropy p.L),
          word s.mem p.stp 24] := by
  have hf := h.input.cfacts
  have hfr := callS_frame (st := st) hm
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨-, -, -, sT, -⟩ := hst
  obtain ⟨-, -, -, a3⟩ := callS_args (used := used) (st := st) hu hm
  obtain ⟨-, -, -, r3, r4, -⟩ := ha
  have hword (d : Nat) (hd : d + 8 ≤ 56) : word (callS p used st u).mem p.stp d = word s.mem p.stp d :=
    hfr.readW (r := cS p) (Offset.contains_base _ hd (by have := hf.nT; omega))
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact sT) (by decide)
  refine ⟨?_, ?_⟩
  · simp only [Search.searchE, callS_gpr (by decide : Reg.x3 ∉ linkRegs), callS_gpr (by decide : Reg.x4 ∉ linkRegs),
      r3, r4, toNat_ofNat_lt (show 8 < 2 ^ 64 by decide)]
    rw [← h.state.e]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hfr.bytes (R := ⟨p.stp + BitVec.ofNat 64 48, 8⟩) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact sT.sub_left rE_sub) (by show 8 ≤ 2 ^ 64; decide)
      (List.mem_range.mp hi)
  · rw [a3]
    show [word _ p.stp (8 * 0), word _ p.stp (8 * 1), word _ p.stp (8 * 2), word _ p.stp (8 * 3)] = _
    rw [hword _ (by decide), hword _ (by decide), hword _ (by decide), hword _ (by decide)]
    have h0 := h.state.remaining
    have h1 := h.state.len
    have h2 := h.state.cap
    simp only [Nat.reduceMul] at h0 h1 h2 ⊢
    rw [h0, h1, h2]

theorem CallSCT.sp {q : GenPoint} {u : State} (h : CallSCT q u) : u.sp = callSp q.inputs := by
  obtain ⟨o, st, s, -, hl, -, -, -, k⟩ := h
  exact k.sp.trans (alloc32_sp hl.toGenFrame)

theorem search_call_ct (v : RoundImpl) : RelCT isa (Two CallSCT) (searchCall v) (fun _ _ => True) := by
  refine RelCT.callEx (k := Search.searchContract) (Search.search_correct (Search.Cand.ofRound v))
    (Search.search_constantTime (Search.Cand.ofRound v)) fun u₁ u₂ ⟨q, h₁, h₂, _⟩ => ?_
  have hu₁ := h₁.sp
  have hu₂ := h₂.sp
  obtain ⟨o₁, st₁, s₁, a₁, l₁, w₁, r₁, m₁, k₁⟩ := h₁
  obtain ⟨o₂, st₂, s₂, a₂, l₂, w₂, r₂, m₂, k₂⟩ := h₂
  have hph : phaseWord st₁.phase = phaseWord st₂.phase := a₁.2.1.trans a₂.2.1.symm
  have hres₁ := callS_result l₁ hu₁ r₁ m₁
  have hres₂ := callS_result l₂ hu₂ r₂ m₂
  obtain ⟨e₁, ws₁⟩ := callS_state l₁ hu₁ r₁ m₁
  obtain ⟨e₂, ws₂⟩ := callS_state l₂ hu₂ r₂ m₂
  have hlen₁ : Search.searchLen (callS q.inputs q.used st₁ u₁) = q.inputs.L := by
    simp only [Search.searchLen, callS_gpr (by decide : Reg.x1 ∉ linkRegs), r₁.2.1]
    exact toNat_ofNat_lt (by have := l₁.input.cfacts.len.2.1; omega)
  have hlen₂ : Search.searchLen (callS q.inputs q.used st₂ u₂) = q.inputs.L := by
    simp only [Search.searchLen, callS_gpr (by decide : Reg.x1 ∉ linkRegs), r₂.2.1]
    exact toNat_ofNat_lt (by have := l₂.input.cfacts.len.2.1; omega)
  obtain ⟨b0, b1, b2, b3⟩ := callS_args (used := q.used) (st := st₁) hu₁ m₁
  obtain ⟨c0, c1, c2, c3⟩ := callS_args (used := q.used) (st := st₂) hu₂ m₂
  refine ⟨sReads q.inputs q.used st₁, sWrites q.inputs st₁, sReads q.inputs q.used st₂, sWrites q.inputs st₂,
    callS_pre l₁ hu₁ r₁ m₁, callS_pre l₂ hu₂ r₂ m₂, ?_,
    search_covers_reads l₁.toGenFrame k₁.rd k₁.wr, search_covers_writes l₁.toGenFrame k₁.wr,
    search_covers_reads l₂.toGenFrame k₂.rd k₂.wr, search_covers_writes l₂.toGenFrame k₂.wr⟩
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7⟩ := r₁
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := r₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, e₁.trans e₂.symm, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.withRegions_sp, State.callEntry_sp, hu₁, hu₂]
  · rw [callS_gpr (by decide), callS_gpr (by decide), d0, f0, outOf_ph hph]
  · rw [callS_gpr (by decide), callS_gpr (by decide), d1, f1]
  · rw [callS_gpr (by decide), callS_gpr (by decide), d2, f2]
  · rw [callS_gpr (by decide), callS_gpr (by decide), d3, f3]
  · rw [callS_gpr (by decide), callS_gpr (by decide), d4, f4]
  · rw [callS_gpr (by decide), callS_gpr (by decide), d5, f5]
  · rw [callS_gpr (by decide), callS_gpr (by decide), d6, f6, plenOf_ph hph]
  · rw [callS_gpr (by decide), callS_gpr (by decide), d7, f7]
  · match j, hj with
    | 0, _ => rw [b0, c0]
    | 1, _ => rw [b1, c1]
    | 2, _ => rw [b2, c2]
    | 3, _ => rw [b3, c3]
  · rw [ws₁, ws₂, a₁.2.2.1, a₂.2.2.1, w₁, w₂]
  · rw [hres₁, hres₂, a₁.status, a₂.status]
  · rw [hres₁, hres₂, a₁.cand, a₂.cand]
  · rw [hlen₁, hlen₂, hres₁, hres₂]
    exact Entropy.requested_congr (a₁.status.trans a₂.status.symm) (a₁.available.trans a₂.available.symm)
  · rw [hres₁, hres₂, a₁.prime, a₂.prime]

/-- A loop state at the point, past the allocation of the search's frame. -/
def AllocSCT (q : GenPoint) (u : State) : Prop := ∃ s, GenCTL q s ∧ u = allocated 32 s

theorem search_run_ct (v : RoundImpl) :
    RelCT isa (Two GenCTL) (searchRun (searchCall v)) (fun _ _ => True) := by
  unfold searchRun
  apply RelCT.alloc
  have hct : RelCT isa (Two AllocSCT) (.block searchArgs) fun _ _ => True :=
    ldf_then (r := .x8) (j := 7) (by decide) (fun q => q.inputs.F) (fun q => q.inputs.stp) [.x19]
      (frame_pins (fun q => q.inputs) fun q u ⟨s, h, e⟩ => by subst e; exact h.any.x19)
      (fun q u ⟨s, ⟨o, st, _, hl, _⟩, e⟩ => by
        subst e
        exact ⟨hl.x19, hl.frame_ld' rfl _ (by decide), hl.headers (7, q.inputs.stp) (by simp [GenPublic.headers])⟩)
      (by taint_decide) (by taint_decide)
  have ha : RelCT isa (Two AllocSCT) (.block searchArgs) (Two CallSCT) :=
    two_post hct fun q u ⟨s, ⟨o, st, ha, hl, hw⟩, e⟩ => by
      subst e
      exact WP.mono (search_args_ok hl.toGenFrame) fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨o, st, s, ha, hl, hw, hr, hm, k⟩
  refine (RelCT.seq ha (search_call_ct v)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocated, hsp]⟩

/-! ## The key -/

theorem keyStatus_keyOp (L : Nat) (eB pB qB : List Byte) :
    keyStatus (keyOp L eB pB qB) = keyResultStatus (keyFromPrimes (16 * L) (Spec.Rsa.os2ip eB)
      (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB)) := by
  unfold keyOp
  split <;> rename_i h <;> rw [h] <;> rfl

/-- After `q`'s search accepted a prime, at the point: the key's state. -/
def KeyCT (q : GenPoint) (u : State) : Prop :=
  ∃ original st final c pB, AtPoint q original st ∧ Mid q.inputs original final q.used st u ∧
    (rOf q.inputs original q.used st).outcome = .accepted c ∧ 0 < (rOf q.inputs original q.used st).used ∧
    st.phase = .q pB

theorem KeyCT.frame {q : GenPoint} {u : State} (h : KeyCT q u) : AnyFrame q.inputs u :=
  let ⟨o, _, _, _, _, _, hm, _⟩ := h; ⟨o, _, _, hm.frame⟩

/-- The key's status, from the point. -/
theorem KeyCT.status {q : GenPoint} {u : State} (h : KeyCT q u) : keyStatus (keyOf q.inputs u.mem) = q.key := by
  obtain ⟨o, st, final, c, pB, ha, hm, ho, hpos, hph⟩ := h
  have hs4 := hm.slot4
  have hs5 := hm.slot5
  rw [hph] at hs4 hs5
  simp only [outBytes, ho] at hs5
  simp only [keyOf, hs4, hs5, keyStatus_keyOp]
  exact ha.keyStatus hm.frame.used_le (genRand_length hm.frame) ho hpos hph

/-- The key's entry, before the call. -/
def CallKCT (q : GenPoint) (u : State) : Prop :=
  ∃ s, KeyCT q s ∧ KeyRegs q.inputs u ∧ u.mem = writeFrame s.mem (keySp q.inputs) (keyValues q.inputs) ∧
    Keep keyArgRegs (allocated 80 s) u

theorem key_call_ct [Key.KeyProof] : RelCT isa (Two CallKCT) keyCall (fun _ _ => True) := by
  refine RelCT.callEx (k := Key.keyA) Key.KeyProof.correct Key.KeyProof.ct fun u₁ u₂ ⟨q, h₁, h₂, _⟩ => ?_
  obtain ⟨s₁, c₁, r₁, m₁, k₁⟩ := h₁
  obtain ⟨s₂, c₂, r₂, m₂, k₂⟩ := h₂
  obtain ⟨o₁, _, _, _, _, _, hm₁, _⟩ := id c₁
  obtain ⟨o₂, _, _, _, _, _, hm₂, _⟩ := id c₂
  have g₁ := hm₁.frame
  have g₂ := hm₂.frame
  have hu₁ : u₁.sp = keySp q.inputs := k₁.sp.trans (alloc80_sp g₁)
  have hu₂ : u₂.sp = keySp q.inputs := k₂.sp.trans (alloc80_sp g₂)
  obtain ⟨res₁, e₁⟩ := callK_res g₁ hu₁ r₁ m₁
  obtain ⟨res₂, e₂⟩ := callK_res g₂ hu₂ r₂ m₂
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := callK_args (s := s₁) hu₁ m₁
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := callK_args (s := s₂) hu₂ m₂
  refine ⟨kReads q.inputs, kWrites q.inputs, kReads q.inputs, kWrites q.inputs,
    callK_pre g₁ hu₁ r₁ m₁, callK_pre g₂ hu₂ r₂ m₂, ?_,
    key_covers_reads g₁ k₁.rd k₁.wr, key_covers_writes g₁ k₁.wr,
    key_covers_reads g₂ k₂.rd k₂.wr, key_covers_writes g₂ k₂.wr⟩
  obtain ⟨x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, x6₁, x7₁⟩ := r₁
  obtain ⟨x0₂, x1₂, x2₂, x3₂, x4₂, x5₂, x6₂, x7₂⟩ := r₂
  refine ⟨fun r hr => ?_, by simp only [State.withRegions_sp, State.callEntry_sp, hu₁, hu₂], fun i hi => ?_, ?_⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [callK_gpr (by decide), callK_gpr (by decide)]
    exacts [x0₁.trans x0₂.symm, x1₁.trans x1₂.symm, x2₁.trans x2₂.symm, x3₁.trans x3₂.symm, x4₁.trans x4₂.symm,
      x5₁.trans x5₂.symm, x6₁.trans x6₂.symm, x7₁.trans x7₂.symm]
  · match i, hi with
    | 0, _ => rw [b0, d0]
    | 1, _ => rw [b1, d1]
    | 2, _ => rw [b2, d2]
    | 3, _ => rw [b3, d3]
    | 4, _ => rw [b4, d4]
    | 5, _ => rw [b5, d5]
    | 6, _ => rw [b6, d6]
    | 7, _ => rw [b7, d7]
    | 8, _ => rw [b8, d8]
    | 9, _ => rw [b9, d9]
  · unfold Key.keyLeak
    rw [e₁, e₂, res₁, res₂, c₁.status, c₂.status]

/-- At the point, past the allocation of the key's frame. -/
def AllocKCT (q : GenPoint) (u : State) : Prop := ∃ s, KeyCT q s ∧ u = allocated 80 s

theorem key_run_ct [Key.KeyProof] : RelCT isa (Two KeyCT) (keyRun keyCall) (fun _ _ => True) := by
  unfold keyRun
  apply RelCT.alloc
  have ha : RelCT isa (Two AllocKCT) (.block keyArgs) (Two CallKCT) :=
    two_post (frame_ct (fun q => q.inputs) (fun q u ⟨s, h, e⟩ => by subst e; exact h.frame.x19)
      (by taint_decide))
      (fun q u ⟨s, hs, e⟩ => by
        subst e
        obtain ⟨o, _, _, _, _, _, hm, _⟩ := id hs
        exact WP.mono (key_args_ok hm.frame) fun _ ⟨⟨hr, hmem⟩, k⟩ => ⟨s, hs, hr, hmem, k⟩)
  refine (RelCT.seq ha key_call_ct).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocated, hsp]⟩

end VG.Proof.RsaKeyGen.AArch64.Generate
