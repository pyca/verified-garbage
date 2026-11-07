module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.CTPoint
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.CTFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.CT
import VerifiedGarbage.Proof.EntropyRequest
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.CTPoint
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.CTFrame
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.CT
meta import VerifiedGarbage.Proof.EntropyRequest
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset

/-! # The calls' timing

The prime search's and the key's: their arguments are the same in two runs
at a point, and so is what their contracts let their timing depend on — the
search's status, consumption, request and trace, and the key's status, all
from the point's trace.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem frame_alloc_ct)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

theorem GenCTL.any {q : GenPoint} {s : State} (h : GenCTL q s) : AnyFrame q.inputs s :=
  let ⟨o, st, _, hl, _⟩ := h; ⟨o, _, st, hl.toGenFrame⟩

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
    word s.mem q.inputs.stp 24 = q.req ∧ SearchRegs q.inputs st u ∧
    u.mem = writeFrame s.mem (q.inputs.F - BitVec.ofNat 64 48) (callValues q.inputs q.used st) ∧
    Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (allocated 48 s) u

/-- The search's exponent and state words at its entry. -/
theorem callS_state {p : GenPublic} {original s u : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s) (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 208) (ha : SearchRegs p st u)
    (hm : u.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 48) (callValues p used st)) :
    Search.searchE (callS p used st u) = p.eB ∧
      Spec.Rsa.wordsAt (callS p used st u).mem (stackArg (callS p used st u) 5) 4 =
        [BitVec.ofNat 64 st.remaining, BitVec.ofNat 64 p.L, BitVec.ofNat 64 (primeEntropy p.L),
          word s.mem p.stp 24] := by
  have hf := h.input.cfacts
  have hfr := callS_frame hu hm
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨-, -, -, sT, -⟩ := hst
  obtain ⟨-, -, -, -, -, a5⟩ := callS_args (used := used) (st := st) hu hm
  obtain ⟨-, -, -, hcx, h8, -⟩ := ha
  have hword (d : Nat) (hd : d + 8 ≤ 56) : word (callS p used st u).mem p.stp d = word s.mem p.stp d :=
    hfr.readW (r := cS p) (Offset.contains_base _ hd (by have := hf.nT; omega))
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact sT) (by decide)
  refine ⟨?_, ?_⟩
  · simp only [Search.searchE, callS_gpr (show Reg.rcx ≠ .rsp by decide), callS_gpr (show Reg.r8 ≠ .rsp by decide),
      hcx, h8, toNat_ofNat_lt (show 8 < 2 ^ 64 by decide)]
    rw [← h.state.e]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hfr.bytes (R := ⟨p.stp + BitVec.ofNat 64 48, 8⟩) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact sT.sub_left rE_sub) (by show 8 ≤ 2 ^ 64; decide)
      (List.mem_range.mp hi)
  · rw [a5]
    show [word _ p.stp (8 * 0), word _ p.stp (8 * 1), word _ p.stp (8 * 2), word _ p.stp (8 * 3)] = _
    rw [hword _ (by decide), hword _ (by decide), hword _ (by decide), hword _ (by decide)]
    have h0 := h.state.remaining
    have h1 := h.state.len
    have h2 := h.state.cap
    simp only [Nat.reduceMul] at h0 h1 h2 ⊢
    rw [h0, h1, h2]

theorem search_call_ct (v : RoundImpl) : RelCT isa (Two CallSCT) (searchCall v) (fun _ _ => True) := by
  refine RelCT.callEx (k := Search.searchContract) (Search.search_correct v) (Search.search_constantTime v)
    fun u₁ u₂ ⟨q, h₁, h₂⟩ => ?_
  obtain ⟨o₁, st₁, s₁, a₁, l₁, w₁, r₁, m₁, k₁⟩ := h₁
  obtain ⟨o₂, st₂, s₂, a₂, l₂, w₂, r₂, m₂, k₂⟩ := h₂
  have hu₁ : u₁.gpr .rsp = q.inputs.sp - BitVec.ofNat 64 208 := by
    rw [k₁.gpr (by decide), allocated_rsp, l₁.rsp, F_48]
  have hu₂ : u₂.gpr .rsp = q.inputs.sp - BitVec.ofNat 64 208 := by
    rw [k₂.gpr (by decide), allocated_rsp, l₂.rsp, F_48]
  have hph : phaseWord st₁.phase = phaseWord st₂.phase := a₁.2.1.trans a₂.2.1.symm
  have hres₁ := callS_result l₁ hu₁ r₁ m₁
  have hres₂ := callS_result l₂ hu₂ r₂ m₂
  obtain ⟨e₁, ws₁⟩ := callS_state l₁ hu₁ r₁ m₁
  obtain ⟨e₂, ws₂⟩ := callS_state l₂ hu₂ r₂ m₂
  have hlen₁ : Search.searchLen (callS q.inputs q.used st₁ u₁) = q.inputs.L := by
    simp only [Search.searchLen, callS_gpr (show Reg.rsi ≠ .rsp by decide), r₁.2.1]
    exact toNat_ofNat_lt (by have := l₁.input.cfacts.len.2.1; omega)
  have hlen₂ : Search.searchLen (callS q.inputs q.used st₂ u₂) = q.inputs.L := by
    simp only [Search.searchLen, callS_gpr (show Reg.rsi ≠ .rsp by decide), r₂.2.1]
    exact toNat_ofNat_lt (by have := l₂.input.cfacts.len.2.1; omega)
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := callS_args (used := q.used) (st := st₁) hu₁ m₁
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := callS_args (used := q.used) (st := st₂) hu₂ m₂
  obtain ⟨di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ := r₁
  obtain ⟨di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ := r₂
  refine ⟨sReads q.inputs q.used st₁, sWrites q.inputs st₁, sReads q.inputs q.used st₂, sWrites q.inputs st₂,
    callS_pre l₁ hu₁ ⟨di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ m₁, callS_pre l₂ hu₂ ⟨di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ m₂, ?_,
    search_covers_reads l₁ k₁.2.1 k₁.2.2, search_covers_writes l₁ k₁.2.2,
    search_covers_reads l₂ k₂.2.1 k₂.2.2, search_covers_writes l₂ k₂.2.2, hu₁.trans hu₂.symm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, e₁.trans e₂.symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [callS_rsp hu₁, callS_rsp hu₂]
  · rw [callS_gpr (by decide), callS_gpr (by decide), di₁, di₂, outOf_ph hph]
  · rw [callS_gpr (by decide), callS_gpr (by decide), si₁, si₂]
  · rw [callS_gpr (by decide), callS_gpr (by decide), dx₁, dx₂]
  · rw [callS_gpr (by decide), callS_gpr (by decide), cx₁, cx₂]
  · rw [callS_gpr (by decide), callS_gpr (by decide), r8₁, r8₂]
  · rw [callS_gpr (by decide), callS_gpr (by decide), r9₁, r9₂]
  · match j, hj with
    | 0, _ => rw [b0, c0, plenOf_ph hph]
    | 1, _ => rw [b1, c1]
    | 2, _ => rw [b2, c2]
    | 3, _ => rw [b3, c3]
    | 4, _ => rw [b4, c4]
    | 5, _ => rw [b5, c5]
  · rw [ws₁, ws₂, a₁.2.2.1, a₂.2.2.1, w₁, w₂]
  · rw [hres₁, hres₂, a₁.status, a₂.status]
  · rw [hres₁, hres₂, a₁.cand, a₂.cand]
  · rw [hlen₁, hlen₂, hres₁, hres₂]
    exact Entropy.requested_congr (a₁.status.trans a₂.status.symm) (a₁.available.trans a₂.available.symm)
  · rw [hres₁, hres₂, a₁.prime, a₂.prime]

/-- A loop state at the point, past the allocation of the search's frame. -/
def AllocSCT (q : GenPoint) (u : State) : Prop := ∃ s, GenCTL q s ∧ u = allocated 48 s

theorem search_run_ct (v : RoundImpl) :
    RelCT isa (Two GenCTL) (searchRun (searchCall v)) (fun _ _ => True) := by
  unfold searchRun
  apply frame_alloc_ct
  have ha : RelCT isa (Two AllocSCT) (.block searchArgs) (Two CallSCT) :=
    two_post (RelCT.taint (A := taint) (genT' 48 []) (fun _ _ ⟨q, ⟨s, hs, e₁⟩, ⟨t, ht, e₂⟩⟩ => by
      subst e₁ e₂; exact alloc_agree (by decide) hs.any ht.any (fun _ h => absurd h List.not_mem_nil))
      (by taint_decide))
      (fun q u ⟨s, ⟨o, st, ha, hl, hw⟩, e⟩ => by
        subst e
        exact WP.mono (search_args_ok hl) fun _ ⟨hr, hm, k⟩ => ⟨o, st, s, ha, hl, hw, hr, hm, k⟩)
  refine (RelCT.seq ha (search_call_ct v)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩⟩

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
  ∃ s, KeyCT q s ∧ KeyRegs q.inputs u ∧
    u.mem = writeFrame s.mem (q.inputs.F - BitVec.ofNat 64 96) (keyValues q.inputs) ∧
    Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (allocated 96 s) u

theorem key_call_ct [Key.KeyProof] : RelCT isa (Two CallKCT) keyCall (fun _ _ => True) := by
  refine RelCT.callEx (k := Key.keyCtr) (Key.KeyProof.correct keyCode_mx) Key.KeyProof.ct
    fun u₁ u₂ ⟨q, h₁, h₂⟩ => ?_
  obtain ⟨s₁, c₁, r₁, m₁, k₁⟩ := h₁
  obtain ⟨s₂, c₂, r₂, m₂, k₂⟩ := h₂
  obtain ⟨o₁, _, _, _, _, _, hm₁, _⟩ := id c₁
  obtain ⟨o₂, _, _, _, _, _, hm₂, _⟩ := id c₂
  have g₁ := hm₁.frame
  have g₂ := hm₂.frame
  have hu₁ : u₁.gpr .rsp = q.inputs.sp - BitVec.ofNat 64 256 := by
    rw [k₁.gpr (by decide), allocated_rsp, g₁.rsp, F_96]
  have hu₂ : u₂.gpr .rsp = q.inputs.sp - BitVec.ofNat 64 256 := by
    rw [k₂.gpr (by decide), allocated_rsp, g₂.rsp, F_96]
  obtain ⟨res₁, e₁⟩ := callK_res g₁ hu₁ r₁ m₁
  obtain ⟨res₂, e₂⟩ := callK_res g₂ hu₂ r₂ m₂
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := callK_args (s := s₁) hu₁ m₁
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩ := callK_args (s := s₂) hu₂ m₂
  obtain ⟨di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ := r₁
  obtain ⟨di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ := r₂
  refine ⟨kReads q.inputs, kWrites q.inputs, kReads q.inputs, kWrites q.inputs,
    callK_pre g₁ hu₁ ⟨di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ m₁, callK_pre g₂ hu₂ ⟨di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ m₂, ?_,
    key_covers_reads g₁ k₁.2.1 k₁.2.2, key_covers_writes g₁ k₁.2.2,
    key_covers_reads g₂ k₂.2.1 k₂.2.2, key_covers_writes g₂ k₂.2.2, hu₁.trans hu₂.symm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [callK_rsp hu₁, callK_rsp hu₂], fun i hi => ?_, ?_⟩
  · rw [callK_gpr (by decide), callK_gpr (by decide), di₁, di₂]
  · rw [callK_gpr (by decide), callK_gpr (by decide), si₁, si₂]
  · rw [callK_gpr (by decide), callK_gpr (by decide), dx₁, dx₂]
  · rw [callK_gpr (by decide), callK_gpr (by decide), cx₁, cx₂]
  · rw [callK_gpr (by decide), callK_gpr (by decide), r8₁, r8₂]
  · rw [callK_gpr (by decide), callK_gpr (by decide), r9₁, r9₂]
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
    | 10, _ => rw [b10, d10]
    | 11, _ => rw [b11, d11]
  · unfold Key.keyLeak
    rw [e₁, e₂, res₁, res₂, c₁.status, c₂.status]

/-- At the point, past the allocation of the key's frame. -/
def AllocKCT (q : GenPoint) (u : State) : Prop := ∃ s, KeyCT q s ∧ u = allocated 96 s

theorem key_run_ct [Key.KeyProof] : RelCT isa (Two KeyCT) (keyRun keyCall) (fun _ _ => True) := by
  unfold keyRun
  apply frame_alloc_ct
  have ha : RelCT isa (Two AllocKCT) (.block keyArgs) (Two CallKCT) :=
    two_post (RelCT.taint (A := taint) (genT' 96 []) (fun _ _ ⟨q, ⟨s, hs, e₁⟩, ⟨t, ht, e₂⟩⟩ => by
      subst e₁ e₂; exact alloc_agree (by decide) hs.frame ht.frame (fun _ h => absurd h List.not_mem_nil))
      (by taint_decide))
      (fun q u ⟨s, hs, e⟩ => by
        subst e
        obtain ⟨o, _, _, _, _, _, hm, _⟩ := id hs
        exact WP.mono (key_args_ok hm.frame) fun _ ⟨hr, hmem, k⟩ => ⟨s, hs, hr, hmem, k⟩)
  refine (RelCT.seq ha key_call_ct).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩⟩

end VG.Proof.RsaKeyGen.X86_64.Generate
