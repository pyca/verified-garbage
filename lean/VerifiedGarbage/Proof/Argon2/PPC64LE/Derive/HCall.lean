module

public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Scratch
public import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Contract
import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Correct
import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Argon2 on PPC64LE: the derivation's calls of H′

`hcall_ok`: `vg_argon2_hprime(r3, r4, r5, r6, r7)` from the body, with
`scratch` as its working space, an input in the memory matrix or H′'s input
in the frame, and an output in the memory matrix or `out`, by H′'s proof
(`HPrime.code_correct`) and `WP.callF`: it keeps the invariant and writes
only its output, `scratch` and the calls' frames.
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Spec.Blake2 (bytesAt)

theorem hPrime_fdepth : Impl.Argon2.PPC64LE.HPrime.code.fdepth = 1 := by lit_decide
theorem hPrime_pushFrames : pushFrames Impl.Argon2.PPC64LE.HPrime.code = true := by lit_decide

/-- The bytes of a region a frame's regions miss are kept. -/
theorem bytes_keep {rs : List Region} {m m' : Mem} (f : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hR : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n :=
  Proof.Blake2.bytesAt_congr fun _ hi => f.bytes (R := ⟨p, n⟩) hd hR hi

section
variable {s₀ : State} (hp : DPre s₀)
include hp

omit hp in
theorem callR_stk : Region.Sub (callR s₀) (stkR0 s₀) := by
  have e : B s₀ = B s₀ + BitVec.ofNat 64 0 := (BitVec.add_zero _).symm
  show Region.Sub ⟨B s₀, 48⟩ _
  rw [e]; exact stk_sub (by decide)

omit hp in
theorem inR_stk : Region.Sub (inR s₀) (stkR0 s₀) := stk_sub (by decide)

/-- The calls' frames are outside the buffers. -/
theorem call_disj {R : Region} (hR : R ∈ [memR s₀, scrR s₀, outR s₀]) : (callR s₀).Disjoint R :=
  (hp.stk_all R (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h <;> simp [h])).sub_left callR_stk

/-- H′'s input in the frame is outside the buffers. -/
theorem in_disj {R : Region} (hR : R ∈ [memR s₀, scrR s₀, outR s₀]) : (inR s₀).Disjoint R :=
  (hp.stk_all R (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h <;> simp [h])).sub_left inR_stk

omit hp in
theorem in_call : (inR s₀).Disjoint (callR s₀) := by
  have e : B s₀ = B s₀ + BitVec.ofNat 64 0 := (BitVec.add_zero _).symm
  show Region.Disjoint _ ⟨B s₀, 48⟩
  rw [e]; exact Offset.disjoint _ (by decide) (by decide) (by decide)

omit hp in
theorem frame_mem : ⟨at' s₀ 80, 304⟩ ∈ (entry s₀).wr := by rw [entry_wr]; simp

/-- What a call of H′ from the body needs. -/
theorem hcall_pre {s : State} (h : Inv s₀ s) (r7 : s.gpr .r7 = scrP s₀)
    (hin : ∃ R ∈ [memR s₀, inR s₀], ∃ off, s.gpr .r3 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .r4).toNat ≤ R.len)
    (hout : ∃ R ∈ [memR s₀, outR s₀], ∃ off, s.gpr .r5 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .r6).toNat ≤ R.len)
    (hL : (s.gpr .r4).toNat < 2 ^ 32) (hO : 1 ≤ (s.gpr .r6).toNat ∧ (s.gpr .r6).toNat < 2 ^ 32) :
    HPrime.localContract.pre (s.callEntry.withRegions [⟨s.gpr .r3, (s.gpr .r4).toNat⟩]
        [⟨s.gpr .r5, (s.gpr .r6).toNat⟩, scrR s₀]) ∧
      Covers ([⟨s.gpr .r3, (s.gpr .r4).toNat⟩] ++ [⟨s.gpr .r5, (s.gpr .r6).toNat⟩, scrR s₀]) (s.rd ++ s.wr) ∧
      Covers [⟨s.gpr .r5, (s.gpr .r6).toNat⟩, scrR s₀] s.wr ∧
      (Region.Sub ⟨s.gpr .r5, (s.gpr .r6).toNat⟩ (memR s₀) ∨
        Region.Sub ⟨s.gpr .r5, (s.gpr .r6).toNat⟩ (outR s₀)) := by
  have hsp : 48 ≤ s.sp.toNat := by
    rw [h.sp, show E s₀ = s₀.sp - BitVec.ofNat 64 336 from rfl,
      toNat_sub_ofNat' (by have := hp.sp_lo; omega)]
    have := hp.sp_lo; omega
  have g : ∀ r, r ∉ linkRegs → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  let I : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
  let O : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  have stk : below s.sp 48 = callR s₀ := by rw [h.sp, callR_eq]
  have hin' : Region.Sub I (memR s₀) ∨ Region.Sub I (inR s₀) := by
    obtain ⟨R, hR, off, hb, hl⟩ := hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    have : Region.Sub I R := by
      show Region.Sub ⟨s.gpr .r3, _⟩ _
      rw [hb]; exact Offset.sub_base _ hl
    rcases hR with rfl | rfl
    · exact .inl this
    · exact .inr this
  have hout' : Region.Sub O (memR s₀) ∨ Region.Sub O (outR s₀) := by
    obtain ⟨R, hR, off, hb, hl⟩ := hout
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    have : Region.Sub O R := by
      show Region.Sub ⟨s.gpr .r5, _⟩ _
      rw [hb]; exact Offset.sub_base _ hl
    rcases hR with rfl | rfl
    · exact .inl this
    · exact .inr this
  -- The input, the output and `scratch` against each other and the stack.
  have Iw : I.Disjoint (scrR s₀) := by
    rcases hin' with hi | hi
    · exact hp.mem_scr.sub_left hi
    · exact (in_disj hp (R := scrR s₀) (by simp)).sub_left hi
  have Ow : O.Disjoint (scrR s₀) := by
    rcases hout' with ho | ho
    · exact hp.mem_scr.sub_left ho
    · exact hp.scr_out.symm.sub_left ho
  have sI : (callR s₀).Disjoint I := by
    rcases hin' with hi | hi
    · exact (call_disj hp (R := memR s₀) (by simp)).sub_right hi
    · exact in_call.symm.sub_right hi
  have sO : (callR s₀).Disjoint O := by
    rcases hout' with ho | ho
    · exact (call_disj hp (R := memR s₀) (by simp)).sub_right ho
    · exact (call_disj hp (R := outR s₀) (by simp)).sub_right ho
  have sW : (callR s₀).Disjoint (scrR s₀) := call_disj hp (R := scrR s₀) (by simp)
  have pre : HPrime.localContract.pre (s.callEntry.withRegions [I] [O, scrR s₀]) := by
    simp only [HPrime.localContract, HPrime.inputR, HPrime.outputR, HPrime.workR, HPrime.stackR,
      State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide),
      g .r6 (by decide), g .r7 (by decide), r7, stk]
    exact ⟨rfl, rfl, hL, hO.1, hO.2, hsp, Iw, Ow, sI, sO, sW⟩
  have scrIn : scrR s₀ ∈ s.wr := by rw [h.wr]; exact scr_mem hp
  have wrs : Covers [O, scrR s₀] s.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · obtain ⟨R, hR, off, hb, hl⟩ := hout
      refine ⟨R, ?_, off, hb, hl⟩
      rw [h.wr, entry_wr, hp.wr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl <;> simp
    · exact ⟨scrR s₀, scrIn, 0, by simp, by simp⟩
  have cov : Covers ([I] ++ [O, scrR s₀]) (s.rd ++ s.wr) := by
    refine Covers.append_left ?_ (Covers.right wrs)
    refine Covers.right (Covers.of_sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨R, hR, off, hb, hl⟩ := hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact ⟨memR s₀, by rw [h.wr, entry_wr, hp.wr]; simp, off, hb, hl⟩
    · exact ⟨⟨at' s₀ 80, 304⟩, by rw [h.wr]; exact frame_mem, off, hb, by
        show off + (s.gpr .r4).toNat ≤ 304; simp only at hl; omega⟩
  exact ⟨pre, cov, wrs, hout'⟩

/-- `hprime(r3, r4, r5, r6, r7)` from the body. -/
theorem hcall_ok {s : State} (h : Inv s₀ s) (r7 : s.gpr .r7 = scrP s₀)
    (hin : ∃ R ∈ [memR s₀, inR s₀], ∃ off, s.gpr .r3 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .r4).toNat ≤ R.len)
    (hout : ∃ R ∈ [memR s₀, outR s₀], ∃ off, s.gpr .r5 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .r6).toNat ≤ R.len)
    (hL : (s.gpr .r4).toNat < 2 ^ 32) (hO : 1 ≤ (s.gpr .r6).toNat ∧ (s.gpr .r6).toNat < 2 ^ 32)
    {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → (∀ r ∈ preserved, t.gpr r = s.gpr r) →
      Frame [⟨s.gpr .r5, (s.gpr .r6).toNat⟩, scrR s₀, callR s₀] s.mem t.mem →
      bytesAt t.mem (s.gpr .r5) (s.gpr .r6).toNat =
        Spec.Argon2.hPrime (s.gpr .r6).toNat (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) → Q t) :
    WP isa Impl.Argon2.PPC64LE.Derive.hPrimeCall s Q := by
  have g : ∀ r, r ∉ linkRegs → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  have stk : below s.sp 48 = callR s₀ := by rw [h.sp, callR_eq]
  obtain ⟨pre, cov, wrs, hout'⟩ := hcall_pre hp h r7 hin hout hL hO
  refine WP.callF (k := HPrime.localContract) HPrime.code_correct pre cov wrs ?_
    (by rw [hPrime_fdepth]; decide) hPrime_pushFrames
  intro t rd wr sp' frame cs post
  simp only [HPrime.localContract, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    g .r3 (by decide), g .r4 (by decide), g .r5 (by decide), g .r6 (by decide)] at post
  rw [hPrime_fdepth, stk] at frame
  have fr : Frame [⟨s.gpr .r5, (s.gpr .r6).toNat⟩, scrR s₀, callR s₀] s.mem t.mem := by simpa using frame
  refine k t (h.step sp' (cs _ (by decide)) (cs _ (by decide))
    (fun r hr => cs r (by revert hr; revert r; decide)) rd wr (fr.sub fun r hr => ?_)) cs fr post
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hout' with ho | ho
    · exact ⟨memR s₀, by simp, ho⟩
    · exact ⟨outR s₀, by simp, ho⟩
  · exact ⟨scrR s₀, by simp, fun _ h => h⟩
  · exact ⟨callR s₀, by simp, fun _ h => h⟩

end

end VG.Proof.Argon2.PPC64LE.Derive
