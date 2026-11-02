module

import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Scratch
public import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Contract
import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Correct
import VerifiedGarbage.Proof.Argon2.RISCV64.CompressLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Argon2.RISCV64.CompressLit
meta import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Body
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Blake2.Stream

/-!
# Argon2 on RISC-V: the derivation's calls of H′

`hcall_ok`: `vg_argon2_hprime(a0, a1, a2, a3, a4)` from the body, with
`scratch` as its working space, an input in the memory matrix or H′'s input
in the frame, and an output in the memory matrix or `out`, by H′'s proof
(`HPrime.code_correct`) and `WP.call`: it keeps the invariant and writes
only its output and `scratch`.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.Spec.Blake2 (bytesAt)

theorem hPrime_noFrames : Impl.Argon2.RISCV64.HPrime.code.noFrames = true := by lit_decide

/-- The bytes of a region a frame's regions miss are kept. -/
theorem bytes_keep {rs : List Region} {m m' : Mem} (f : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hR : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n :=
  Proof.Blake2.bytesAt_congr fun _ hi => f.bytes (R := ⟨p, n⟩) hd hR hi

section
variable {s₀ : State} (hp : DPre s₀)
include hp

omit hp in
theorem inR_stk : Region.Sub (inR s₀) (stkR0 s₀) := stk_sub (by decide)

/-- H′'s input in the frame is outside the buffers. -/
theorem in_disj {R : Region} (hR : R ∈ [memR s₀, scrR s₀, outR s₀]) : (inR s₀).Disjoint R :=
  (hp.stk_all R (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h <;> simp [h])).sub_left inR_stk

omit hp in
theorem frame_mem : ⟨at' s₀ 0, 320⟩ ∈ (entry s₀).wr := by rw [entry_wr]; simp

/-- What a call of H′ from the body needs. -/
theorem hcall_pre {s : State} (h : Inv s₀ s) (a4 : s.gpr .a4 = scrP s₀)
    (hin : ∃ R ∈ [memR s₀, inR s₀], ∃ off, s.gpr .a0 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .a1).toNat ≤ R.len)
    (hout : ∃ R ∈ [memR s₀, outR s₀], ∃ off, s.gpr .a2 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .a3).toNat ≤ R.len)
    (hL : (s.gpr .a1).toNat < 2 ^ 32) (hO : 1 ≤ (s.gpr .a3).toNat ∧ (s.gpr .a3).toNat < 2 ^ 32) :
    HPrime.localContract.pre (s.callEntry.withRegions [⟨s.gpr .a0, (s.gpr .a1).toNat⟩]
        [⟨s.gpr .a2, (s.gpr .a3).toNat⟩, scrR s₀]) ∧
      Covers ([⟨s.gpr .a0, (s.gpr .a1).toNat⟩] ++ [⟨s.gpr .a2, (s.gpr .a3).toNat⟩, scrR s₀]) (s.rd ++ s.wr) ∧
      Covers [⟨s.gpr .a2, (s.gpr .a3).toNat⟩, scrR s₀] s.wr ∧
      (Region.Sub ⟨s.gpr .a2, (s.gpr .a3).toNat⟩ (memR s₀) ∨
        Region.Sub ⟨s.gpr .a2, (s.gpr .a3).toNat⟩ (outR s₀)) := by
  have g : ∀ r, r ∉ linkRegs → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  let I : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
  let O : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  have hin' : Region.Sub I (memR s₀) ∨ Region.Sub I (inR s₀) := by
    obtain ⟨R, hR, off, hb, hl⟩ := hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    have : Region.Sub I R := by
      show Region.Sub ⟨s.gpr .a0, _⟩ _
      rw [hb]; exact Offset.sub_base _ hl
    rcases hR with rfl | rfl
    · exact .inl this
    · exact .inr this
  have hout' : Region.Sub O (memR s₀) ∨ Region.Sub O (outR s₀) := by
    obtain ⟨R, hR, off, hb, hl⟩ := hout
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    have : Region.Sub O R := by
      show Region.Sub ⟨s.gpr .a2, _⟩ _
      rw [hb]; exact Offset.sub_base _ hl
    rcases hR with rfl | rfl
    · exact .inl this
    · exact .inr this
  have Iw : I.Disjoint (scrR s₀) := by
    rcases hin' with hi | hi
    · exact hp.mem_scr.sub_left hi
    · exact (in_disj hp (R := scrR s₀) (by simp)).sub_left hi
  have Ow : O.Disjoint (scrR s₀) := by
    rcases hout' with ho | ho
    · exact hp.mem_scr.sub_left ho
    · exact hp.scr_out.symm.sub_left ho
  have pre : HPrime.localContract.pre (s.callEntry.withRegions [I] [O, scrR s₀]) := by
    simp only [HPrime.localContract, HPrime.inputR, HPrime.outputR, HPrime.workR,
      State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      g .a0 (by decide), g .a1 (by decide), g .a2 (by decide), g .a3 (by decide), g .a4 (by decide), a4]
    exact ⟨rfl, rfl, hL, hO.1, hO.2, h.sal, Iw, Ow⟩
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
    refine VG.Covers.append_left ?_ (VG.Covers.right wrs)
    refine VG.Covers.right (Covers.of_sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨R, hR, off, hb, hl⟩ := hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact ⟨memR s₀, by rw [h.wr, entry_wr, hp.wr]; simp, off, hb, hl⟩
    · exact ⟨⟨at' s₀ 0, 320⟩, by rw [h.wr]; exact frame_mem, off, hb, by
        show off + (s.gpr .a1).toNat ≤ 320; simp only at hl; omega⟩
  exact ⟨pre, cov, wrs, hout'⟩

/-- `hprime(a0, a1, a2, a3, a4)` from the body. -/
theorem hcall_ok {s : State} (h : Inv s₀ s) (a4 : s.gpr .a4 = scrP s₀)
    (hin : ∃ R ∈ [memR s₀, inR s₀], ∃ off, s.gpr .a0 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .a1).toNat ≤ R.len)
    (hout : ∃ R ∈ [memR s₀, outR s₀], ∃ off, s.gpr .a2 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .a3).toNat ≤ R.len)
    (hL : (s.gpr .a1).toNat < 2 ^ 32) (hO : 1 ≤ (s.gpr .a3).toNat ∧ (s.gpr .a3).toNat < 2 ^ 32)
    {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → (∀ r ∈ preserved, t.gpr r = s.gpr r) →
      Frame [⟨s.gpr .a2, (s.gpr .a3).toNat⟩, scrR s₀] s.mem t.mem →
      bytesAt t.mem (s.gpr .a2) (s.gpr .a3).toNat =
        Spec.Argon2.hPrime (s.gpr .a3).toNat (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) → Q t) :
    WP isa Impl.Argon2.RISCV64.Derive.hPrimeCall s Q := by
  have g : ∀ r, r ∉ linkRegs → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  obtain ⟨pre, cov, wrs, hout'⟩ := hcall_pre hp h a4 hin hout hL hO
  refine WP.call (k := HPrime.localContract) HPrime.code_correct pre cov wrs ?_ hPrime_noFrames
  intro t rd wr sp' fr cs _ post
  simp only [HPrime.localContract, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    g .a0 (by decide), g .a1 (by decide), g .a2 (by decide), g .a3 (by decide)] at post
  refine k t (h.step sp' (cs _ (by decide)) (cs _ (by decide)) (cs _ (by decide))
    (fun r hr => cs r (by revert hr; revert r; decide)) rd wr (fr.sub fun r hr => ?_)) cs fr post
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rcases hout' with ho | ho
    · exact ⟨memR s₀, by simp, ho⟩
    · exact ⟨outR s₀, by simp, ho⟩
  · exact ⟨scrR s₀, by simp, fun _ h => h⟩

end

end VG.Proof.Argon2.RISCV64.Derive
