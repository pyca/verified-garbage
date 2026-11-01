module

import VerifiedGarbage.Proof.Argon2.PPC64LE.Copy
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import Mathlib.Tactic.IntervalCases
import VerifiedGarbage.Proof.Argon2.PPC64LE.CompressLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Argon2.PPC64LE.CompressLit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Argon2.PPC64LE.Copy
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Rounds

/-! # Argon2 compression G on PPC64LE: correctness, constant time, `Verified` -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE

open VG VG.PPC64LE VG.Spec.Argon2

/-- The contract the proof is written against. -/
def compressLocal : Contract isa where
  pre s :=
    let x : Region := ⟨s.gpr .r3, 1024⟩
    let y : Region := ⟨s.gpr .r4, 1024⟩
    let out : Region := ⟨s.gpr .r5, 1024⟩
    let scratch : Region := ⟨s.gpr .r6, 4096⟩
    s.rd = [x, y] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ x.Disjoint scratch ∧ y.Disjoint scratch
  post s t := blockAt t.mem (s.gpr .r5) =
    compress (blockAt s.mem (s.gpr .r3)) (blockAt s.mem (s.gpr .r4))
  pub s t := s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4 ∧
    s.gpr .r5 = t.gpr .r5 ∧ s.gpr .r6 = t.gpr .r6 ∧ s.sp = t.sp

def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x6000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]
  wr := [⟨0x3000, 1024⟩, ⟨0x4000, 4096⟩]

theorem compress_implies : compressLocal.Implies (compressContract PPC64LE.abi) := by
  sig_implies [compressContract, compressSig, compressLocal, PPC64LE.abi, PPC64LE.argRegs]
    [satState] using satState

theorem compress_ct : ConstantTime isa compressLocal.pre compressLocal.pub
    Impl.Argon2.PPC64LE.compress := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A block unchanged by a frame disjoint from it. -/
theorem blockAt_frame {m m' : Mem} {x : Addr} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨x, 1024⟩ : Region).Disjoint r) : blockAt m' x = blockAt m x := by
  apply Vector.ext
  intro i hi
  show (blockAt m' x)[(⟨i, hi⟩ : Fin 128)] = (blockAt m x)[(⟨i, hi⟩ : Fin 128)]
  rw [blockAt_get, blockAt_get]
  exact hf.readW (r := ⟨x, 1024⟩) (Offset.contains_base x (by omega) (by omega)) hd (by decide)

/-- The save area, past the two blocks. -/
abbrev saveR (p : Addr) : Region := ⟨p + BitVec.ofNat 64 2048, 72⟩

theorem saved_in : ∀ q ∈ Impl.Argon2.PPC64LE.saved, 2048 ≤ q.2 ∧ q.2 + 8 ≤ 2048 + 72 := by decide

theorem preserved_split : ∀ r ∈ preserved, r ∈ Impl.Argon2.PPC64LE.saved.map Prod.fst ∨
    (r ∉ roundRegs ∧ r ≠ .r0 ∧ r ≠ .r22 ∧ r ∉ Impl.Argon2.PPC64LE.saved.map Prod.fst) := by decide

theorem compress_wp (s : State) (hs : compressLocal.pre s) :
    WP isa Impl.Argon2.PPC64LE.compress s fun t => compressLocal.post s t ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) := by
  obtain ⟨hrd, hwr, hout, hx, hy⟩ := hs
  set p := s.gpr .r6 with hp
  have scr : Scratch s p := ⟨rfl, by simp [hwr]⟩
  unfold Impl.Argon2.PPC64LE.compress
  apply WP.seq
  rw [show Impl.Argon2.PPC64LE.save = Spill.saveCode .r6 Impl.Argon2.PPC64LE.saved from rfl]
  refine Spill.save_ok (by decide) (by decide) (fun q hq => scr.write (by have := saved_in q hq; omega)) ?_
  set s₀ : State := { s with mem := Spill.saveMem s.mem (s.gpr .r6) s.gpr Impl.Argon2.PPC64LE.saved }
  have f₀ : Frame [saveR p] s.mem s₀.mem := Spill.saveMem_frame saved_in (by decide) _ _ _
  have sv₀ : Spill.Saved p s.gpr Impl.Argon2.PPC64LE.saved s₀.mem :=
    Spill.saveMem_saved (by decide) _ _ _
  have xs : (⟨s.gpr .r3, 1024⟩ : Region).Disjoint (saveR p) := hx.sub_right (Offset.sub_base _ (by omega))
  have ys : (⟨s.gpr .r4, 1024⟩ : Region).Disjoint (saveR p) := hy.sub_right (Offset.sub_base _ (by omega))
  have bx : blockAt s₀.mem (s.gpr .r3) = blockAt s.mem (s.gpr .r3) := blockAt_frame f₀ (by simpa using xs)
  have by' : blockAt s₀.mem (s.gpr .r4) = blockAt s.mem (s.gpr .r4) := blockAt_frame f₀ (by simpa using ys)
  have scr₀ : Scratch s₀ p := ⟨rfl, scr.wr⟩
  have inputs : Inputs s₀ (s.gpr .r3) (s.gpr .r4) p :=
    ⟨rfl, rfl, by simp [s₀, hrd], by simp [s₀, hrd], hx, hy⟩
  refine (init_prefix 128 (by decide) s₀ scr₀ inputs).mono ?_
  rintro s₁ ⟨hinit, hf1, hk1⟩
  obtain ⟨horig, hwork⟩ := initialized_blocks hinit
  have scr1 := scr₀.of_copy hk1
  have sv₁ : Spill.Saved p s.gpr Impl.Argon2.PPC64LE.saved s₁.mem :=
    sv₀.frame_in saved_in hf1 (by simpa using Offset.disjoint_base p (by omega) (by omega))
  apply WP.seq
  refine (rounds_ok rowIndex (List.finRange 8) s₁ scr1).mono ?_
  rintro s₂ ⟨hrow, hf2, hk2⟩
  apply WP.seq
  refine (rounds_ok colIndex (List.finRange 8) s₂ (scr1.of_keeps hk2)).mono ?_
  rintro s₃ ⟨hcol, hf3, hk3⟩
  have scr3 := (scr1.of_keeps hk2).of_keeps hk3
  have d1024 : ∀ r ∈ [(⟨off p 1024, 1024⟩ : Region)], Region.Disjoint (saveR p) r := by
    simpa using Offset.disjoint p (by omega) (by omega) (by omega)
  have sv₃ : Spill.Saved p s.gpr Impl.Argon2.PPC64LE.saved s₃.mem :=
    (sv₁.frame_in saved_in hf2 d1024).frame_in saved_in hf3 d1024
  have hout3 : s₃.gpr .r5 = s.gpr .r5 := by
    rw [hk3.1 .r5 (by decide), hk2.1 .r5 (by decide), hk1.1 .r5 (by decide) (by decide)]
  have hw3 : s₃.wr = s.wr := hk3.2.2.1.trans (hk2.2.2.1.trans hk1.2.2.1)
  apply WP.block_append
  refine (finish_prefix 128 (by decide) s₃ scr3 hout3 (by rw [hw3, hwr]; simp) hout.symm).mono ?_
  rintro s₄ ⟨hfinish, hf4, hk4⟩
  have sv₄ : Spill.Saved p s.gpr Impl.Argon2.PPC64LE.saved s₄.mem :=
    sv₃.frame_in saved_in hf4 (by simpa using (hout.sub_right (Offset.sub_base p (d := 2048) (n := 72)
      (by omega))).symm)
  rw [show Impl.Argon2.PPC64LE.restore = Spill.restoreCode .r6 Impl.Argon2.PPC64LE.saved from rfl]
  refine WP.mono (Spill.restore_wp (by decide) (scr3.of_copy hk4).reg (by decide) (by decide)
    (fun q hq => (scr3.of_copy hk4).read (by have := saved_in q hq; omega)) sv₄) fun t ht => ⟨?_, ?_⟩
  · have ho : blockAt s₃.mem p = blockAt s₁.mem p :=
      blockAt_frame (hf2.trans hf3) (by simpa using Offset.base_disjoint p (by omega) (by omega))
    rw [horig] at ho
    have he := written_block hfinish
    rw [hcol, hrow, hwork, ho, bx, by'] at he
    show blockAt t.mem (s.gpr .r5) = _
    rw [ht.mem, he]
    rfl
  · intro r hr
    rcases preserved_split r hr with h | ⟨h1, h2, h3, h4⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
      exact ht.gpr q hq
    · rw [ht.other r h4, hk4.1 r h2 h3, hk3.1 r h1, hk2.1 r h1, hk1.1 r h2 h3]

theorem compress_correct (s : State) (hs : compressLocal.pre s) :
    ∃ tr t, Exec isa Impl.Argon2.PPC64LE.compress s tr t ∧ abiPreserved s t ∧
      compressLocal.post s t := by
  obtain ⟨tr, t, he, hp, hk⟩ := compress_wp s hs
  exact ⟨tr, t, he, ⟨hk, Exec.sp he, Exec.lr he (by lit_decide) (by rw [← Code.allInstrs_eq]; lit_decide)⟩, hp⟩

theorem compress_verified : Verified PPC64LE.target Impl.Argon2.PPC64LE.compress
    (Proof.Argon2.compressContract PPC64LE.abi) :=
  Verified.of_correct compress_correct compress_ct compress_implies

end VG.Proof.Argon2.PPC64LE
