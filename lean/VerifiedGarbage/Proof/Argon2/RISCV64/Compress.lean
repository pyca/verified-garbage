module

import VerifiedGarbage.Proof.Argon2.RISCV64.Copy
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Argon2.RISCV64.CompressLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
meta import VerifiedGarbage.Proof.Argon2.RISCV64.CompressLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Copy
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Wp
meta import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.RISCV64.Rounds

/-! # Argon2 compression G on RISC-V: correctness and constant time

`vg_argon2_compress` is an internal function, which only the derivation
calls: its contract, `compressLocal`, states that its pointers are 8-byte
aligned. -/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64

open VG VG.RISCV64 VG.Spec.Argon2
open VG.RISCV64.Wp (Upd wp_addi)

/-- The contract the proof is written against. -/
def compressLocal : Contract isa where
  pre s :=
    let x : Region := ⟨s.gpr .a0, 1024⟩
    let y : Region := ⟨s.gpr .a1, 1024⟩
    let out : Region := ⟨s.gpr .a2, 1024⟩
    let scratch : Region := ⟨s.gpr .a3, 4096⟩
    s.rd = [x, y] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ x.Disjoint scratch ∧ y.Disjoint scratch ∧
      (s.gpr .a0).toNat % 8 = 0 ∧ (s.gpr .a1).toNat % 8 = 0 ∧ (s.gpr .a2).toNat % 8 = 0 ∧
      (s.gpr .a3).toNat % 8 = 0
  post s t := blockAt t.mem (s.gpr .a2) =
    compress (blockAt s.mem (s.gpr .a0)) (blockAt s.mem (s.gpr .a1))
  pub s t := s.gpr .a0 = t.gpr .a0 ∧ s.gpr .a1 = t.gpr .a1 ∧
    s.gpr .a2 = t.gpr .a2 ∧ s.gpr .a3 = t.gpr .a3 ∧ s.sp = t.sp

theorem compress_ct : ConstantTime isa compressLocal.pre compressLocal.pub
    Impl.Argon2.RISCV64.compress := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A block unchanged by a frame disjoint from it. -/
theorem blockAt_frame {m m' : Mem} {rs : List Region} {x : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨x, 1024⟩ : Region).Disjoint r) : blockAt m' x = blockAt m x := by
  apply Vector.ext
  intro i hi
  show (blockAt m' x)[(⟨i, hi⟩ : Fin 128)] = (blockAt m x)[(⟨i, hi⟩ : Fin 128)]
  rw [blockAt_get, blockAt_get]
  exact hf.readW (r := ⟨x, 1024⟩) (Offset.contains_base x (by omega) (by omega)) hd (by decide)

/-- The base of the saves. -/
abbrev saveB (p : Addr) : Addr := p + BitVec.ofNat 64 2040

/-- The save area, past the two blocks. -/
abbrev saveR (p : Addr) : Region := ⟨p + BitVec.ofNat 64 2048, 40⟩

theorem saveB_off (p : Addr) (d : Nat) :
    saveB p + BitVec.ofNat 64 d = p + BitVec.ofNat 64 (2040 + d) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem saved_in : ∀ q ∈ Impl.Argon2.RISCV64.saved, 8 ≤ q.2 ∧ q.2 + 8 ≤ 8 + 40 := by decide

theorem saved_fits : ∀ q ∈ Impl.Argon2.RISCV64.saved, q.2 % 8 = 0 ∧ q.2 < 2048 := by decide

theorem saveR_eq (p : Addr) : (⟨saveB p + BitVec.ofNat 64 8, 40⟩ : Region) = saveR p := by
  rw [saveB_off]

theorem preserved_split : ∀ r ∈ .ra :: preserved, r ∈ Impl.Argon2.RISCV64.saved.map Prod.fst ∨
    (r ∉ roundRegs ∧ r ≠ .t0 ∧ r ≠ .t1 ∧ r ∉ Impl.Argon2.RISCV64.saved.map Prod.fst) := by decide

/-- `t0 := scratch + 2040`, the base of the saves and restores. -/
theorem base_ok (s : State) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' .t0 (saveB (s.gpr .a3)) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi .t0 .a3 2040 :: is)) s Q :=
  wp_addi (imm := 2040) (by decide) k

theorem compress_wp (s : State) (hs : compressLocal.pre s) :
    WP isa Impl.Argon2.RISCV64.compress s fun t => compressLocal.post s t ∧
      (∀ r ∈ .ra :: preserved, t.gpr r = s.gpr r) := by
  obtain ⟨hrd, hwr, hout, hx, hy, ax, ay, ao, ap⟩ := hs
  obtain ⟨p, hp⟩ : ∃ p, s.gpr .a3 = p := ⟨_, rfl⟩
  rw [hp] at hwr hout hx hy ap
  have scr : Scratch s p := ⟨hp, by simp [hwr], ap⟩
  unfold Impl.Argon2.RISCV64.compress
  apply WP.seq
  rw [show Impl.Argon2.RISCV64.save = .addi .t0 .a3 2040 :: Spill.saveCode .t0 Impl.Argon2.RISCV64.saved
    from rfl, List.cons_append]
  refine base_ok s fun s₀' u₀ => ?_
  have b0 : s₀'.gpr .t0 = saveB p := by rw [u₀.gpr, hp]
  refine Spill.save_ok (by rw [b0]; exact Spill.al8 ap (by decide)) saved_fits
    (fun q hq => by
      rw [b0, u₀.wr, saveB_off]
      exact scr.write (by have := saved_in q hq; omega)) ?_
  generalize e₀ : ({ s₀' with
    mem := Spill.saveMem s₀'.mem (s₀'.gpr .t0) s₀'.gpr Impl.Argon2.RISCV64.saved } : State) = s₀
  have m₀ : s₀.mem = Spill.saveMem s₀'.mem (s₀'.gpr .t0) s₀'.gpr Impl.Argon2.RISCV64.saved := by
    rw [← e₀]
  have gr₀ : s₀.gpr = s₀'.gpr := by rw [← e₀]
  have rd₀ : s₀.rd = s.rd := by rw [← e₀]; exact u₀.rd
  have wr₀ : s₀.wr = s.wr := by rw [← e₀]; exact u₀.wr
  have f₀ : Frame [saveR p] s.mem s₀.mem := by
    have := Spill.saveMem_frame saved_in (by decide) s₀'.mem (s₀'.gpr .t0) s₀'.gpr
    rw [b0, saveR_eq] at this
    rw [m₀, b0, ← u₀.mem]
    exact this
  have g₀ : ∀ r, r ≠ .t0 → s₀'.gpr r = s.gpr r := fun r hr => u₀.other r hr
  have sv₀ : Spill.Saved (saveB p) s.gpr Impl.Argon2.RISCV64.saved s₀.mem := by
    intro q hq
    have := Spill.saveMem_saved (by decide) s₀'.mem (s₀'.gpr .t0) s₀'.gpr q hq
    rw [b0] at this
    have hne : ∀ q ∈ Impl.Argon2.RISCV64.saved, q.1 ≠ .t0 := by decide
    rw [m₀, b0, this, g₀ _ (hne q hq)]
  have xs : (⟨s.gpr .a0, 1024⟩ : Region).Disjoint (saveR p) := hx.sub_right (Offset.sub_base _ (by omega))
  have ys : (⟨s.gpr .a1, 1024⟩ : Region).Disjoint (saveR p) := hy.sub_right (Offset.sub_base _ (by omega))
  have bx : blockAt s₀.mem (s.gpr .a0) = blockAt s.mem (s.gpr .a0) := blockAt_frame f₀ (by simpa using xs)
  have by' : blockAt s₀.mem (s.gpr .a1) = blockAt s.mem (s.gpr .a1) := blockAt_frame f₀ (by simpa using ys)
  have scr₀ : Scratch s₀ p := ⟨by rw [gr₀, g₀ .a3 (by decide), hp], by simp [wr₀, hwr], ap⟩
  have inputs : Inputs s₀ (s.gpr .a0) (s.gpr .a1) p :=
    ⟨by rw [gr₀, g₀ .a0 (by decide)], by rw [gr₀, g₀ .a1 (by decide)], by simp [rd₀, wr₀, hrd],
      by simp [rd₀, wr₀, hrd], hx, hy, ax, ay⟩
  refine (init_prefix 128 (by decide) s₀ scr₀ inputs).mono ?_
  rintro s₁ ⟨hinit, hf1, hk1⟩
  obtain ⟨horig, hwork⟩ := initialized_blocks hinit
  have scr1 := scr₀.of_copy hk1
  have sv₁ : Spill.Saved (saveB p) s.gpr Impl.Argon2.RISCV64.saved s₁.mem :=
    sv₀.frame_in saved_in hf1 (by rw [saveR_eq]; simpa using Offset.disjoint_base p (by omega) (by omega))
  apply WP.seq
  refine (rounds_ok rowIndex (List.finRange 8) s₁ scr1).mono ?_
  rintro s₂ ⟨hrow, hf2, hk2⟩
  apply WP.seq
  refine (rounds_ok colIndex (List.finRange 8) s₂ (scr1.of_keeps hk2)).mono ?_
  rintro s₃ ⟨hcol, hf3, hk3⟩
  have scr3 := (scr1.of_keeps hk2).of_keeps hk3
  have d1024 : ∀ r ∈ [(⟨off p 1024, 1024⟩ : Region)],
      Region.Disjoint ⟨saveB p + BitVec.ofNat 64 8, 40⟩ r := by
    rw [saveR_eq]; simpa using Offset.disjoint p (by omega) (by omega) (by omega)
  have sv₃ : Spill.Saved (saveB p) s.gpr Impl.Argon2.RISCV64.saved s₃.mem :=
    (sv₁.frame_in saved_in hf2 d1024).frame_in saved_in hf3 d1024
  have hout3 : s₃.gpr .a2 = s.gpr .a2 := by
    rw [hk3.1 .a2 (by decide), hk2.1 .a2 (by decide), hk1.1 .a2 (by decide) (by decide), gr₀,
      g₀ .a2 (by decide)]
  have hw3 : s₃.wr = s.wr := hk3.2.2.1.trans (hk2.2.2.1.trans (hk1.2.2.1.trans wr₀))
  apply WP.block_append
  refine (finish_prefix 128 (by decide) s₃ scr3 hout3 (by rw [hw3, hwr]; simp) hout.symm ao).mono ?_
  rintro s₄ ⟨hfinish, hf4, hk4⟩
  have sv₄ : Spill.Saved (saveB p) s.gpr Impl.Argon2.RISCV64.saved s₄.mem :=
    sv₃.frame_in saved_in hf4 (by
      rw [saveR_eq]
      simpa using (hout.sub_right (Offset.sub_base p (d := 2048) (n := 40) (by omega))).symm)
  have scr4 := scr3.of_copy hk4
  rw [show Impl.Argon2.RISCV64.restore = .addi .t0 .a3 2040 ::
    Spill.restoreCode .t0 Impl.Argon2.RISCV64.saved from rfl]
  refine base_ok s₄ fun s₅ u₅ => ?_
  have b5 : s₅.gpr .t0 = saveB p := by rw [u₅.gpr, scr4.reg]
  refine WP.mono (Spill.restore_wp (b := .t0) (B := saveB p) (Spill.al8 ap (by decide)) b5 saved_fits
    (by decide) (fun q hq => by
      rw [u₅.rd, u₅.wr, saveB_off]
      exact scr4.read (by have := saved_in q hq; omega)) (by rw [u₅.mem]; exact sv₄)) fun t ht => ⟨?_, ?_⟩
  · have ho : blockAt s₃.mem p = blockAt s₁.mem p :=
      blockAt_frame (hf2.trans hf3) (by simpa using Offset.base_disjoint p (by omega) (by omega))
    rw [horig] at ho
    have he := written_block hfinish
    rw [hcol, hrow, hwork, ho, bx, by'] at he
    show blockAt t.mem (s.gpr .a2) = _
    rw [ht.mem, u₅.mem, he]
    rfl
  · intro r hr
    rcases preserved_split r hr with h | ⟨h1, h2, h3, h4⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
      exact ht.gpr q hq
    · rw [ht.other r h4, u₅.other r h2, hk4.1 r h2 h3, hk3.1 r h1, hk2.1 r h1, hk1.1 r h2 h3, gr₀, g₀ r h2]

theorem compress_correct (s : State) (hs : compressLocal.pre s) :
    ∃ tr t, Exec isa Impl.Argon2.RISCV64.compress s tr t ∧ abiPreserved s t ∧
      compressLocal.post s t := by
  obtain ⟨tr, t, he, hp, hk⟩ := compress_wp s hs
  exact ⟨tr, t, he, ⟨fun r hr => hk r (List.mem_cons_of_mem _ hr), Exec.sp he,
    hk .ra (List.mem_cons_self ..)⟩, hp⟩

end VG.Proof.Argon2.RISCV64
