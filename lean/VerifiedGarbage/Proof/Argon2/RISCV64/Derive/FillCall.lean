module

import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Scratch
public import VerifiedGarbage.Proof.Argon2.RISCV64.Compress
import VerifiedGarbage.Proof.Argon2.RISCV64.CompressLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Argon2.RISCV64.CompressLit
meta import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Body
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline

/-!
# Argon2 on RISC-V: calls of G in the filling loops

The filling loops call `vg_argon2_compress` with its arguments in registers,
`compress(a0, a1, a2, a3)`: G of the blocks at `a0` and `a1`, each a cell of
the memory matrix or a block of `scratch` below offset 4096 (`GArg`), to
`scratch + o` (`a2`), with `scratch[4096, 8192)` (`a3`) as its working space
(`ccall_ok`). It uses no stack.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.Spec.Argon2 (Block compress)

/-- G's working space. -/
abbrev gwP (s₀ : State) : Addr := scrP s₀ + BitVec.ofNat 64 4096

/-- A block G may read: a cell of the matrix, or a block of `scratch` below
4096 apart from the output at offset `o`. -/
def GArg (s₀ : State) (o : Nat) (p : Addr) : Prop :=
  (∃ k < blocksN s₀, p = memP s₀ + BitVec.ofNat 64 (k * 1024)) ∨
    ∃ d, d + 1024 ≤ 4096 ∧ d % 8 = 0 ∧ (d + 1024 ≤ o ∨ o + 1024 ≤ d) ∧
      p = scrP s₀ + BitVec.ofNat 64 d

theorem compress_noFrames : Impl.Argon2.RISCV64.compress.noFrames = true := by lit_decide

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- What a call needs of a block it reads. -/
theorem GArg.facts {o : Nat} (ho' : o + 1024 ≤ 4096) {p : Addr} (h : GArg s₀ o p) :
    (∃ R ∈ [memR s₀, scrR s₀], ∃ off, p = R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len) ∧
    Region.Disjoint ⟨p, 1024⟩ ⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩ ∧
    Region.Disjoint ⟨p, 1024⟩ ⟨gwP s₀, 4096⟩ ∧ p.toNat % 8 = 0 := by
  rcases h with ⟨k, hk, rfl⟩ | ⟨d, hd', hd8, hdo, rfl⟩
  · have hk' : k * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
    have sub : Region.Sub ⟨memP s₀ + BitVec.ofNat 64 (k * 1024), 1024⟩ (memR s₀) :=
      Offset.sub_base _ hk'
    refine ⟨⟨memR s₀, by simp, k * 1024, rfl, hk'⟩, ?_, ?_, ?_⟩
    · exact (hp.mem_scr.sub_left sub).sub_right (Offset.sub_base _ (by omega))
    · exact (hp.mem_scr.sub_left sub).sub_right (Offset.sub_base _ (by decide))
    · exact al_add (by decide) (.inr hp.mem_al) (by omega)
  · refine ⟨⟨scrR s₀, by simp, d, rfl, by simp only; omega⟩, ?_, ?_, ?_⟩
    · exact Offset.disjoint _ hdo (by omega) (by omega)
    · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    · exact al_add (by decide) (.inr hp.scr_al) hd8

/-- What a call of G from the body needs. -/
theorem ccall_pre {s : State} (h : Inv s₀ s) (h3 : s.gpr .a3 = gwP s₀) {o : Nat}
    (ho' : o + 1024 ≤ 4096) (ho8 : o % 8 = 0) (h2 : s.gpr .a2 = scrP s₀ + BitVec.ofNat 64 o)
    (hx : GArg s₀ o (s.gpr .a0)) (hy : GArg s₀ o (s.gpr .a1)) :
    Proof.Argon2.RISCV64.compressLocal.pre (s.callEntry.withRegions [⟨s.gpr .a0, 1024⟩, ⟨s.gpr .a1, 1024⟩]
        [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨gwP s₀, 4096⟩]) ∧
      Covers ([⟨s.gpr .a0, 1024⟩, ⟨s.gpr .a1, 1024⟩] ++ [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨gwP s₀, 4096⟩])
        (s.rd ++ s.wr) ∧
      Covers [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨gwP s₀, 4096⟩] s.wr := by
  obtain ⟨⟨RX, hRX, oX, bX, lX⟩, X_out, X_scr, X_al⟩ := hx.facts hp ho'
  obtain ⟨⟨RY, hRY, oY, bY, lY⟩, Y_out, Y_scr, Y_al⟩ := hy.facts hp ho'
  have memW : ∀ R ∈ [memR s₀, scrR s₀], R ∈ s.wr := fun R hR => by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact mem_mem hp
    · exact scr_mem hp
  have scrW : scrR s₀ ∈ s.wr := memW _ (by simp)
  let cRd : List Region := [⟨s.gpr .a0, 1024⟩, ⟨s.gpr .a1, 1024⟩]
  let cWr : List Region := [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨gwP s₀, 4096⟩]
  have cX : Covers [⟨s.gpr .a0, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RX, memW _ hRX, oX, bX, lX⟩
  have cY : Covers [⟨s.gpr .a1, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RY, memW _ hRY, oY, bY, lY⟩
  have cO : Covers [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨scrR s₀, scrW, o, rfl, by simp only; omega⟩
  have cW : Covers [⟨gwP s₀, 4096⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨scrR s₀, scrW, 4096, rfl, by simp⟩
  have O_W : Region.Disjoint ⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩ ⟨gwP s₀, 4096⟩ :=
    Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have g : ∀ r, r ∉ linkRegs → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  have pre : Proof.Argon2.RISCV64.compressLocal.pre (s.callEntry.withRegions cRd cWr) := by
    simp only [Proof.Argon2.RISCV64.compressLocal, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, g .a0 (by decide), g .a1 (by decide), g .a2 (by decide), g .a3 (by decide),
      h2, h3]
    exact ⟨rfl, rfl, O_W, X_scr, Y_scr, X_al, Y_al, h.scr_al (by decide) ho8,
      h.scr_al (by decide) (by decide)⟩
  exact ⟨pre, (VG.Covers.pair cX cY).right.append_left (VG.Covers.pair cO cW).right,
    VG.Covers.pair cO cW⟩

/-- A call of G from the body: `compress(a0, a1, a2, a3)`, to `scratch + o`. -/
theorem ccall_ok {s : State} (h : Inv s₀ s) (h3 : s.gpr .a3 = gwP s₀) {o : Nat}
    (ho' : o + 1024 ≤ 4096) (ho8 : o % 8 = 0) (h2 : s.gpr .a2 = scrP s₀ + BitVec.ofNat 64 o)
    (hx : GArg s₀ o (s.gpr .a0)) (hy : GArg s₀ o (s.gpr .a1)) {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → (∀ q ∈ preserved, t.gpr q = s.gpr q) →
      Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨gwP s₀, 4096⟩] s.mem t.mem →
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 o) =
        compress (blockAt s.mem (s.gpr .a0)) (blockAt s.mem (s.gpr .a1)) → Q t) :
    WP isa Impl.Argon2.RISCV64.Derive.compressCall s Q := by
  have g : ∀ r, r ∉ linkRegs → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  obtain ⟨pre, cv, cw⟩ := ccall_pre hp h h3 ho' ho8 h2 hx hy
  refine WP.call (k := Proof.Argon2.RISCV64.compressLocal) Proof.Argon2.RISCV64.compress_correct pre cv cw
    (fun t hrd hwr hsp hf hcs _ post => ?_) compress_noFrames
  replace post : blockAt t.mem (s.gpr .a2) =
      compress (blockAt s.mem (s.gpr .a0)) (blockAt s.mem (s.gpr .a1)) := by
    simpa only [Proof.Argon2.RISCV64.compressLocal, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, g .a0 (by decide), g .a1 (by decide), g .a2 (by decide)] using post
  rw [h2] at post
  refine k t (h.step hsp (hcs _ (by decide)) (hcs _ (by decide)) (hcs _ (by decide))
    (fun r hr => hcs r (by revert hr; revert r; decide)) hrd hwr (hf.sub fun q hq => ?_)) hcs hf post
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨scrR s₀, by simp, Offset.sub_base _ (by omega)⟩
  · exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩

end

end VG.Proof.Argon2.RISCV64.Derive
