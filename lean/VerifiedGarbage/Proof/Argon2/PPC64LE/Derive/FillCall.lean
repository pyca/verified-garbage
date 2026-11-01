module

import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Scratch
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Compress
import VerifiedGarbage.Proof.Argon2.PPC64LE.CompressLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Argon2.PPC64LE.CompressLit
meta import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Body
public import VerifiedGarbage.Proof.Argon2.Contract

/-!
# Argon2 on PPC64LE: calls of G in the filling loops

The filling loops call `vg_argon2_compress` with its arguments in registers,
`compress(r3, r4, r5, r6)`: G of the blocks at `r3` and `r4`, each a cell of
the memory matrix or a block of `scratch` from offset 4096 on (`GArg`), to
`scratch + o` (`r5`), with `scratch[0, 4096)` (`r6`) as its working space
(`ccall_ok`). It uses no stack.
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Spec.Argon2 (Block compress)

/-- A block G may read: a cell of the matrix, or a block of `scratch` from 4096
on apart from the output at offset `o`. -/
def GArg (s₀ : State) (o : Nat) (p : Addr) : Prop :=
  (∃ k < blocksN s₀, p = memP s₀ + BitVec.ofNat 64 (k * 1024)) ∨
    ∃ d, 4096 ≤ d ∧ d + 1024 ≤ 16384 ∧ (d + 1024 ≤ o ∨ o + 1024 ≤ d) ∧ p = scrP s₀ + BitVec.ofNat 64 d

theorem compress_noFrames : Impl.Argon2.PPC64LE.compress.noFrames = true := by lit_decide

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- What a call needs of a block it reads. -/
theorem GArg.facts {o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384) {p : Addr} (h : GArg s₀ o p) :
    (∃ R ∈ [memR s₀, scrR s₀], ∃ off, p = R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len) ∧
    Region.Disjoint ⟨p, 1024⟩ ⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩ ∧
    Region.Disjoint ⟨p, 1024⟩ ⟨scrP s₀, 4096⟩ := by
  rcases h with ⟨k, hk, rfl⟩ | ⟨d, hd, hd', hdo, rfl⟩
  · have hk' : k * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
    have sub : Region.Sub ⟨memP s₀ + BitVec.ofNat 64 (k * 1024), 1024⟩ (memR s₀) :=
      Offset.sub_base _ hk'
    refine ⟨⟨memR s₀, by simp, k * 1024, rfl, hk'⟩, ?_, ?_⟩
    · exact (hp.mem_scr.sub_left sub).sub_right (Offset.sub_base _ ho')
    · exact (hp.mem_scr.sub_left sub).sub_right (Region.sub_prefix (by decide))
  · refine ⟨⟨scrR s₀, by simp, d, rfl, hd'⟩, ?_, ?_⟩
    · exact Offset.disjoint _ hdo (by omega) (by omega)
    · exact Offset.disjoint_base _ hd (by omega)

/-- What a call of G from the body needs. -/
theorem ccall_pre {s : State} (h : Inv s₀ s) (h6 : s.gpr .r6 = scrP s₀) {o : Nat} (ho : 4096 ≤ o)
    (ho' : o + 1024 ≤ 16384) (h5 : s.gpr .r5 = scrP s₀ + BitVec.ofNat 64 o)
    (hx : GArg s₀ o (s.gpr .r3)) (hy : GArg s₀ o (s.gpr .r4)) :
    Proof.Argon2.PPC64LE.compressLocal.pre (s.callEntry.withRegions [⟨s.gpr .r3, 1024⟩, ⟨s.gpr .r4, 1024⟩]
        [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrP s₀, 4096⟩]) ∧
      Covers ([⟨s.gpr .r3, 1024⟩, ⟨s.gpr .r4, 1024⟩] ++ [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrP s₀, 4096⟩])
        (s.rd ++ s.wr) ∧
      Covers [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrP s₀, 4096⟩] s.wr := by
  obtain ⟨⟨RX, hRX, oX, bX, lX⟩, X_out, X_scr⟩ := hx.facts hp ho ho'
  obtain ⟨⟨RY, hRY, oY, bY, lY⟩, Y_out, Y_scr⟩ := hy.facts hp ho ho'
  have memW : ∀ R ∈ [memR s₀, scrR s₀], R ∈ s.wr := fun R hR => by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact mem_mem hp
    · exact scr_mem hp
  have scrW : scrR s₀ ∈ s.wr := memW _ (by simp)
  let cRd : List Region := [⟨s.gpr .r3, 1024⟩, ⟨s.gpr .r4, 1024⟩]
  let cWr : List Region := [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrP s₀, 4096⟩]
  have cX : Covers [⟨s.gpr .r3, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RX, memW _ hRX, oX, bX, lX⟩
  have cY : Covers [⟨s.gpr .r4, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RY, memW _ hRY, oY, bY, lY⟩
  have cO : Covers [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨scrR s₀, scrW, o, rfl, ho'⟩
  have cW : Covers [⟨scrP s₀, 4096⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨scrR s₀, scrW, 0, by simp, by simp⟩
  have O_W : Region.Disjoint ⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩ ⟨scrP s₀, 4096⟩ :=
    Offset.disjoint_base _ ho (by omega)
  have g : ∀ r, r ∉ linkRegs → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  have pre : Proof.Argon2.PPC64LE.compressLocal.pre (s.callEntry.withRegions cRd cWr) := by
    simp only [Proof.Argon2.PPC64LE.compressLocal, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide), g .r6 (by decide),
      h5, h6]
    exact ⟨rfl, rfl, O_W, X_scr, Y_scr⟩
  exact ⟨pre, (Covers.pair cX cY).right.append_left (Covers.pair cO cW).right, Covers.pair cO cW⟩

/-- A call of G from the body: `compress(r3, r4, r5, r6)`, to `scratch + o`. -/
theorem ccall_ok {s : State} (h : Inv s₀ s) (h6 : s.gpr .r6 = scrP s₀) {o : Nat} (ho : 4096 ≤ o)
    (ho' : o + 1024 ≤ 16384) (h5 : s.gpr .r5 = scrP s₀ + BitVec.ofNat 64 o)
    (hx : GArg s₀ o (s.gpr .r3)) (hy : GArg s₀ o (s.gpr .r4)) {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → (∀ q ∈ preserved, t.gpr q = s.gpr q) →
      Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrP s₀, 4096⟩] s.mem t.mem →
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 o) =
        compress (blockAt s.mem (s.gpr .r3)) (blockAt s.mem (s.gpr .r4)) → Q t) :
    WP isa Impl.Argon2.PPC64LE.Derive.compressCall s Q := by
  have g : ∀ r, r ∉ linkRegs → s.callEntry.gpr r = s.gpr r := fun r hr => State.callEntry_gpr s hr
  obtain ⟨pre, cv, cw⟩ := ccall_pre hp h h6 ho ho' h5 hx hy
  have O_W : Region.Disjoint ⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩ ⟨scrP s₀, 4096⟩ :=
    Offset.disjoint_base _ ho (by omega)
  refine WP.call (k := Proof.Argon2.PPC64LE.compressLocal) Proof.Argon2.PPC64LE.compress_correct pre cv cw
    (fun t hrd hwr hsp hf hcs _ post => ?_) compress_noFrames
  replace post : blockAt t.mem (s.gpr .r5) =
      compress (blockAt s.mem (s.gpr .r3)) (blockAt s.mem (s.gpr .r4)) := by
    simpa only [Proof.Argon2.PPC64LE.compressLocal, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide)] using post
  rw [h5] at post
  refine k t (h.step hsp (hcs _ (by decide)) (hcs _ (by decide))
    (fun r hr => hcs r (by revert hr; revert r; decide)) hrd hwr (hf.sub fun q hq => ?_)) hcs hf post
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨scrR s₀, by simp, Offset.sub_base _ ho'⟩
  · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩

end

end VG.Proof.Argon2.PPC64LE.Derive
