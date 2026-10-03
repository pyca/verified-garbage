import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillState
import VerifiedGarbage.Proof.Argon2.Arm.CompressVerified
import VerifiedGarbage.Proof.Argon2.Arm.CompressLit

/-!
# Argon2 on ARMv7: calls of G in the filling loops

The filling loops call `vg_argon2_compress` with its arguments in registers,
`compress(r0, r1, r2, r3)`: G of the blocks at `r0` and `r1`, each a cell of
the memory matrix or a block of `scratch` from offset 4096 on (`GArg`), to
`scratch + o` (`r2`), with `scratch[0, 4096)` (`r3`) as its working space
(`ccall_ok`). It uses no stack.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Spec.Argon2 (Block blockAt compress)
open VG.Proof.Argon2.Arm (blk compressArm)

/-- `scratch`, as an address. -/
abbrev scrB (s₀ : State) : Addr := State.addr (scrP s₀)

/-- A block G may read: a cell of the matrix, or a block of `scratch` from 4096
on apart from the output at offset `o`. -/
def GArg (s₀ : State) (o : Nat) (p : BitVec 32) : Prop :=
  (∃ k < blocksN s₀, p = memP s₀ + BitVec.ofNat 32 (k * 1024)) ∨
    ∃ d, 4096 ≤ d ∧ d + 1024 ≤ 16384 ∧ (d + 1024 ≤ o ∨ o + 1024 ≤ d) ∧ p = scrP s₀ + BitVec.ofNat 32 d

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- What a call needs of a block it reads. -/
theorem GArg.facts {o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384) {p : BitVec 32} (h : GArg s₀ o p) :
    (∃ R ∈ [memR s₀, scrR s₀], ∃ off, State.addr p = R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len) ∧
    p.toNat + 1024 ≤ 2 ^ 32 ∧
    Region.Disjoint ⟨State.addr p, 1024⟩ ⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩ ∧
    Region.Disjoint ⟨State.addr p, 1024⟩ ⟨scrB s₀, 4096⟩ := by
  have hs := hp.scr_fits
  have hm := hp.mem_fits
  rcases h with ⟨k, hk, rfl⟩ | ⟨d, hd, hd', hdo, rfl⟩
  · have hk' : k * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
    have e := cell_addr hp hk
    have sub : Region.Sub ⟨State.addr (memP s₀ + BitVec.ofNat 32 (k * 1024)), 1024⟩ (memR s₀) := by
      rw [e]; exact cell_in_mem hk
    refine ⟨⟨memR s₀, by simp, k * 1024, e, hk'⟩, by rw [add_nat (by omega)]; omega, ?_, ?_⟩
    · exact (hp.mem_scr.sub_left sub).sub_right (Offset.sub_base _ ho')
    · exact (hp.mem_scr.sub_left sub).sub_right (Region.sub_prefix (by decide))
  · have e : State.addr (scrP s₀ + BitVec.ofNat 32 d) = scrB s₀ + BitVec.ofNat 64 d := scr_addr hp (by omega)
    refine ⟨⟨scrR s₀, by simp, d, e, hd'⟩, by rw [add_nat (by omega)]; omega, ?_, ?_⟩
    · rw [e]; exact Offset.disjoint _ hdo (by omega) (by omega)
    · rw [e]; exact Offset.disjoint_base _ hd (by omega)

/-- The regions G is given. -/
abbrev cRd (s : State) : List Region := [⟨State.addr (s.gpr .r0), 1024⟩, ⟨State.addr (s.gpr .r1), 1024⟩]
abbrev cWr (s₀ : State) (o : Nat) : List Region := [⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrB s₀, 4096⟩]

/-- What G needs, from the body: `compress(r0, r1, r2, r3)`, to `scratch + o`. -/
theorem ccall_pre {s : State} (h : Inv s₀ s) (h3 : s.gpr .r3 = scrP s₀) {o : Nat} (ho : 4096 ≤ o)
    (ho' : o + 1024 ≤ 16384) (h2 : s.gpr .r2 = scrP s₀ + BitVec.ofNat 32 o) (hx : GArg s₀ o (s.gpr .r0))
    (hy : GArg s₀ o (s.gpr .r1)) :
    compressArm.pre (s.callEntry.withRegions (cRd s) (cWr s₀ o)) ∧ Covers (cRd s ++ cWr s₀ o) (s.rd ++ s.wr) ∧
      Covers (cWr s₀ o) s.wr := by
  have hs := hp.scr_fits
  obtain ⟨⟨RX, hRX, oX, bX, lX⟩, fX, X_out, X_scr⟩ := hx.facts hp ho ho'
  obtain ⟨⟨RY, hRY, oY, bY, lY⟩, fY, Y_out, Y_scr⟩ := hy.facts hp ho ho'
  have eO : State.addr (scrP s₀ + BitVec.ofNat 32 o) = scrB s₀ + BitVec.ofNat 64 o := scr_addr hp (by omega)
  have memW : ∀ R ∈ [memR s₀, scrR s₀], R ∈ s.wr := fun R hR => by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact mem_mem hp
    · exact scr_mem hp
  have scrW : scrR s₀ ∈ s.wr := memW _ (by simp)
  have cX : Covers [⟨State.addr (s.gpr .r0), 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RX, memW _ hRX, oX, bX, lX⟩
  have cY : Covers [⟨State.addr (s.gpr .r1), 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RY, memW _ hRY, oY, bY, lY⟩
  have cO : Covers [⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨scrR s₀, scrW, o, rfl, ho'⟩
  have cW : Covers [⟨scrB s₀, 4096⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨scrR s₀, scrW, 0, by simp, by simp⟩
  have O_W : Region.Disjoint ⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩ ⟨scrB s₀, 4096⟩ :=
    Offset.disjoint_base _ ho (by omega)
  refine ⟨?_, (Covers.pair cX cY).right.append_left (Covers.pair cO cW).right, Covers.pair cO cW⟩
  · simp only [compressArm, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r1 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.r2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide),
      h2, h3, eO]
    refine ⟨trivial, trivial, O_W, X_out, X_scr, Y_out, Y_scr, fX, fY, by rw [add_nat (by omega)]; omega, by omega⟩

/-- A call of G from the body: `compress(r0, r1, r2, r3)`, to `scratch + o`. -/
theorem ccall_ok {s : State} (h : Inv s₀ s) (h3 : s.gpr .r3 = scrP s₀) {o : Nat} (ho : 4096 ≤ o)
    (ho' : o + 1024 ≤ 16384) (h2 : s.gpr .r2 = scrP s₀ + BitVec.ofNat 32 o) (hx : GArg s₀ o (s.gpr .r0))
    (hy : GArg s₀ o (s.gpr .r1)) {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → (∀ q ∈ preserved, q ≠ .lr → t.gpr q = s.gpr q) →
      Frame [⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrB s₀, 4096⟩] s.mem t.mem →
      blk t.mem (scrP s₀) o =
        compress (blockAt s.mem (State.addr (s.gpr .r0))) (blockAt s.mem (State.addr (s.gpr .r1))) → Q t) :
    WP isa Impl.Argon2.Arm.Derive.compressCall s Q := by
  have hs := hp.scr_fits
  obtain ⟨pre, cv, cw⟩ := ccall_pre hp h h3 ho ho' h2 hx hy
  refine WP.call (k := compressArm) Proof.Argon2.Arm.compress_verified'.1 pre cv cw
    (fun t hrd hwr hsp hf hcs _ hpost => ?_) (by lit_decide)
  simp only [compressArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r2 ∉ linkRegs by decide), h2] at hpost
  rw [Proof.Argon2.Arm.blockAt_eq (by rw [add_nat (by omega)]; omega), blk_shift] at hpost
  refine k t (h.step hsp (hcs .r11 (by decide) (by decide)) hrd hwr (hf.sub fun q hq => ?_)) hcs hf hpost
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨scrR s₀, by simp, Offset.sub_base _ ho'⟩
  · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩

end

end VG.Proof.Argon2.Arm.Derive
