import VerifiedGarbage.Proof.AesGcm.X86_64.Loops

/-!
# AES-GCM streaming encryption out of place, x86-64: copying bytes

Untrusted: everything here is checked by Lean. `copyLoop_ok` for any number
of bytes below 2⁶⁴ (`copyLoopL_ok`), as the plaintext left may be.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

/-- What `copyLoop` needs of the state: `LoopPre`, with fewer than 2⁶⁴ bytes. -/
structure CopyPre (s : State) (S D : Addr) (n : Nat) : Prop where
  rsi : s.gpr .rsi = S
  rdi : s.gpr .rdi = D
  rcx : s.gpr .rcx = BitVec.ofNat 64 n
  pos : 1 ≤ n
  lt : n < 2 ^ 64
  rd : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, n⟩] s.wr
  disj : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩

/-- The source byte `i` is not overwritten by the copy so far. -/
theorem src_keptL {m : Mem} {S D : Addr} {n i : Nat} (hd : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) (hi : i < n)
    (hn : n < 2 ^ 64) (xs : List Byte) (hxs : xs.length = i) :
    writeBytes m D xs (S + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i) :=
  (writeBytes_frame m D xs (R := ⟨D, i⟩) (by rw [hxs]; exact Region.contains_self _ _)) _
    fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hd _ (Offset.contains_base S (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)

theorem copyLoopL_ok (s : State) {S D : Addr} {n : Nat} (h : CopyPre s S D n) :
    WP isa copyLoop s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r10₁, g₁⟩ : ∃ s₁, runBlock isa [.mov32 .r10 (imm 0)] s = some s₁ ∧
      s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ s₁ = s.setReg .r10 (BitVec.setWidth 64 (BitVec.ofNat 32 0)) :=
    ⟨_, by simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32], by simp [gpr_setReg], rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  subst g₁
  refine WP.loop (M := isa) (body := .block copyBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem D (bytesAt s.mem S i) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, h.pos, r10₁, by simp [bytesAt, writeBytes_nil, mem_setReg],
      fun r h₁ h₂ => by simp [gpr_setReg, h₂], rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r10, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := copyStep_ok t
    (by rw [g _ (by decide) (by decide), h.rsi]) (by rw [g _ (by decide) (by decide), h.rdi]) r10
    (by rw [g _ (by decide) (by decide), h.rcx])
    (by rw [rd, wr]; exact in_of_covers h.rd hi h.lt)
    (by rw [wr]; exact in_of_covers h.wr hi h.lt)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (bytesAt s.mem S i).length = i := by simp [bytesAt]
  have hmem : t'.mem = writeBytes s.mem D (bytesAt s.mem S (i + 1)) := by
    rw [mem', mem, src_keptL h.disj hi h.lt _ hlen, bytesAt_succ,
      writeBytes_snoc s.mem D (bytesAt s.mem S i) _ (by rw [hlen]; have := h.lt; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = n)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by have := h.lt; omega) (by have := h.lt; omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : i + 1 = n
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', succ_ofNat],
      hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.AesGcm.X86_64.StreamTo
