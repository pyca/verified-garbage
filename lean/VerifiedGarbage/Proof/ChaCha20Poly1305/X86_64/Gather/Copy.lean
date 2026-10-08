import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Copy
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealGather

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: copying a slice

Untrusted: everything here is checked by Lean. `copyBytes` copies `rcx`
bytes from `rsi` to `rdi`, 16 at a time through `xmm0` (SSE2's `movdqu`) and
then one at a time (`copyBytes_ok`), as AES-GCM's short path does through
`xmm4` (`Proof/AesGcm/X86_64/Short/Copy.lean`, whose setup and byte loop it
shares); the buffers do not overlap.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (copyBytes)
open VG.Proof.AesGcm.X86_64 (ea_idx succ_ofNat bytesAt_succ in_of_covers copyBody copyStep_ok src_kept length_bytesAt
  writeBytes_frame' bytesAt_add ofNat_add_ofNat sub_beq bytesAt_frame)
open VG.Proof.AesGcm.X86_64.Short (writeW_readW128 CopyPre copySetup_ok in_of_covers16)
open VG.Spec.Aes (bytesAt)

/-- The 16-byte loop's body. -/
abbrev copy16Body : List Instr :=
  [.movdquLoad .xmm0 srcB, .movdquStore dstB .xmm0, .alu .add .r10 (imm 16), .alu .cmp .r10 (.reg .r8)]

theorem copy16Step_ok (s : State) {S D : Addr} {i k : Nat} (hs : s.gpr .rsi = S) (hd : s.gpr .rdi = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hk : s.gpr .r8 = BitVec.ofNat 64 k)
    (r : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 16) (w : InRegions s.wr (D + BitVec.ofNat 64 i) 16) :
    ∃ s', runBlock isa copy16Body s = some s' ∧
      s'.mem = writeBytes s.mem (D + BitVec.ofNat 64 i) (bytesAt s.mem (S + BitVec.ofNat 64 i) 16) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 16 ∧
      s'.zf = some (BitVec.ofNat 64 i + 16 - BitVec.ofNat 64 k == 0) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e₁ := ea_idx s .rsi hs hi
  have e₂ := ea_idx s .rdi hd hi
  refine ⟨_, by
    simp only [copy16Body, srcB, dstB, imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, State.load128, State.store128, State.ea, e₁, r, ite_true, Option.map_some, Option.bind_some,
      gpr_setXmm, rd_setXmm, wr_setXmm, mem_setXmm, xmm_setXmm_self, e₂, w]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    exact writeW_readW128 _ _ _ _
  · simp [gpr_setReg, gpr_arithFlags, hi]
  · simp [gpr_setReg, gpr_arithFlags, zf_arithFlags, hi, hk]
  · intro r h₁; simp [gpr_setReg, gpr_arithFlags, h₁]

/-- What `copyBytes` leaves. -/
def CopyPost (s : State) (S D : Addr) (n : Nat) (s' : State) : Prop :=
  s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
    (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem copyBytes_ok (s : State) {S D : Addr} {n : Nat} (h : CopyPre s S D n) :
    WP isa copyBytes s (CopyPost s S D n) := by
  have hn63 := h.lt
  refine WP.seq (WP.mono (copySetup_ok s h.rcx h.lt) fun s₁ ⟨r10₁, r8₁, zf₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_)
  -- After the 16-byte loop: the first `16 ⌊n / 16⌋` bytes copied.
  let q := n / 16
  have mid : WP isa (.ite .e (.block []) (.loop (.block copy16Body) .ne)) s₁ fun t =>
      t.gpr .r10 = BitVec.ofNat 64 (16 * q) ∧ t.mem = writeBytes s.mem D (bytesAt s.mem S (16 * q)) ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
    refine WP.ite (decide (16 * q = 0)) (by simp only [eval, zf₁, q]) (fun hz => ?_) (fun hz => ?_)
    · have hq : 16 * q = 0 := of_decide_eq_true hz
      refine WP.block_nil ⟨by rw [r10₁, hq], by rw [m₁, hq]; simp [bytesAt, writeBytes_nil],
        fun r a b c => g₁ r b c, rd₁, wr₁⟩
    · have hq : 0 < q := by have := of_decide_eq_false hz; omega
      refine WP.loop (M := isa) (body := .block copy16Body) (c := .ne)
        (fun (k : Nat) (t : State) => ∃ j, k = q - j ∧ j < q ∧ t.gpr .r10 = BitVec.ofNat 64 (16 * j) ∧
          t.mem = writeBytes s.mem D (bytesAt s.mem S (16 * j)) ∧
          (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → t.gpr r = s.gpr r) ∧
          t.gpr .r8 = BitVec.ofNat 64 (16 * q) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (q - 0) _
        ⟨0, rfl, hq, by rw [r10₁], by rw [m₁]; simp [bytesAt, writeBytes_nil], fun r a b c => g₁ r b c,
          r8₁, rd₁, wr₁⟩
      rintro k t ⟨j, rfl, hj, r10, mem, g, r8, rd, wr⟩
      have hj16 : 16 * j + 16 ≤ n := by omega
      obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := copy16Step_ok t
        (by rw [g _ (by decide) (by decide) (by decide), h.rsi])
        (by rw [g _ (by decide) (by decide) (by decide), h.rdi]) r10 r8
        (by rw [rd, wr]; exact in_of_covers16 h.rd hj16 (by omega))
        (by rw [wr]; exact in_of_covers16 h.wr hj16 (by omega))
      refine WP.of_runBlock ⟨t', run', ?_⟩
      have hlen : (bytesAt s.mem S (16 * j)).length = 16 * j := length_bytesAt _ _ _
      have hsrc : bytesAt t.mem (S + BitVec.ofNat 64 (16 * j)) 16 =
          bytesAt s.mem (S + BitVec.ofNat 64 (16 * j)) 16 := by
        rw [mem]
        refine bytesAt_frame (writeBytes_frame' s.mem hlen) (fun r hr => ?_) (by decide)
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.disj.sub_left (Offset.sub_base S hj16)).sub_right (Region.sub_prefix (by omega))
      have hmem : t'.mem = writeBytes s.mem D (bytesAt s.mem S (16 * (j + 1))) := by
        rw [mem', hsrc, mem, show 16 * (j + 1) = 16 * j + 16 by omega, bytesAt_add]
        conv => lhs; rw [show D + BitVec.ofNat 64 (16 * j) = D + BitVec.ofNat 64 (bytesAt s.mem S (16 * j)).length
          by rw [hlen]]
        exact writeBytes_append s.mem D (bytesAt s.mem S (16 * j)) (bytesAt s.mem (S + BitVec.ofNat 64 (16 * j)) 16)
          (by rw [length_bytesAt, length_bytesAt]; omega)
      have hz : t'.zf = some (decide (j + 1 = q)) := by
        rw [zf', show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat, sub_beq (by omega) (by omega)]
        congr 1; simp only [decide_eq_decide]; omega
      have gg : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → t'.gpr r = s.gpr r := fun r a b c => by
        rw [g' r c, g r a b c]
      have r10'' : t'.gpr .r10 = BitVec.ofNat 64 (16 * (j + 1)) := by
        rw [r10', show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]; congr 1
      by_cases he : j + 1 = q
      · left
        refine ⟨by simp [eval, hz, he], by rw [r10'', he], by rw [hmem, he], gg, by rw [rd', rd],
          by rw [wr', wr]⟩
      · right
        refine ⟨by simp [eval, hz, he], q - (j + 1), by omega, j + 1, rfl, by omega, r10'', hmem, gg,
          by rw [g' _ (by decide), r8], by rw [rd', rd], by rw [wr', wr]⟩
  refine WP.seq (WP.mono mid fun s₂ ⟨r10₂, m₂, g₂, rd₂, wr₂⟩ => ?_)
  -- The last `n mod 16` bytes, one at a time.
  have hcx : s₂.gpr .rcx = BitVec.ofNat 64 n := by rw [g₂ _ (by decide) (by decide) (by decide), h.rcx]
  refine WP.seq (WP.mono (Q := fun (t : State) => t.zf = some (decide (16 * q = n)) ∧ t.gpr = s₂.gpr ∧
      t.mem = s₂.mem ∧ t.rd = s₂.rd ∧ t.wr = s₂.wr) ?_ fun s₃ ⟨zf₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  · apply WP.of_runBlock
    refine ⟨_, by xrun [r10₂, hcx], ?_⟩
    refine ⟨?_, by simp [gpr_arithFlags], rfl, rfl, rfl⟩
    simp only [zf_arithFlags]; rw [sub_beq (by omega) (by omega)]
  refine WP.ite (decide (16 * q = n)) (by simp only [eval, zf₃]) (fun hz => ?_) (fun hz => ?_)
  · have hq : 16 * q = n := of_decide_eq_true hz
    exact WP.block_nil ⟨by rw [m₃, m₂, hq], fun r a b c => by rw [g₃, g₂ r a b c], by rw [rd₃, rd₂],
      by rw [wr₃, wr₂]⟩
  · have hq : 16 * q < n := by have := of_decide_eq_false hz; omega
    refine WP.loop (M := isa) (body := .block copyBody) (c := .ne)
      (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
        t.mem = writeBytes s.mem D (bytesAt s.mem S i) ∧
        (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_
      (n - 16 * q) _
      ⟨16 * q, rfl, hq, by rw [g₃, r10₂], by rw [m₃, m₂], fun r a b c => by rw [g₃, g₂ r a b c],
        by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩
    rintro k t ⟨i, rfl, hi, r10, mem, g, rd, wr⟩
    obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := copyStep_ok t
      (by rw [g _ (by decide) (by decide) (by decide), h.rsi])
      (by rw [g _ (by decide) (by decide) (by decide), h.rdi]) r10
      (by rw [g _ (by decide) (by decide) (by decide), h.rcx])
      (by rw [rd, wr]; exact in_of_covers h.rd hi (by omega))
      (by rw [wr]; exact in_of_covers h.wr hi (by omega))
    refine WP.of_runBlock ⟨t', run', ?_⟩
    have hlen : (bytesAt s.mem S i).length = i := length_bytesAt _ _ _
    have hmem : t'.mem = writeBytes s.mem D (bytesAt s.mem S (i + 1)) := by
      rw [mem', mem, src_kept h.disj hi h.lt _ hlen, bytesAt_succ,
        writeBytes_snoc s.mem D (bytesAt s.mem S i) _ (by rw [hlen]; omega), hlen]
    have hz : t'.zf = some (decide (i + 1 = n)) := by
      rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    have gg : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → t'.gpr r = s.gpr r := fun r a b c => by
      rw [g' r a c, g r a b c]
    by_cases he : i + 1 = n
    · left
      exact ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
    · right
      exact ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', succ_ofNat],
        hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.ChaCha20Poly1305.X86_64.Gather
