import VerifiedGarbage.Impl.AesGcm.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.AesGcm.X86_64.Blocks
import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Dec
import VerifiedGarbage.Proof.Aes.X86_64.Variant
import VerifiedGarbage.Proof.Aes.X86_64.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Gcm.X86_64.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Impl.Gcm.X86_64.Stitch
import VerifiedGarbage.Impl.Gcm.X86_64.StitchZ
import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Loops`. -/
section

/-!
# AES-GCM on x86-64: the byte loops

Untrusted: everything here is checked by Lean. `copyLoop` copies `rcx`
bytes from `rsi` to `rdi`, and `xorLoop` XORs `rcx` bytes at `rsi` into those
at `rdi`, a byte at a time with the index in `r10` (`copyLoop_ok`,
`xorLoop_ok`); the buffers do not overlap.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

theorem ea_idx (s : State) (b : Reg) {B : Addr} (hb : s.gpr b = B) {i : Nat}
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) :
    s.gpr b + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 (0 : Int) = B + BitVec.ofNat 64 i := by
  rw [hb, hi, BitVec.mul_one]; simp

theorem succ_ofNat (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    bytesAt m p (i + 1) = bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [bytesAt, List.range_succ]

/-- Byte `i` of a region `⟨p, n⟩`, `i < n`, is in it. -/
theorem in_of_covers {rs : List Region} {p : Addr} {n i : Nat} (h : Covers [⟨p, n⟩] rs) (hi : i < n)
    (hn : n < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 i) 1 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base p (by omega) (by omega)⟩

/-- What the loops need of the state. -/
structure LoopPre (s : State) (S D : Addr) (n : Nat) : Prop where
  rsi : s.gpr .rsi = S
  rdi : s.gpr .rdi = D
  rcx : s.gpr .rcx = BitVec.ofNat 64 n
  pos : 1 ≤ n
  lt : n < 2 ^ 63
  rd : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, n⟩] s.wr
  disj : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩

/-! ## `copyLoop` -/

abbrev copyBody : List Instr :=
  [.movzx8 .rax srcB, .store8 dstB .rax, .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rcx)]

theorem copyStep_ok (s : State) {S D : Addr} {i n : Nat} (hs : s.gpr .rsi = S) (hd : s.gpr .rdi = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hn : s.gpr .rcx = BitVec.ofNat 64 n)
    (r : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa VG.Proof.AesGcm.X86_64.copyBody s = some s' ∧
      s'.mem = s.mem.writeW (D + BitVec.ofNat 64 i) (s.mem (S + BitVec.ofNat 64 i)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 n == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e₁ := VG.Proof.AesGcm.X86_64.ea_idx s .rsi hs hi
  have e₂ := VG.Proof.AesGcm.X86_64.ea_idx s .rdi hd hi
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.reduceGT, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, BitVec.reduceEq, not_false_eq_true, not_true_eq_false, Bool.not_true, Bool.not_false, and_self, false_implies, implies_true, Nat.reduceBEq, Nat.reduceBNe, decide_true, decide_false, BitVec.reduceSignExtend, VG.Proof.AesGcm.X86_64.copyBody, srcB, dstB, imm, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false,
      e₁, e₂, r, w]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
      BitVec.setWidth_eq]
  · simp [gpr_setReg, hi]
  · simp [hi, hn]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

/-- The source byte `i` is not overwritten by the copy so far. -/
theorem src_kept {m : Mem} {S D : Addr} {n i : Nat} (hd : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) (hi : i < n)
    (hn : n < 2 ^ 63) (xs : List Byte) (hxs : xs.length = i) :
    writeBytes m D xs (S + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i) :=
  (writeBytes_frame m D xs (R := ⟨D, i⟩) (by rw [hxs]; exact Region.contains_self _ _)) _
    fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hd _ (Offset.contains_base S (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)

theorem copyLoop_ok (s : State) {S D : Addr} {n : Nat} (h : VG.Proof.AesGcm.X86_64.LoopPre s S D n) :
    WP isa copyLoop s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r10₁, g₁⟩ : ∃ s₁, runBlock isa [.mov32 .r10 (imm 0)] s = some s₁ ∧
      s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ s₁ = s.setReg .r10 (BitVec.setWidth 64 (BitVec.ofNat 32 0)) :=
    ⟨_, by simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32], by simp [gpr_setReg], rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  subst g₁
  refine WP.loop (M := isa) (body := .block VG.Proof.AesGcm.X86_64.copyBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem D (bytesAt s.mem S i) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, h.pos, r10₁, by simp [bytesAt, writeBytes_nil, mem_setReg],
      fun r h₁ h₂ => by simp [gpr_setReg, h₂], rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r10, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := VG.Proof.AesGcm.X86_64.copyStep_ok t
    (by rw [g _ (by decide) (by decide), h.rsi]) (by rw [g _ (by decide) (by decide), h.rdi]) r10
    (by rw [g _ (by decide) (by decide), h.rcx])
    (by rw [rd, wr]; exact VG.Proof.AesGcm.X86_64.in_of_covers h.rd hi (by have := h.lt; omega))
    (by rw [wr]; exact VG.Proof.AesGcm.X86_64.in_of_covers h.wr hi (by have := h.lt; omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (bytesAt s.mem S i).length = i := by simp [bytesAt]
  have hmem : t'.mem = writeBytes s.mem D (bytesAt s.mem S (i + 1)) := by
    rw [mem', mem, VG.Proof.AesGcm.X86_64.src_kept h.disj hi h.lt _ hlen, VG.Proof.AesGcm.X86_64.bytesAt_succ,
      writeBytes_snoc s.mem D (bytesAt s.mem S i) _ (by rw [hlen]; have := h.lt; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = n)) := by
    rw [zf', VG.Proof.AesGcm.X86_64.succ_ofNat, Offset.ofNat_sub_ofNat_beq (by have := h.lt; omega) (by have := h.lt; omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : i + 1 = n
  · left
    refine ⟨by simp [VG.X86_64.eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [VG.X86_64.eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', VG.Proof.AesGcm.X86_64.succ_ofNat],
      hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

/-! ## `xorLoop` -/

abbrev xorBody : List Instr :=
  [.movzx8 .rax dstB, .movzx8 .r11 srcB, .alu .xor .rax (.reg .r11), .store8 dstB .rax,
    .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rcx)]

theorem setWidth8_xor (a b : Byte) :
    ((a.setWidth 64 ^^^ b.setWidth 64 : BitVec 64)).setWidth 8 = a ^^^ b := by
  ext j hj; simp

theorem xorStep_ok (s : State) {S D : Addr} {i n : Nat} (hs : s.gpr .rsi = S) (hd : s.gpr .rdi = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hn : s.gpr .rcx = BitVec.ofNat 64 n)
    (r : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa VG.Proof.AesGcm.X86_64.xorBody s = some s' ∧
      s'.mem = s.mem.writeW (D + BitVec.ofNat 64 i)
        (s.mem (D + BitVec.ofNat 64 i) ^^^ s.mem (S + BitVec.ofNat 64 i)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 n == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e₁ := VG.Proof.AesGcm.X86_64.ea_idx s .rsi hs hi
  have e₂ := VG.Proof.AesGcm.X86_64.ea_idx s .rdi hd hi
  have wr' : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 i) 1 := by
    obtain ⟨x, hx, hc⟩ := w; exact ⟨x, List.mem_append_right _ hx, hc⟩
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.reduceGT, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, BitVec.reduceEq, not_false_eq_true, not_true_eq_false, Bool.not_true, Bool.not_false, and_self, false_implies, implies_true, Nat.reduceBEq, Nat.reduceBNe, decide_true, decide_false, BitVec.reduceSignExtend, VG.Proof.AesGcm.X86_64.xorBody, srcB, dstB, imm, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags,
      wr_setReg, wr_arithFlags, ite_true, ite_false, e₁, e₂, r, w, wr']
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags, VG.Proof.AesGcm.X86_64.setWidth8_xor]
  · simp [gpr_setReg, hi]
  · simp [hi, hn]
  · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]

/-- The bytes at `D` XORed with those at `S`. -/
def xorBytes (m : Mem) (D S : Addr) (n : Nat) : List Byte :=
  List.zipWith (· ^^^ ·) (bytesAt m D n) (bytesAt m S n)

theorem xorBytes_succ (m : Mem) (D S : Addr) (i : Nat) :
    VG.Proof.AesGcm.X86_64.xorBytes m D S (i + 1) = VG.Proof.AesGcm.X86_64.xorBytes m D S i ++ [m (D + BitVec.ofNat 64 i) ^^^ m (S + BitVec.ofNat 64 i)] := by
  simp [VG.Proof.AesGcm.X86_64.xorBytes, VG.Proof.AesGcm.X86_64.bytesAt_succ, List.zipWith_append, Cmac.bytesAt_length]

theorem length_xorBytes (m : Mem) (D S : Addr) (n : Nat) : (VG.Proof.AesGcm.X86_64.xorBytes m D S n).length = n := by
  simp [VG.Proof.AesGcm.X86_64.xorBytes, Cmac.bytesAt_length]

/-- Byte `i` of the destination, not yet written. -/
theorem dst_kept {m : Mem} {D : Addr} {n i : Nat} (hi : i < n) (hn : n < 2 ^ 63) (xs : List Byte)
    (hxs : xs.length = i) : writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.lt_irrefl, ite_false]

theorem xorLoop_ok (s : State) {S D : Addr} {n : Nat} (h : VG.Proof.AesGcm.X86_64.LoopPre s S D n) :
    WP isa xorLoop s fun s' => s'.mem = writeBytes s.mem D (VG.Proof.AesGcm.X86_64.xorBytes s.mem D S n) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r10₁, g₁⟩ : ∃ s₁, runBlock isa [.mov32 .r10 (imm 0)] s = some s₁ ∧
      s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ s₁ = s.setReg .r10 (BitVec.setWidth 64 (BitVec.ofNat 32 0)) :=
    ⟨_, by simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32], by simp [gpr_setReg], rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  subst g₁
  refine WP.loop (M := isa) (body := .block VG.Proof.AesGcm.X86_64.xorBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem D (VG.Proof.AesGcm.X86_64.xorBytes s.mem D S i) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, h.pos, r10₁, by simp [VG.Proof.AesGcm.X86_64.xorBytes, bytesAt, writeBytes_nil, mem_setReg],
      fun r h₁ h₂ _ => by simp [gpr_setReg, h₂], rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r10, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := VG.Proof.AesGcm.X86_64.xorStep_ok t
    (by rw [g _ (by decide) (by decide) (by decide), h.rsi])
    (by rw [g _ (by decide) (by decide) (by decide), h.rdi]) r10
    (by rw [g _ (by decide) (by decide) (by decide), h.rcx])
    (by rw [rd, wr]; exact VG.Proof.AesGcm.X86_64.in_of_covers h.rd hi (by have := h.lt; omega))
    (by rw [wr]; exact VG.Proof.AesGcm.X86_64.in_of_covers h.wr hi (by have := h.lt; omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen := VG.Proof.AesGcm.X86_64.length_xorBytes s.mem D S i
  have hmem : t'.mem = writeBytes s.mem D (VG.Proof.AesGcm.X86_64.xorBytes s.mem D S (i + 1)) := by
    rw [mem', mem, VG.Proof.AesGcm.X86_64.src_kept h.disj hi h.lt _ hlen, VG.Proof.AesGcm.X86_64.dst_kept hi h.lt _ hlen, VG.Proof.AesGcm.X86_64.xorBytes_succ,
      writeBytes_snoc s.mem D _ _ (by rw [hlen]; have := h.lt; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = n)) := by
    rw [zf', VG.Proof.AesGcm.X86_64.succ_ofNat, Offset.ofNat_sub_ofNat_beq (by have := h.lt; omega) (by have := h.lt; omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → t'.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ => by rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  by_cases he : i + 1 = n
  · left
    refine ⟨by simp [VG.X86_64.eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [VG.X86_64.eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', VG.Proof.AesGcm.X86_64.succ_ofNat],
      hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Callee`. -/
section

/-!
# AES-GCM on x86-64: the functions called

Untrusted: everything here is checked by Lean. What the AES-GCM functions
need of the implementations of `vg_ghash`, `vg_aes_expand_key_scratch` and
`vg_aes_ctr32` they call (`GhashImpl`, `KeyImpl`, and the existing
`Ctr32Impl`), and each call from its callee's contract (with `WP.call`), with
the regions it is given: what it needs (`GhCall`, `CtrCall`, `KeyCall`) and
what it leaves (`GhPost`, `CtrPost`, `KeyPost`); and that it is constant time
(`gh_rel`, `ctr_rel`, `key_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctr32 aesWith)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- An implementation of `vg_ghash` on x86-64. -/
structure GhashImpl where
  fn : Fn
  depth : fn.code.depth = 0
  /-- It uses no stack, so that its callers can say how much they use. -/
  noStack : fn.code.x86_64Depth = 0 := by lit_decide
  ok : ∀ s, Proof.Gcm.ghashX86_64.pre s →
    ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ Proof.Gcm.ghashX86_64.post s s'
  ct : ConstantTime isa Proof.Gcm.ghashX86_64.pre Proof.Gcm.ghashX86_64.pub fn.code
  nosp : NoSp fn.code
  mxcsr : fn.code.allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : fn.code.all (fun i => !isa.writesSp i) = true
  suffix : String
  features : List String

/-- An implementation of `vg_aes_expand_key_scratch` on x86-64. -/
structure KeyImpl where
  fn : Fn
  depth : fn.code.depth = 0
  /-- It uses no stack, so that its callers can say how much they use. -/
  noStack : fn.code.x86_64Depth = 0 := by lit_decide
  ok : ∀ s, Proof.Aes.expandKeyX86_64.pre s →
    ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyX86_64.post s s'
  ct : ConstantTime isa Proof.Aes.expandKeyX86_64.pre Proof.Aes.expandKeyX86_64.pub fn.code
  nosp : NoSp fn.code
  mxcsr : fn.code.allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : fn.code.all (fun i => !isa.writesSp i) = true
  features : List String

theorem nosp_of {c : Prog isa} (h : ((instrs c).all fun i => !Taint.clobbers i .rsp) = true) : NoSp c :=
  fun i hi => by simpa using List.all_eq_true.mp h i hi

namespace KeyImpl

/-- `vg_aes_expand_key_scratch`, in the baseline ISA. -/
def scalar : KeyImpl where
  fn := ⟨"vg_aes_expand_key_scratch", Impl.Aes.X86_64.expandKey⟩
  depth := by lit_decide
  ok := Proof.Aes.X86_64.expandKey_correct
  ct := Proof.Aes.X86_64.expandKey_ct
  nosp := VG.Proof.AesGcm.X86_64.nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  features := []

/-- `vg_aes_expand_key_scratch_aesni`. -/
def aesni : KeyImpl where
  fn := ⟨"vg_aes_expand_key_scratch_aesni", Impl.Aes.X86_64.AesNi.expandKey⟩
  depth := by lit_decide
  ok s hs := Proof.Aes.X86_64.AesNi.Key.expandKey_correct s
    ⟨hs.1, hs.2.1, hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.2⟩
  ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp :=
    Proof.Aes.X86_64.AesNi.Key.expandKey_ct s₁ s₂ t₁ t₂ s₁' s₂'
      ⟨h₁.1, h₁.2.1, h₁.2.2.2.2.2.1, h₁.2.2.2.2.2.2.2⟩ ⟨h₂.1, h₂.2.1, h₂.2.2.2.2.2.1, h₂.2.2.2.2.2.2.2⟩
      ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  nosp := VG.Proof.AesGcm.X86_64.nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  features := ["aes"]

end KeyImpl

/-! ## Memory -/

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  rw [blockAt, blockAt, VG.Proof.AesGcm.X86_64.bytesAt_frame hf hd (by decide)]

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    blocksAt m' p n = blocksAt m p n := by
  rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, VG.Proof.AesGcm.X86_64.bytesAt_frame hf hd hn]

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

theorem disj_below {s : State} {p : Addr} {n : Nat} (h : (below (s.gpr .rsp) 8).Disjoint ⟨p, n⟩) :
    ∀ r ∈ [below (s.gpr .rsp) 8], (⟨p, n⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact h.symm

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## `vg_ghash` -/

/-- What a call of `vg_ghash` needs: the hash subkey at `H`, the accumulator
at `Y`, `n` blocks at `D` and working space at `S`. -/
structure GhCall (s : State) (H Y D S : Addr) (n : Nat) : Prop where
  rdi : s.gpr .rdi = H
  rsi : s.gpr .rsi = Y
  rdx : s.gpr .rdx = D
  rcx : s.gpr .rcx = BitVec.ofNat 64 n
  r8 : s.gpr .r8 = S
  n_lt : 16 * n < 2 ^ 64
  hy : (⟨H, 16⟩ : Region).Disjoint ⟨Y, 16⟩
  hs : (⟨H, 16⟩ : Region).Disjoint ⟨S, 256⟩
  yd : (⟨Y, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ys : (⟨Y, 16⟩ : Region).Disjoint ⟨S, 256⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 256⟩
  stkH : (below (s.gpr .rsp) 8).Disjoint ⟨H, 16⟩
  stkY : (below (s.gpr .rsp) 8).Disjoint ⟨Y, 16⟩
  stkD : (below (s.gpr .rsp) 8).Disjoint ⟨D, 16 * n⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 256⟩
  reads : Covers ([⟨H, 16⟩, ⟨D, 16 * n⟩] ++ [⟨Y, 16⟩, ⟨S, 256⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨Y, 16⟩, ⟨S, 256⟩] s.wr

/-- What a call of `vg_ghash` leaves. -/
structure GhPost (s : State) (H Y D S : Addr) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨Y, 16⟩, ⟨S, 256⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  out : blockAt s'.mem Y = ghashFrom (blockAt s.mem H) (blockAt s.mem Y) (blocksAt s.mem D n)

theorem GhCall.pre {s : State} {H Y D S : Addr} {n : Nat} (h : VG.Proof.AesGcm.X86_64.GhCall s H Y D S n) :
    Proof.Gcm.ghashX86_64.pre (s.callEntry.withRegions [⟨H, 16⟩, ⟨D, 16 * n⟩] [⟨Y, 16⟩, ⟨S, 256⟩]) := by
  have hn := VG.Proof.AesGcm.X86_64.toNat_ofNat_lt (show n < 2 ^ 64 by have := h.n_lt; omega)
  simp only [Proof.Gcm.ghashX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hn]
  exact ⟨trivial, trivial, h.hy, h.hs, h.yd, h.ys, h.ds, h.stkY, h.stkS⟩

theorem gh_call (g : VG.Proof.AesGcm.X86_64.GhashImpl) {s : State} {H Y D S : Addr} {n : Nat} (h : VG.Proof.AesGcm.X86_64.GhCall s H Y D S n) :
    WP isa (.call g.fn.name g.fn.code) s (VG.Proof.AesGcm.X86_64.GhPost s H Y D S n) := by
  have hn := VG.Proof.AesGcm.X86_64.toNat_ofNat_lt (show n < 2 ^ 64 by have := h.n_lt; omega)
  refine WP.call (k := Proof.Gcm.ghashX86_64) g.ok g.nosp (by rw [g.depth]; decide)
    (rd := [⟨H, 16⟩, ⟨D, 16 * n⟩]) (wr := [⟨Y, 16⟩, ⟨S, 256⟩]) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [g.depth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [Proof.Gcm.ghashX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, hn, hm₂] at hpost
  have fE := VG.Proof.AesGcm.X86_64.callEntry_frame s
  rw [hpost, VG.Proof.AesGcm.X86_64.blockAt_frame fE (VG.Proof.AesGcm.X86_64.disj_below h.stkH), VG.Proof.AesGcm.X86_64.blockAt_frame fE (VG.Proof.AesGcm.X86_64.disj_below h.stkY),
    VG.Proof.AesGcm.X86_64.blocksAt_frame fE (VG.Proof.AesGcm.X86_64.disj_below h.stkD) (by have := h.n_lt; omega)]

theorem gh_rel (g : VG.Proof.AesGcm.X86_64.GhashImpl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ H Y D S : Addr, ∃ n : Nat,
      VG.Proof.AesGcm.X86_64.GhCall s₁ H Y D S n ∧ VG.Proof.AesGcm.X86_64.GhCall s₂ H Y D S n ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call g.fn.name g.fn.code) fun _ _ => True := by
  refine RelCT.callEx g.ok g.ct fun s₁ s₂ hp => ?_
  obtain ⟨H, Y, D, S, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Gcm.ghashX86_64, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_ctr32` -/

/-- What a call of `vg_aes_ctr32` needs: the key schedule at `K` for `R`
rounds, the counter block at `C`, `n` blocks at `D` and working space at `S`. -/
structure CtrCall (s : State) (K C D S : Addr) (R n : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = D
  r8 : s.gpr .r8 = BitVec.ofNat 64 n
  r9 : s.gpr .r9 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  kc : (⟨K, 240⟩ : Region).Disjoint ⟨C, 16⟩
  kd : (⟨K, 240⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ks : (⟨K, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 2048⟩
  stkK : (below (s.gpr .rsp) 8).Disjoint ⟨K, 240⟩
  stkC : (below (s.gpr .rsp) 8).Disjoint ⟨C, 16⟩
  stkD : (below (s.gpr .rsp) 8).Disjoint ⟨D, 16 * n⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 2048⟩
  reads : Covers ([⟨K, 240⟩] ++ [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩] s.wr

/-- What a call of `vg_aes_ctr32` leaves. -/
structure CtrPost (s : State) (K C D S : Addr) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  out : blocksAt s'.mem D n = ctr32 (aesWith R (bytesAt s.mem K (16 * (R + 1)))) (blockAt s.mem C)
    (blocksAt s.mem D n)
  ctr : blockAt s'.mem C = Nat.repeat Spec.Gcm.inc32 n (blockAt s.mem C)

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 64 R).toNat = R :=
  VG.Proof.AesGcm.X86_64.toNat_ofNat_lt (by omega)

theorem CtrCall.pre {s : State} {K C D S : Addr} {R n : Nat} (h : VG.Proof.AesGcm.X86_64.CtrCall s K C D S R n) :
    Proof.Aes.ctr32X86_64.pre
      (s.callEntry.withRegions [⟨K, 240⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) := by
  have hR := VG.Proof.AesGcm.X86_64.toNat_rounds h.rounds
  have hn := VG.Proof.AesGcm.X86_64.toNat_ofNat_lt (show n < 2 ^ 64 by have := h.wrap; omega)
  simp only [Proof.Aes.ctr32X86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hR, hn]
  exact ⟨trivial, trivial, h.kc, h.kd, h.ks, h.cd, h.cs, h.ds, h.stkC, h.stkD, h.stkS, h.wrap,
    h.rounds⟩

theorem ctr_call (v : Ctr32Impl) {s : State} {K C D S : Addr} {R n : Nat} (h : VG.Proof.AesGcm.X86_64.CtrCall s K C D S R n) :
    WP isa (.call v.callee.name v.callee.code) s (VG.Proof.AesGcm.X86_64.CtrPost s K C D S R n) := by
  have hR := VG.Proof.AesGcm.X86_64.toNat_rounds h.rounds
  have hn := VG.Proof.AesGcm.X86_64.toNat_ofNat_lt (show n < 2 ^ 64 by have := h.wrap; omega)
  refine WP.call (k := Proof.Aes.ctr32X86_64) v.ok v.nosp (by rw [v.depth]; decide)
    (rd := [⟨K, 240⟩]) (wr := [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [v.depth] at hf
  obtain ⟨hdata, hctr⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hn,
    hm₂] at hdata hctr
  have fE := VG.Proof.AesGcm.X86_64.callEntry_frame s
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with rfl | rfl | rfl <;> decide
  have eK := VG.Proof.AesGcm.X86_64.bytesAt_frame fE (p := K) (n := 16 * (R + 1))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.stkK.sub_right (Region.sub_prefix hRb)).symm) (by omega)
  rw [VG.Proof.AesGcm.X86_64.blockAt_frame fE (VG.Proof.AesGcm.X86_64.disj_below h.stkC), VG.Proof.AesGcm.X86_64.blocksAt_frame fE (VG.Proof.AesGcm.X86_64.disj_below h.stkD) (by have := h.wrap; omega),
    eK] at hdata
  rw [VG.Proof.AesGcm.X86_64.blockAt_frame fE (VG.Proof.AesGcm.X86_64.disj_below h.stkC)] at hctr
  exact ⟨hrd, hwr, hcs, by simpa using hf, hdata, hctr⟩

theorem ctr_rel (v : Ctr32Impl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C D S : Addr, ∃ R n : Nat,
      VG.Proof.AesGcm.X86_64.CtrCall s₁ K C D S R n ∧ VG.Proof.AesGcm.X86_64.CtrCall s₂ K C D S R n ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call v.callee.name v.callee.code) fun _ _ => True := by
  refine RelCT.callEx v.ok v.ct fun s₁ s₂ hp => ?_
  obtain ⟨K, C, D, S, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.ctr32X86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key_scratch` -/

/-- What a call of `vg_aes_expand_key_scratch` needs: the `L`-byte key at `K`, the key
schedule at `C` and working space at `S`. -/
structure KeyCall (s : State) (K C S : Addr) (L : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 L
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = S
  len : L = 16 ∨ L = 24 ∨ L = 32
  kc : (⟨K, L⟩ : Region).Disjoint ⟨C, 240⟩
  ks : (⟨K, L⟩ : Region).Disjoint ⟨S, 512⟩
  cs : (⟨C, 240⟩ : Region).Disjoint ⟨S, 512⟩
  stkK : (below (s.gpr .rsp) 8).Disjoint ⟨K, L⟩
  stkC : (below (s.gpr .rsp) 8).Disjoint ⟨C, 240⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 512⟩
  reads : Covers ([⟨K, L⟩] ++ [⟨C, 240⟩, ⟨S, 512⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 240⟩, ⟨S, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key_scratch` leaves. -/
structure KeyPost (s : State) (K C S : Addr) (L : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 240⟩, ⟨S, 512⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  out : bytesAt s'.mem C (16 * (Spec.Aes.rounds (L / 4) + 1)) = Spec.Aes.expandKey (bytesAt s.mem K L)

theorem KeyCall.pre {s : State} {K C S : Addr} {L : Nat} (h : VG.Proof.AesGcm.X86_64.KeyCall s K C S L) :
    Proof.Aes.expandKeyX86_64.pre (s.callEntry.withRegions [⟨K, L⟩] [⟨C, 240⟩, ⟨S, 512⟩]) := by
  have hL := VG.Proof.AesGcm.X86_64.toNat_ofNat_lt (show L < 2 ^ 64 by rcases h.len with rfl | rfl | rfl <;> decide)
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, hL]
  exact ⟨trivial, trivial, h.kc, h.ks, h.cs, h.stkC, h.stkS, h.len⟩

theorem key_call (k : VG.Proof.AesGcm.X86_64.KeyImpl) {s : State} {K C S : Addr} {L : Nat} (h : VG.Proof.AesGcm.X86_64.KeyCall s K C S L) :
    WP isa (.call k.fn.name k.fn.code) s (VG.Proof.AesGcm.X86_64.KeyPost s K C S L) := by
  have hL := VG.Proof.AesGcm.X86_64.toNat_ofNat_lt (show L < 2 ^ 64 by rcases h.len with rfl | rfl | rfl <;> decide)
  refine WP.call (k := Proof.Aes.expandKeyX86_64) k.ok k.nosp (by rw [k.depth]; decide)
    (rd := [⟨K, L⟩]) (wr := [⟨C, 240⟩, ⟨S, 512⟩]) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [k.depth] at hf
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx, hL, hm₂] at hpost
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  rw [hpost, VG.Proof.AesGcm.X86_64.bytesAt_frame (VG.Proof.AesGcm.X86_64.callEntry_frame s) (VG.Proof.AesGcm.X86_64.disj_below h.stkK)
    (by rcases h.len with rfl | rfl | rfl <;> decide)]

theorem key_rel (k : VG.Proof.AesGcm.X86_64.KeyImpl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C S : Addr, ∃ L : Nat,
      VG.Proof.AesGcm.X86_64.KeyCall s₁ K C S L ∧ VG.Proof.AesGcm.X86_64.KeyCall s₂ K C S L ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call k.fn.name k.fn.code) fun _ _ => True := by
  refine RelCT.callEx k.ok k.ct fun s₁ s₂ hp => ?_
  obtain ⟨K, C, S, L, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## The implementations, together -/

/-- What `Blocks.stitchPart` needs of the loops `code` it runs, besides
their contract: no write of `mxcsr` or `rsp`, no calls, and constant time,
from the registers it keeps public. -/
structure Piece (code : Prog isa) : Prop where
  mxcsr : code.allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : code.all (fun i => !X86_64.isa.writesSp i) = true
  nosp : code.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  depth : code.depth = 0
  /-- It uses no stack. -/
  xdepth : code.x86_64Depth = 0
  ct : ∃ hc, ((taint.check (Taint.ofRegs [.r11, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
    (Blocks.stitchPart code) hc).map fun τ' => (RegSet.ofList [Reg.rsp]).subset τ'.regs &&
      (!false || τ'.flags)) = some true

/-- Loops that interleave counter mode and GHASH on groups of 16 blocks, for
`vg_aes_gcm_encrypt_blocks` and `_decrypt_blocks` (`Gcm.X86_64.Stitch.SPre`).
Their proof is supplied only by the instances that use them (it imports the
algebra of `Proof/Gcm/Poly.lean`). -/
structure StitchImpl where
  /-- What the names of the instances using them end with, after the
  callees' suffixes. -/
  suffix : String
  /-- The CPU features they need beyond the callees'. -/
  features : List String
  enc : Prog isa
  dec : Prog isa
  ok : Gcm.X86_64.Stitch.StitchOk enc dec
  encP : VG.Proof.AesGcm.X86_64.Piece enc
  decP : VG.Proof.AesGcm.X86_64.Piece dec

namespace StitchImpl

variable (st : Option VG.Proof.AesGcm.X86_64.StitchImpl) {f : VG.Proof.AesGcm.X86_64.StitchImpl → Prog isa} (hf : ∀ i, VG.Proof.AesGcm.X86_64.Piece (f i))
include hf

theorem head_mxcsr : (Blocks.head (st.map f)).allInstrs (fun i => !loadsMxcsr i) = true := by
  rcases st with _ | i <;>
  simp only [Option.map, Blocks.head, Blocks.stitchPart, Code.allInstrs, (hf _).mxcsr] <;> decide

theorem head_spSafe : (Blocks.head (st.map f)).all (fun i => !X86_64.isa.writesSp i) = true := by
  rcases st with _ | i <;>
  simp only [Option.map, Blocks.head, Blocks.stitchPart, Code.all, (hf _).spSafe] <;> decide

theorem head_nosp : (Blocks.head (st.map f)).allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
  rcases st with _ | i <;>
  simp only [Option.map, Blocks.head, Blocks.stitchPart, Code.allInstrs, (hf _).nosp] <;> decide

theorem head_depth : (Blocks.head (st.map f)).depth = 0 := by
  rcases st with _ | i <;>
  simp only [Option.map, Blocks.head, Blocks.stitchPart, Code.depth, (hf _).depth] <;> decide

theorem head_xdepth : (Blocks.head (st.map f)).x86_64Depth = 0 := by
  rcases st with _ | i <;>
  simp only [Option.map, Blocks.head, Blocks.stitchPart, Code.x86_64Depth, (hf _).xdepth] <;> decide

end StitchImpl

/-- What an AES-GCM function calls: an implementation of `vg_aes_ctr32`, the
`vg_aes_expand_key_scratch` for the same CPUs, and one of `vg_ghash`. -/
structure GcmImpl where
  ctr : Ctr32Impl
  key : VG.Proof.AesGcm.X86_64.KeyImpl
  gh : VG.Proof.AesGcm.X86_64.GhashImpl
  /-- The loops with which `vg_aes_gcm_encrypt_blocks` and `_decrypt_blocks`
  interleave counter mode and GHASH, if any. -/
  stitch : Option VG.Proof.AesGcm.X86_64.StitchImpl := none

namespace GcmImpl

variable (v : VG.Proof.AesGcm.X86_64.GcmImpl)

/-- What the names of the functions calling `vg_ghash` end with. -/
def suffix : String := v.ctr.suffix ++ v.gh.suffix ++ (v.stitch.map (·.suffix)).getD ""

def callees : Callees :=
  ⟨⟨v.ctr.callee.name, v.ctr.callee.code⟩, v.key.fn, v.gh.fn,
    ⟨Spec.Gcm.encryptBlocksApi.name ++ v.suffix,
      Impl.AesGcm.X86_64.Blocks.encrypt ⟨v.ctr.callee.name, v.ctr.callee.code⟩ v.gh.fn (v.stitch.map (·.enc))⟩,
    ⟨Spec.Gcm.decryptBlocksApi.name ++ v.suffix,
      Impl.AesGcm.X86_64.Blocks.decrypt ⟨v.ctr.callee.name, v.ctr.callee.code⟩ v.gh.fn (v.stitch.map (·.dec))⟩⟩

end GcmImpl

/-- The implementations of `vg_ghash`, by name, as the variants of `AesGcm`
choose them (`GcmVariant`, `Variant.lean`). `GhashName.impl`, in `GhashImpls.lean`, gives
their `GhashImpl`s, whose proofs import the algebra of `Proof/Gcm/Poly.lean`,
which the variants then need not import. -/
inductive GhashName where
  | scalar
  | pclmul
  | vpclmul

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Variant`. -/
section

/-!
# AES-GCM on x86-64: the variants

Untrusted: everything here is checked by Lean. What a variant of `AesGcm`
is (see `TCB/Emit.lean`): the implementations its functions call, with the
proofs that import the algebra of `Proof/Gcm/Poly.lean` (those of
`vg_ghash` and of the interleaved loops) named rather than held, so that the
variants need not import that algebra. The generic file
(`Generic/AesGcm/X86_64/AesGcm.lean`) resolves the names (`GcmVariant.impl`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The interleaved loops for `vg_aes_gcm_encrypt_blocks` and
`_decrypt_blocks`, by name. `StitchName.ok`, in the generic file, gives
their proof. -/
inductive StitchName where
  /-- `Impl.Gcm.X86_64.Stitch`: VAES and VPCLMULQDQ on 256-bit registers. -/
  | vaes
  /-- `Impl.Gcm.X86_64.StitchZ`: VAES and VPCLMULQDQ on 512-bit registers. -/
  | vaesAvx512
  /-- `Impl.Gcm.X86_64.StitchAvx`: AES-NI and PCLMULQDQ in `VEX.128`. -/
  | aesniAvx

namespace StitchName

/-- The encryption loop named `n`. -/
def enc : VG.Proof.AesGcm.X86_64.StitchName → Prog isa
  | .vaes => Impl.Gcm.X86_64.Stitch.enc
  | .vaesAvx512 => Impl.Gcm.X86_64.StitchZ.enc
  | .aesniAvx => Impl.Gcm.X86_64.StitchAvx.enc

/-- The decryption loop named `n`. -/
def dec : VG.Proof.AesGcm.X86_64.StitchName → Prog isa
  | .vaes => Impl.Gcm.X86_64.Stitch.dec
  | .vaesAvx512 => Impl.Gcm.X86_64.StitchZ.dec
  | .aesniAvx => Impl.Gcm.X86_64.StitchAvx.dec

end StitchName

/-- A `StitchImpl` with its loops named, and so without their proof of
`StitchOk` (`StitchName.ok`). -/
structure StitchPart where
  name : VG.Proof.AesGcm.X86_64.StitchName
  /-- What the names of the instances using them end with, after the
  callees' suffixes. -/
  suffix : String
  /-- The CPU features they need beyond the callees'. -/
  features : List String
  encP : VG.Proof.AesGcm.X86_64.Piece name.enc
  decP : VG.Proof.AesGcm.X86_64.Piece name.dec

/-- A variant of `AesGcm` (see `TCB/Emit.lean`): a `GcmImpl` with its
implementation of `vg_ghash` (`GhashName`) and its interleaved loops
(`StitchPart`) named, which `GcmVariant.impl`, in the generic file,
resolves. -/
structure GcmVariant where
  ctr : Ctr32Impl
  key : VG.Proof.AesGcm.X86_64.KeyImpl
  gh : VG.Proof.AesGcm.X86_64.GhashName
  stitch : Option VG.Proof.AesGcm.X86_64.StitchPart := none

end VG.Proof.AesGcm.X86_64

end
