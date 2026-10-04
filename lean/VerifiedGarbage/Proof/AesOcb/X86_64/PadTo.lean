import VerifiedGarbage.Proof.AesOcb.X86_64.Args
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops

/-!
# AES-OCB on x86-64: copying bytes (`copyLoop`, `padTo`)

Untrusted: everything here is checked by Lean. `copyLoop` copies the `n`
bytes at `rbx` to `rsi`, a byte at a time, counting up in `rcx`
(`copyLoop_ok`); `padTo d` writes `pad(S)` (§4.1) of the `n < 16` bytes `S`
at `rbx` to `W + d`: zeros, the bytes, and `0x80` after them (`padTo_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem pad)
open VG.Proof.AesCcm.X86_64 (runBlock_append eval_e eval_ne toNat_ofNat_of_lt length_bytesAt
  bytesAt_writeBytes_base writeW8_eq imm_eq)
open VG.Proof.AesGcm.X86_64 (in_of_covers succ_ofNat bytesAt_succ)

theorem ea_index (s : State) {b i : Reg} {B : Addr} {j : Nat} (hb : s.gpr b = B)
    (hi : s.gpr i = BitVec.ofNat 64 j) :
    s.gpr b + s.gpr i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = B + BitVec.ofNat 64 j := by
  rw [hb, hi, BitVec.mul_one]; simp

theorem contains_pre (p : Addr) {j n : Nat} (h : j ≤ n) : (⟨p, n⟩ : Region).Contains p j := by
  simpa using Offset.contains_base p (d := 0) (n := j) (k := n) (by omega) (by decide)

theorem setWidth_byte (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt b.isLt]

/-- One step of `copyLoop`. -/
theorem copyStep_ok (s : State) {S Dd : Addr} {j n : Nat} (h3 : s.gpr .rbx = S) (h6 : s.gpr .rsi = Dd)
    (h1 : s.gpr .rcx = BitVec.ofNat 64 j) (h12 : s.gpr .r12 = BitVec.ofNat 64 n)
    (rq : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 j) 1) (wq : InRegions s.wr (Dd + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa [.movzx8 .rax { base := .rbx, index := some .rcx },
        .store8 { base := .rsi, index := some .rcx } .rax, addi .rcx 1, .alu .cmp .rcx (.reg .r12)] s = some s' ∧
      s'.mem = s.mem.writeW (Dd + BitVec.ofNat 64 j) (s.mem (S + BitVec.ofNat 64 j)) ∧
      s'.gpr .rcx = BitVec.ofNat 64 (j + 1) ∧
      s'.zf = some (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 n == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea₁ := ea_index s h3 h1
  have ea₂ := ea_index s h6 h1
  refine ⟨_, by orun [ea₁, ea₂, rq, wq], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, setWidth_byte]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, h1, sext1, ← BitVec.ofNat_add]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h1, h12, sext1,
      ← BitVec.ofNat_add]
  · intro r h₁ h₂; simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, ite_false]
  all_goals rfl

/-- `copyLoop`: the `n > 0` bytes at `S` (in `rbx`) to `Dd` (in `rsi`), from `rcx = 0`. -/
theorem copyLoop_ok (s : State) {S Dd : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64) (h3 : s.gpr .rbx = S)
    (h6 : s.gpr .rsi = Dd) (h1 : s.gpr .rcx = BitVec.ofNat 64 0) (h12 : s.gpr .r12 = BitVec.ofNat 64 n)
    (hS : Covers [⟨S, n⟩] (s.rd ++ s.wr)) (hD : Covers [⟨Dd, n⟩] s.wr) (hSD : (⟨S, n⟩ : Region).Disjoint ⟨Dd, n⟩) :
    WP isa copyLoop s fun t => t.mem = writeBytes s.mem Dd (bytesAt s.mem S n) ∧
      t.gpr .rcx = BitVec.ofNat 64 n ∧ (∀ r, r ≠ .rax → r ≠ .rcx → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .rcx = BitVec.ofNat 64 j ∧
      t.mem = writeBytes s.mem Dd (bytesAt s.mem S j) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn, h1, by simp [bytesAt, writeBytes_nil], fun r _ _ => rfl, rfl, rfl⟩
  rintro k t ⟨j, rfl, hj, rcx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', rcx', zf', g', rd', wr'⟩ := copyStep_ok t (S := S) (Dd := Dd) (j := j) (n := n)
    (by rw [g _ (by decide) (by decide), h3]) (by rw [g _ (by decide) (by decide), h6]) rcx
    (by rw [g _ (by decide) (by decide), h12]) (by rw [rd, wr]; exact in_of_covers hS hj hn')
    (by rw [wr]; exact in_of_covers hD hj hn')
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨Dd, n⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact contains_pre _ (by omega))
  have hq : t.mem (S + BitVec.ofNat 64 j) = s.mem (S + BitVec.ofNat 64 j) :=
    fr _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hSD _ (Offset.contains_base S (by omega) (by omega)) hc
  have hmem : t'.mem = writeBytes s.mem Dd (bytesAt s.mem S (j + 1)) := by
    rw [mem', hq, mem, bytesAt_succ, writeBytes_snoc _ _ _ _ (by rw [length_bytesAt]; omega), length_bytesAt]
  have hz : t'.zf = some (decide (j + 1 = n)) := by
    rw [zf', Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .rcx → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : j + 1 = n
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), by rw [hmem, he], by rw [rcx', he], gg, by rw [rd', rd],
      by rw [wr', wr]⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), n - (j + 1), by omega, j + 1, rfl, by omega, rcx', hmem, gg,
      by rw [rd', rd], by rw [wr', wr]⟩

theorem toBytes_zero : Spec.Ocb.toBytes 0 = Spec.Ocb.zeros 16 := by decide

/-- The 16 bytes of a block that is zero. -/
theorem bytesAt_of_zero {m : Mem} {p : Addr} (h : blockAtMem m p = 0) : bytesAt m p 16 = Spec.Ocb.zeros 16 := by
  rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt m p 16), ← toBytes_zero, ← h]; rfl

/-- `padTo d`: `W + d ← pad(S)`, for the `n` bytes `S` at `rbx`, `0 < n < 16`. -/
theorem padTo_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {S : Addr} {n d : Nat} (hn : 0 < n)
    (hn' : n < 16) (hd : d + 16 ≤ 2560) (h3 : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 n)
    (hS : Covers [⟨S, n⟩] (s.rd ++ s.wr)) (hSD : (⟨S, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, 16⟩) :
    WP isa (padTo d) s fun t => Frame [⟨W + BitVec.ofNat 64 d, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (W + BitVec.ofNat 64 d) = pad (bytesAt s.mem S n) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have h15 := E.r15
  obtain ⟨s₁, run₁, B₁⟩ := zero16_ok (s := s) (d := d) h15 (E.perm.wW (by omega)) (E.perm.wW (by omega))
  obtain ⟨s₂, run₂, rsi₂, rcx₂, g₂, m₂, rd₂, wr₂⟩ : ∃ s₂,
      runBlock isa [mvr .rsi .r15, addi .rsi d, .mov .rcx (.imm 0)] s₁ = some s₂ ∧
      s₂.gpr .rsi = W + BitVec.ofNat 64 d ∧ s₂.gpr .rcx = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .rsi → r ≠ .rcx → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have h15₁ : s₁.gpr .r15 = W := by rw [B₁.gpr _ (by decide), h15]
    refine ⟨_, by orun [h15₁], ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₁]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, BitVec.xor_self, sext0]
    · simp only [gpr_setReg, gpr_arithFlags, h1, h2, ite_false]
    all_goals rfl
  have hS₂ : Covers [⟨S, n⟩] (s₂.rd ++ s₂.wr) := by rw [rd₂, wr₂, B₁.rd, B₁.wr]; exact hS
  have hD₂ : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s₂.wr := by
    rw [wr₂, B₁.wr]; exact E.perm.wC (by omega)
  have hSD' : (⟨S, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ := hSD.sub_right (Region.sub_prefix (by omega))
  have eS : bytesAt s₂.mem S n = bytesAt s.mem S n := by
    rw [m₂]
    exact Proof.AesCcm.X86_64.bytesAt_frame B₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hSD) (by omega)
  have z₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 d) 16 = Spec.Ocb.zeros 16 := by
    rw [m₂]; exact bytesAt_of_zero B₁.val
  unfold padTo
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append, run₁, Option.bind_some, run₂], ?_⟩)
  refine WP.seq (WP.mono (copyLoop_ok s₂ hn (by omega) (by rw [g₂ _ (by decide) (by decide), B₁.gpr _ (by decide), h3])
    rsi₂ rcx₂ (by rw [g₂ _ (by decide) (by decide), B₁.gpr _ (by decide), h12]) hS₂ hD₂ hSD') fun s₃ h₃ => ?_)
  obtain ⟨m₃, rcx₃, g₃, rd₃, wr₃⟩ := h₃
  have rsi₃ : s₃.gpr .rsi = W + BitVec.ofNat 64 d := by rw [g₃ _ (by decide) (by decide), rsi₂]
  have ea := ea_index s₃ rsi₃ rcx₃
  have w₃ : InRegions s₃.wr (W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) 1 := by
    rw [wr₃, wr₂, B₁.wr, Offset.add_add]; exact E.perm.wW (by omega)
  refine WP.of_runBlock ⟨_, by orun [ea, w₃], ?_⟩
  have hlen : (bytesAt s.mem S n).length = n := length_bytesAt _ _ _
  have e80 : ((BitVec.signExtend 64 (128 : BitVec 32)).setWidth 8 : Byte) = 0x80 := by decide
  have key : ∀ (m : Mem) (b : Byte), (writeBytes m (W + BitVec.ofNat 64 d) (bytesAt s.mem S n)).writeW
      (W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) b = writeBytes m (W + BitVec.ofNat 64 d) (bytesAt s.mem S n ++ [b]) :=
    fun m b => by rw [writeBytes_snoc _ _ _ _ (by omega), hlen]
  refine ⟨?_, ?_, fun r h1 h2 h3 => ?_, by simp only [rd_setReg]; rw [rd₃, rd₂, B₁.rd],
    by simp only [wr_setReg]; rw [wr₃, wr₂, B₁.wr]⟩
  · simp only [mem_setReg, gpr_setReg, ite_true]
    rw [m₃, eS, key]
    intro x hx
    rw [writeBytes_frame _ _ _ (by simp [hlen]; exact contains_pre _ (by omega)) x hx, m₂]
    exact B₁.frame x hx
  · simp only [mem_setReg, gpr_setReg, ite_true]
    rw [m₃, eS, key, blockAtMem, bytesAt_writeBytes_base _ _ _ (by simp [hlen]; omega) (by decide), z₂, e80]
    simp only [pad, hlen, List.length_append, List.length_singleton, Spec.Ocb.zeros, List.drop_replicate,
      List.append_assoc, List.singleton_append, show 16 - (n + 1) = 15 - n by omega]
  · simp only [gpr_setReg, h1, ite_false]
    rw [g₃ r h1 h2, g₂ r h3 h2, B₁.gpr r (by simp [h1])]

end VG.Proof.AesOcb.X86_64
