import VerifiedGarbage.Proof.AesOcb.X86_64.Entry
import VerifiedGarbage.Proof.AesGcm.X86_64.Variant
import VerifiedGarbage.Proof.Ocb.Stretch32
import VerifiedGarbage.Proof.AesCcm.X86_64.Frame
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.Proof.AesOcb.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.PadTo`. -/
section

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
  have ea₁ := VG.Proof.AesOcb.X86_64.ea_index s h3 h1
  have ea₂ := VG.Proof.AesOcb.X86_64.ea_index s h6 h1
  refine ⟨_, by orun [ea₁, ea₂, rq, wq], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, VG.Proof.AesOcb.X86_64.setWidth_byte]
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
  obtain ⟨t', run', mem', rcx', zf', g', rd', wr'⟩ := VG.Proof.AesOcb.X86_64.copyStep_ok t (S := S) (Dd := Dd) (j := j) (n := n)
    (by rw [g _ (by decide) (by decide), h3]) (by rw [g _ (by decide) (by decide), h6]) rcx
    (by rw [g _ (by decide) (by decide), h12]) (by rw [rd, wr]; exact in_of_covers hS hj hn')
    (by rw [wr]; exact in_of_covers hD hj hn')
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨Dd, n⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact VG.Proof.AesOcb.X86_64.contains_pre _ (by omega))
  have hq : t.mem (S + BitVec.ofNat 64 j) = s.mem (S + BitVec.ofNat 64 j) :=
    fr _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hSD _ (Offset.contains_base S (by omega) (by omega)) hc
  have hmem : t'.mem = writeBytes s.mem Dd (bytesAt s.mem S (j + 1)) := by
    rw [mem', hq, mem, VG.Proof.AesGcm.X86_64.bytesAt_succ, writeBytes_snoc _ _ _ _ (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; omega), VG.Proof.AesCcm.X86_64.length_bytesAt]
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
  rw [← Proof.Ocb.toBytes_ofBytes (VG.Proof.AesCcm.X86_64.length_bytesAt m p 16), ← VG.Proof.AesOcb.X86_64.toBytes_zero, ← h]; rfl

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
    rw [m₂]; exact VG.Proof.AesOcb.X86_64.bytesAt_of_zero B₁.val
  unfold padTo
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₁, Option.bind_some, run₂], ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.copyLoop_ok s₂ hn (by omega) (by rw [g₂ _ (by decide) (by decide), B₁.gpr _ (by decide), h3])
    rsi₂ rcx₂ (by rw [g₂ _ (by decide) (by decide), B₁.gpr _ (by decide), h12]) hS₂ hD₂ hSD') fun s₃ h₃ => ?_)
  obtain ⟨m₃, rcx₃, g₃, rd₃, wr₃⟩ := h₃
  have rsi₃ : s₃.gpr .rsi = W + BitVec.ofNat 64 d := by rw [g₃ _ (by decide) (by decide), rsi₂]
  have ea := VG.Proof.AesOcb.X86_64.ea_index s₃ rsi₃ rcx₃
  have w₃ : InRegions s₃.wr (W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) 1 := by
    rw [wr₃, wr₂, B₁.wr, Offset.add_add]; exact E.perm.wW (by omega)
  refine WP.of_runBlock ⟨_, by orun [ea, w₃], ?_⟩
  have hlen : (bytesAt s.mem S n).length = n := VG.Proof.AesCcm.X86_64.length_bytesAt _ _ _
  have e80 : ((BitVec.signExtend 64 (128 : BitVec 32)).setWidth 8 : Byte) = 0x80 := by decide
  have key : ∀ (m : Mem) (b : Byte), (writeBytes m (W + BitVec.ofNat 64 d) (bytesAt s.mem S n)).writeW
      (W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) b = writeBytes m (W + BitVec.ofNat 64 d) (bytesAt s.mem S n ++ [b]) :=
    fun m b => by rw [writeBytes_snoc _ _ _ _ (by omega), hlen]
  refine ⟨?_, ?_, fun r h1 h2 h3 => ?_, by simp only [rd_setReg]; rw [rd₃, rd₂, B₁.rd],
    by simp only [wr_setReg]; rw [wr₃, wr₂, B₁.wr]⟩
  · simp only [mem_setReg, gpr_setReg, ite_true]
    rw [m₃, eS, key]
    intro x hx
    rw [writeBytes_frame _ _ _ (by simp [hlen]; exact VG.Proof.AesOcb.X86_64.contains_pre _ (by omega)) x hx, m₂]
    exact B₁.frame x hx
  · simp only [mem_setReg, gpr_setReg, ite_true]
    rw [m₃, eS, key, blockAtMem, VG.Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by simp [hlen]; omega) (by decide), z₂, e80]
    simp only [pad, hlen, List.length_append, List.length_singleton, Spec.Ocb.zeros, List.drop_replicate,
      List.append_assoc, List.singleton_append, show 16 - (n + 1) = 15 - n by omega]
  · simp only [gpr_setReg, h1, ite_false]
    rw [g₃ r h1 h2, g₂ r h3 h2, B₁.gpr r (by simp [h1])]

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.NonceBlock`. -/
section

/-!
# AES-OCB on x86-64: the block `Nonce` (`nonceBlock`)

Untrusted: everything here is checked by Lean. `nonceBlock` writes `Nonce`
(§4.2) with its last 6 bits cleared to `W + tmpO`, and `bottom` to
`W + botO` (`nonceBlock_ok`): zeros, the nonce copied to the end
(`copyLoop`), the 1 before it, `TAGLEN mod 128` ORed into the first byte,
and the last byte split into `bottom` and the rest. The 16 bytes are
followed as a list through the writes, and compared with `nb`
(`Proof.Ocb.nonceN_masked_byte`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (nonceN nb nbase)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt length_bytesAt bytesAt_writeBytes_at
  bytesAt_writeW8_at bytesAt_writeW8_base and15' imm_eq)

theorem or_byte (b : Byte) {v : Nat} (hv : v < 256) :
    ((b.setWidth 64 ||| BitVec.ofNat 64 v).setWidth 8 : Byte) = b ||| BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := v) (by omega), Nat.mod_eq_of_lt (a := v) (by omega),
    Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow b.isLt (by omega))

theorem and_byte (b : Byte) {v : Nat} (hv : v < 256) :
    ((b.setWidth 64 &&& BitVec.ofNat 64 v).setWidth 8 : Byte) = b &&& BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := v) (by omega), Nat.mod_eq_of_lt (a := v) (by omega),
    Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left b.isLt)

theorem and63 (b : Byte) : b.setWidth 64 &&& BitVec.ofNat 64 63 = BitVec.ofNat 64 (b.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (63 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem sub_one_addr (p : Addr) {a : Nat} (ha : 1 ≤ a) (ha' : a < 2 ^ 64) :
    p + BitVec.ofNat 64 a + BitVec.ofInt 64 (-1) = p + BitVec.ofNat 64 (a - 1) := by
  rw [BitVec.add_assoc]
  refine congrArg (p + ·) ?_
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt ha', VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (by omega),
    show (BitVec.ofInt 64 (-1)).toNat = 2 ^ 64 - 1 by simp]
  omega

theorem getD_bytesAt_eq (m : Mem) (p : Addr) {k n : Nat} (hk : k < n) :
    m (p + BitVec.ofNat 64 k) = (bytesAt m p n).getD k 0 := by
  rw [List.getD_eq_getElem?_getD]; simp [bytesAt, hk]

/-- A byte written into a list of 16. -/
theorem getD_set16 (L : List Byte) (hL : L.length = 16) {o : Nat} (ho : o < 16) (b : Byte) {k : Nat}
    (hk : k < 16) : (L.take o ++ [b] ++ L.drop (o + 1)).getD k 0 = if k = o then b else L.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rcases Nat.lt_trichotomy k o with h | rfl | h
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_take_of_lt h]
    simp [show k ≠ o by omega]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp [show min k L.length = k by omega]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_take, List.length_singleton, List.getElem?_drop,
      show ¬ k = o by omega, ↓reduceIte]
    congr 2; omega

/-- What `nonceBlock` leaves. -/
structure NoncePost (W : Addr) (t : Nat) (nonce : List Byte) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 botO, 8⟩] s.mem s'.mem
  blk : blockAtMem s'.mem (W + BitVec.ofNat 64 tmpO) = nonceN t nonce &&& ~~~(63 : Block)
  bot : s'.mem.readW (W + BitVec.ofNat 64 botO) 64 = BitVec.ofNat 64 ((nonceN t nonce).extractLsb' 0 6).toNat
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .rbx → r ≠ .r12 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem nonceBlock_ok {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {N : Addr} {nl t : Nat}
    (hN : s.mem.readW (W + BitVec.ofNat 64 nO) 64 = N) (hnl : s.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ nl) (h15 : nl ≤ 15) (ht : t < 2 ^ 64)
    (hB : Buf W SP s N nl) :
    WP isa nonceBlock s (VG.Proof.AesOcb.X86_64.NoncePost W t (bytesAt s.mem N nl) s) := by
  have h15r := E.r15
  simp only [nO, nlO, tlO] at hN hnl htl
  -- `zero16 tmpO`
  obtain ⟨s₁, run₁, B₁⟩ := zero16_ok (s := s) (d := tmpO) h15r (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have h15₁ : s₁.gpr .r15 = W := by rw [B₁.gpr _ (by decide), h15r]
  have kept₁ : ∀ {d}, (d + 8 ≤ tmpO ∨ tmpO + 16 ≤ d) → d + 8 ≤ 2560 →
      s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun h₁ h₂ =>
    B₁.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (by simp only [tmpO] at h₁ ⊢; omega) h₂ (by decide)) (by decide)
  -- the pointers and the count
  obtain ⟨s₂, run₂, rbx₂, r12₂, rsi₂, rcx₂, g₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [VG.Impl.AesOcb.X86_64.ld .rbx .r15 nO, VG.Impl.AesOcb.X86_64.ld .r12 .r15 nlO, mvr .rsi .r15, addi .rsi (tmpO + 16), .alu .sub .rsi (.reg .r12),
        .mov .rcx (.imm 0)] s₁ = some s₂ ∧
      s₂.gpr .rbx = N ∧ s₂.gpr .r12 = BitVec.ofNat 64 nl ∧ s₂.gpr .rsi = W + BitVec.ofNat 64 (128 - nl) ∧
      s₂.gpr .rcx = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .rsi → r ≠ .rcx → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have r₁ : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 nO) 8 := by rw [B₁.rd, B₁.wr]; exact E.perm.wR (by decide)
    have r₂ : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 nlO) 8 := by rw [B₁.rd, B₁.wr]; exact E.perm.wR (by decide)
    have hN₁ := kept₁ (d := nO) (by decide) (by decide)
    have hnl₁ := kept₁ (d := nlO) (by decide) (by decide)
    simp only [nO, nlO] at r₁ r₂ hN₁ hnl₁
    refine ⟨_, by orun [h15₁, r₁, r₂, hN₁, hnl₁, hN, hnl], ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₁]
      exact Offset.add_ofNat_sub W (by omega)
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, BitVec.xor_self, sext0]
    · simp only [gpr_setReg, gpr_arithFlags, h1, h2, h3, h4, ite_false]
    all_goals rfl
  have eN : bytesAt s₂.mem N nl = bytesAt s.mem N nl := by
    rw [m₂]
    exact Proof.AesCcm.X86_64.bytesAt_frame B₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hB.w.sub_right (Lay.wSub (by decide))) (by omega)
  have hS₂ : Covers [⟨N, nl⟩] (s₂.rd ++ s₂.wr) := by rw [rd₂, wr₂, B₁.rd, B₁.wr]; exact hB.rd
  have hD₂ : Covers [⟨W + BitVec.ofNat 64 (128 - nl), nl⟩] s₂.wr := by
    rw [wr₂, B₁.wr]; exact E.perm.wC (by omega)
  have hSD : (⟨N, nl⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (128 - nl), nl⟩ := hB.w.sub_right (Lay.wSub (by omega))
  unfold nonceBlock
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₁, Option.bind_some, run₂], ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.copyLoop_ok s₂ (by omega) (by omega) rbx₂ rsi₂ rcx₂ r12₂ hS₂ hD₂ hSD) fun s₃ h₃ => ?_)
  obtain ⟨m₃, rcx₃, g₃, rd₃, wr₃⟩ := h₃
  rw [eN] at m₃
  have h15₃ : s₃.gpr .r15 = W := by
    rw [g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide), h15₁]
  have rsi₃ : s₃.gpr .rsi = W + BitVec.ofNat 64 (128 - nl) := by rw [g₃ _ (by decide) (by decide), rsi₂]
  have ea₁ : s₃.gpr .rsi + BitVec.ofInt 64 (-1) = W + BitVec.ofNat 64 (127 - nl) := by
    rw [rsi₃, VG.Proof.AesOcb.X86_64.sub_one_addr W (by omega) (by omega), show 128 - nl - 1 = 127 - nl by omega]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂, B₁.wr]
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂, B₁.rd]
  have w127n : InRegions s₃.wr (W + BitVec.ofNat 64 (127 - nl)) 1 := by rw [wr₃']; exact E.perm.wW (by omega)
  have rtl : InRegions (s₃.rd ++ s₃.wr) (W + BitVec.ofNat 64 224) 8 := by rw [rd₃', wr₃']; exact E.perm.wR (by decide)
  have r112 : InRegions (s₃.rd ++ s₃.wr) (W + BitVec.ofNat 64 112) 1 := by rw [rd₃', wr₃']; exact E.perm.wR (by decide)
  have w112 : InRegions s₃.wr (W + BitVec.ofNat 64 112) 1 := by rw [wr₃']; exact E.perm.wW (by decide)
  have r127 : InRegions (s₃.rd ++ s₃.wr) (W + BitVec.ofNat 64 127) 1 := by rw [rd₃', wr₃']; exact E.perm.wR (by decide)
  have w127 : InRegions s₃.wr (W + BitVec.ofNat 64 127) 1 := by rw [wr₃']; exact E.perm.wW (by decide)
  have w256 : InRegions s₃.wr (W + BitVec.ofNat 64 256) 8 := by rw [wr₃']; exact E.perm.wW (by decide)
  -- the 1 before the nonce
  obtain ⟨s₄, run₄, m₄, g₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa [.mov .rax (.imm 1),
      .store8 { base := .rsi, disp := -1 } .rax] s₃ = some s₄ ∧
      s₄.mem = s₃.mem.writeW (W + BitVec.ofNat 64 (127 - nl)) (1 : Byte) ∧
      (∀ r, r ≠ .rax → s₄.gpr r = s₃.gpr r) ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    refine ⟨_, by orun [ea₁, w127n], ?_, fun r h => ?_, ?_, ?_⟩
    · simp only [mem_setReg, sext1]; rfl
    · simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  -- `TAGLEN mod 128` in the top bits of a byte
  have fr₃ : Frame [⟨W + BitVec.ofNat 64 (128 - nl), nl⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact writeBytes_frame _ _ _ (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact VG.Proof.AesOcb.X86_64.contains_pre _ (by omega))
  have htl₄ : s₄.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [m₄, Mem.readW_writeW_sep (Offset.sep W (by omega) (by decide) (by omega)) (by decide),
      fr₃.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by omega)) (by decide) (by omega))
        (by decide), m₂]
    exact (kept₁ (d := 224) (by decide) (by decide)).trans htl
  have h15₄ : s₄.gpr .r15 = W := by rw [g₄ _ (by decide), h15₃]
  obtain ⟨s₅, run₅, rax₅, g₅, m₅, rd₅, wr₅⟩ : ∃ s₅, runBlock isa [VG.Impl.AesOcb.X86_64.ld .rax .r15 tlO, .alu .and .rax (.imm 15),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax)] s₄ = some s₅ ∧ s₅.gpr .rax = BitVec.ofNat 64 (16 * (t % 16)) ∧
      (∀ r, r ≠ .rax → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    have r₄ : InRegions (s₄.rd ++ s₄.wr) (W + BitVec.ofNat 64 224) 8 := by rw [rd₄, wr₄]; exact rtl
    have e15 : BitVec.signExtend 64 (15 : BitVec 32) = 15#64 := by decide
    refine ⟨_, by orun [h15₄, r₄, htl₄], ?_, fun r h => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, e15, and15', VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt ht, ← BitVec.ofNat_add]
      congr 1; omega
    · simp only [gpr_setReg, gpr_arithFlags, h, ite_false]
    all_goals rfl
  have h15₅ : s₅.gpr .r15 = W := by rw [g₅ _ (by decide), h15₄]
  have r112₅ : InRegions (s₅.rd ++ s₅.wr) (W + BitVec.ofNat 64 112) 1 := by rw [rd₅, wr₅, rd₄, wr₄]; exact r112
  have w112₅ : InRegions s₅.wr (W + BitVec.ofNat 64 112) 1 := by rw [wr₅, wr₄]; exact w112
  obtain ⟨s₆, run₆, m₆, g₆, rd₆, wr₆⟩ : ∃ s₆, runBlock isa [.movzx8 .rcx (at_ .r15 tmpO), .alu .or .rcx (.reg .rax),
      .store8 (at_ .r15 tmpO) .rcx] s₅ = some s₆ ∧
      s₆.mem = s₅.mem.writeW (W + BitVec.ofNat 64 112)
        (s₅.mem (W + BitVec.ofNat 64 112) ||| BitVec.ofNat 8 (16 * (t % 16))) ∧
      (∀ r, r ≠ .rcx → s₆.gpr r = s₅.gpr r) ∧ s₆.rd = s₅.rd ∧ s₆.wr = s₅.wr := by
    refine ⟨_, by orun [h15₅, r112₅, w112₅], ?_, fun r h => ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, rax₅]
      rw [VG.Proof.AesOcb.X86_64.or_byte _ (by omega)]
    · simp only [gpr_setReg, gpr_arithFlags, h, ite_false]
    all_goals rfl
  have h15₆ : s₆.gpr .r15 = W := by rw [g₆ _ (by decide), h15₅]
  have r127₆ : InRegions (s₆.rd ++ s₆.wr) (W + BitVec.ofNat 64 127) 1 := by
    rw [rd₆, wr₆, rd₅, wr₅, rd₄, wr₄]; exact r127
  have w127₆ : InRegions s₆.wr (W + BitVec.ofNat 64 127) 1 := by rw [wr₆, wr₅, wr₄]; exact w127
  have w256₆ : InRegions s₆.wr (W + BitVec.ofNat 64 256) 8 := by rw [wr₆, wr₅, wr₄]; exact w256
  obtain ⟨s₇, run₇, m₇, g₇, rd₇, wr₇⟩ : ∃ s₇, runBlock isa [.movzx8 .rax (at_ .r15 (tmpO + 15)), mvr .rcx .rax,
      .alu .and .rcx (.imm 63), st .r15 botO .rcx, .alu .and .rax (.imm 0xc0), .store8 (at_ .r15 (tmpO + 15)) .rax]
      s₆ = some s₇ ∧
      s₇.mem = (s₆.mem.writeW (W + BitVec.ofNat 64 256)
          (BitVec.ofNat 64 ((s₆.mem (W + BitVec.ofNat 64 127)).toNat % 64))).writeW (W + BitVec.ofNat 64 127)
        (s₆.mem (W + BitVec.ofNat 64 127) &&& BitVec.ofNat 8 192) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s₇.gpr r = s₆.gpr r) ∧ s₇.rd = s₆.rd ∧ s₇.wr = s₆.wr := by
    have e63 : BitVec.signExtend 64 (63 : BitVec 32) = BitVec.ofNat 64 63 := by decide
    have e192 : BitVec.signExtend 64 (0xc0 : BitVec 32) = BitVec.ofNat 64 192 := by decide
    refine ⟨_, by orun [h15₆, r127₆, w127₆, w256₆], ?_, fun r h1 h2 => ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e63,
        e192, VG.Proof.AesOcb.X86_64.and63, VG.Proof.AesOcb.X86_64.and_byte _ (show 192 < 256 by decide)]
    · simp only [gpr_setReg, gpr_arithFlags, h1, h2, ite_false]
    all_goals rfl
  -- the bytes at `W + tmpO`, step by step
  have hlen : (bytesAt s.mem N nl).length = nl := VG.Proof.AesCcm.X86_64.length_bytesAt _ _ _
  have L₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros 16 := by
    rw [m₂]; exact VG.Proof.AesOcb.X86_64.bytesAt_of_zero B₁.val
  have e128 : W + BitVec.ofNat 64 (128 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (16 - nl) := by
    rw [Offset.add_add, show 112 + (16 - nl) = 128 - nl by omega]
  have e127 : W + BitVec.ofNat 64 (127 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (15 - nl) := by
    rw [Offset.add_add, show 112 + (15 - nl) = 127 - nl by omega]
  have L₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros (16 - nl) ++ bytesAt s.mem N nl := by
    rw [m₃, e128, VG.Proof.AesCcm.X86_64.bytesAt_writeBytes_at _ _ _ (by omega) (by decide), L₂, hlen]
    rw [show 16 - nl + nl = 16 by omega]
    simp only [Spec.Ocb.zeros, List.take_replicate, List.drop_replicate, show min (16 - nl) 16 = 16 - nl by omega,
      Nat.sub_self, List.replicate_zero, List.append_nil]
  have L₄ : bytesAt s₄.mem (W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros (15 - nl) ++ [1] ++ bytesAt s.mem N nl := by
    rw [m₄, e127, VG.Proof.AesCcm.X86_64.bytesAt_writeW8_at _ _ _ (by omega) (by decide), L₃]
    simp only [Spec.Ocb.zeros, List.take_append, List.take_replicate, List.drop_append, List.drop_replicate,
      List.length_replicate, show min (15 - nl) (16 - nl) = 15 - nl by omega, show 15 - nl - (16 - nl) = 0 by omega,
      show 16 - nl - (15 - nl + 1) = 0 by omega, show 15 - nl + 1 - (16 - nl) = 0 by omega, List.take_zero,
      List.drop_zero, List.replicate_zero, List.nil_append, List.append_nil, List.append_assoc]
  have L₄d : ∀ k < 16, (bytesAt s₄.mem (W + BitVec.ofNat 64 112) 16).getD k 0 = nbase (bytesAt s.mem N nl) k :=
    fun k hk => by
      have := Proof.Ocb.nbase_list (bytesAt s.mem N nl) (by rw [hlen]; omega) (by rw [hlen]; omega) hk
      rw [hlen] at this; rw [L₄]; exact this
  have e127' : W + BitVec.ofNat 64 127 = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 15 := (Offset.add_add W 112 15).symm
  have h0 : W + BitVec.ofNat 64 112 + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 112 := BitVec.add_zero _
  have b0e : s₅.mem (W + BitVec.ofNat 64 112) = nbase (bytesAt s.mem N nl) 0 := by
    have := VG.Proof.AesOcb.X86_64.getD_bytesAt_eq s₄.mem (W + BitVec.ofNat 64 112) (k := 0) (n := 16) (by decide)
    rw [h0] at this
    rw [m₅, this, L₄d 0 (by decide)]
  have L₆d : ∀ k < 16, (bytesAt s₆.mem (W + BitVec.ofNat 64 112) 16).getD k 0 = VG.Proof.Ocb.nb t (bytesAt s.mem N nl) k := by
    intro k hk
    rw [m₆, VG.Proof.AesCcm.X86_64.bytesAt_writeW8_base _ _ _ (by decide) (by decide), b0e, m₅]
    unfold VG.Proof.Ocb.nb
    rcases k with _ | k
    · rfl
    · simp only [List.getD_cons_succ, show k + 1 ≠ 0 by omega, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
        show 1 + k = k + 1 by omega]
      exact L₄d (k + 1) hk
  have b15e : s₆.mem (W + BitVec.ofNat 64 127) = VG.Proof.Ocb.nb t (bytesAt s.mem N nl) 15 := by
    rw [e127', VG.Proof.AesOcb.X86_64.getD_bytesAt_eq s₆.mem (W + BitVec.ofNat 64 112) (k := 15) (n := 16) (by decide), L₆d 15 (by decide)]
  have fr256 : ∀ v : BitVec 64, Frame [⟨W + BitVec.ofNat 64 256, 8⟩] s₆.mem (s₆.mem.writeW (W + BitVec.ofNat 64 256) v) :=
    fun v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have L₇d : ∀ k < 16, (bytesAt s₇.mem (W + BitVec.ofNat 64 112) 16).getD k 0 =
      if k = 15 then VG.Proof.Ocb.nb t (bytesAt s.mem N nl) 15 &&& 0xc0 else VG.Proof.Ocb.nb t (bytesAt s.mem N nl) k := by
    intro k hk
    generalize hb : s₆.mem (W + BitVec.ofNat 64 127) = b at m₇ b15e
    rw [m₇, e127', VG.Proof.AesCcm.X86_64.bytesAt_writeW8_at _ _ (o := 15) (n := 16) _ (by decide) (by decide),
      Proof.AesCcm.X86_64.bytesAt_frame (fr256 _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := 112) (n := 16) (d := 256) (k := 8) (.inl (by decide)) (by decide) (by decide))
        (by decide),
      VG.Proof.AesOcb.X86_64.getD_set16 _ (VG.Proof.AesCcm.X86_64.length_bytesAt _ _ _) (by decide) _ hk, b15e]
    split
    · rfl
    · exact L₆d k hk
  have hlen16 := VG.Proof.AesCcm.X86_64.length_bytesAt s₇.mem (W + BitVec.ofNat 64 112) 16
  -- the whole block
  have run : runBlock isa ([.mov .rax (.imm 1), .store8 { base := .rsi, disp := -1 } .rax] ++
      ([VG.Impl.AesOcb.X86_64.ld .rax .r15 tlO, .alu .and .rax (.imm 15), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax)] ++
      ([.movzx8 .rcx (at_ .r15 tmpO), .alu .or .rcx (.reg .rax), .store8 (at_ .r15 tmpO) .rcx] ++
      [.movzx8 .rax (at_ .r15 (tmpO + 15)), mvr .rcx .rax, .alu .and .rcx (.imm 63), st .r15 botO .rcx,
        .alu .and .rax (.imm 0xc0), .store8 (at_ .r15 (tmpO + 15)) .rax]))) s₃ = some s₇ := by
    rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₄, Option.bind_some, VG.Proof.AesCcm.X86_64.runBlock_append, run₅, Option.bind_some, VG.Proof.AesCcm.X86_64.runBlock_append, run₆,
      Option.bind_some, run₇]
  refine WP.of_runBlock ⟨s₇, run, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the frame
    have F₁ : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 botO, 8⟩] s.mem s₃.mem :=
      (B₁.frame.mono (fun r hr => by simp at hr; simp [hr])).trans (by
        rw [← m₂]
        exact fr₃.sub fun r hr => ⟨_, List.mem_cons_self .., by
          simp only [List.mem_singleton] at hr; subst hr
          rw [e128]; exact Offset.sub_base _ (by omega)⟩)
    rw [m₇, m₆, m₅, m₄]
    refine (((F₁.writeW (List.mem_cons_self ..) _ ?_).writeW (List.mem_cons_self ..) _ ?_).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ ?_).writeW (List.mem_cons_self ..) _ ?_
    · rw [e127]; exact Offset.contains_base _ (by omega) (by omega)
    · show (⟨W + BitVec.ofNat 64 112, 16⟩ : Region).Contains (W + BitVec.ofNat 64 112) 1
      exact VG.Proof.AesOcb.X86_64.contains_pre _ (by decide)
    · exact Region.contains_self _ _
    · rw [e127']; exact Offset.contains_base _ (by decide) (by decide)
  · -- the block
    show blockAtMem s₇.mem (W + BitVec.ofNat 64 112) = _
    rw [blockAtMem]
    apply Proof.Ocb.toBytes_inj
    rw [Proof.Ocb.toBytes_ofBytes hlen16]
    refine Proof.Cmac.ext16 hlen16 (Proof.Ocb.toBytes_length _) fun k hk => ?_
    rw [L₇d k hk, Proof.Ocb.nonceN_masked_byte _ _ (by omega) (by omega) hk]
  · -- `bottom`
    show s₇.mem.readW (W + BitVec.ofNat 64 256) 64 = _
    rw [m₇, Mem.readW_writeW_sep (Offset.sep W (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64, b15e, Proof.Ocb.nonceN_bottom _ _ (by omega) (by omega)]
  · intro r h1 h2 h3 h4 h5
    rw [g₇ r h1 h2, g₆ r h2, g₅ r h1, g₄ r h1, g₃ r h1 h2, g₂ r h4 h5 h3 h2, B₁.gpr r (by simp [h1])]
  · rw [rd₇, rd₆, rd₅, rd₄, rd₃']
  · rw [wr₇, wr₆, wr₅, wr₄, wr₃']

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.Offset0`. -/
section

/-!
# AES-OCB on x86-64: `Offset_0` (`offset0`)

Untrusted: everything here is checked by Lean. `offset0` loads `Ktop` as
two byte-reversed words, computes the third word of `Stretch`
(`Proof.Ocb.stretch_words`), shifts the three words left by `bottom` in six
masked stages (`stage_ok`, `Proof.Ocb.shl_stages`), and stores the top two,
byte-reversed, to `W + ofsO` and `W + o0O` (`offset0_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (shlIf ror_mask sel_mask shl3 bit_bottom)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt)

theorem sel_mask' (x x' : BitVec 64) (b : Bool) :
    x ^^^ ((x' ^^^ x) &&& (0#64 - (if b then 1 else 0))) = if b then x' else x := sel_mask x x' b

theorem bit_bottom0 {v : Nat} (hv : v < 64) :
    BitVec.ofNat 64 v &&& BitVec.signExtend 64 (1 : BitVec 32) = if v.testBit 0 then 1 else 0 := by
  have := bit_bottom hv 0
  rwa [BitVec.ushiftRight_zero] at this

/-- One stage: the three words shifted left by `a` if bit `k` of `bottom` is set. -/
theorem stage_ok (s : State) {k a v : Nat} (hk6 : k < 64) (ha : 0 < a) (ha' : a < 64) (hv : v < 64)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa (stage k a) s = some s' ∧
      s'.gpr .rax ++ s'.gpr .rdx ++ s'.gpr .rcx = shlIf (v.testBit k) a (s.gpr .rax ++ s.gpr .rdx ++ s.gpr .rcx) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hm : 0#64 - ((BitVec.ofNat 64 v >>> k) &&& BitVec.signExtend 64 (1 : BitVec 32)) =
      0#64 - (if v.testBit k then 1 else 0) := by rw [bit_bottom hv]
  have c1 : 1 ≤ 64 - a ∧ 64 - a ≤ 63 := ⟨by omega, by omega⟩
  by_cases hk : k = 0
  · subst hk
    refine ⟨_, by orun [stage, hbx, c1, List.flatMap_cons, List.flatMap_nil], ?_, fun r h1 h2 h3 h4 h5 h6 h7 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx,
        BitVec.xor_self, VG.Proof.AesOcb.X86_64.bit_bottom0 hv, ror_mask _ ha ha', VG.Proof.AesOcb.X86_64.sel_mask']
      unfold shlIf
      split
      · exact shl3 _ _ _ ha ha'
      · rfl
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h1, h2, h3, h4, h5, h6, h7, ite_false]
    all_goals rfl
  · have ck : 1 ≤ k ∧ k ≤ 63 := ⟨by omega, by omega⟩
    refine ⟨_, by orun [stage, hbx, hk, c1, ck, List.flatMap_cons, List.flatMap_nil], ?_, fun r h1 h2 h3 h4 h5 h6 h7 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx,
        BitVec.xor_self, hm, ror_mask _ ha ha', VG.Proof.AesOcb.X86_64.sel_mask']
      unfold shlIf
      split
      · exact shl3 _ _ _ ha ha'
      · rfl
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h1, h2, h3, h4, h5, h6, h7, ite_false]
    all_goals rfl

/-- The top two of three words. -/
theorem top2 (x y z : BitVec 64) : (x ++ y ++ z).extractLsb' 64 128 = x ++ y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    show ¬ 64 + i < 64 by omega, ↓reduceIte, show 64 + i - 64 = i by omega]

/-- `Stretch` shifted left by `bottom`: its top 128 bits are `Offset_0`. -/
def stretch (ktop : Block) : BitVec 192 := ktop ++ (ktop.extractLsb' 64 64 ^^^ ktop.extractLsb' 56 64)

/-- What `offset0` leaves. -/
structure Off0Post (W : Addr) (o : Block) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 o0O, 16⟩] s.mem s'.mem
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) = o
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .rbx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
    s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem offset0_ok {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {v : Nat} (hv : v < 64)
    (hbot : s.mem.readW (W + BitVec.ofNat 64 botO) 64 = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa offset0 s = some s' ∧
      VG.Proof.AesOcb.X86_64.Off0Post W ((VG.Proof.AesOcb.X86_64.stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128) s s' := by
  have h15 := E.r15
  simp only [botO] at hbot
  -- `Stretch` in three words
  obtain ⟨s₁, run₁, w₁, rbx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [VG.Impl.AesOcb.X86_64.ld .rax .r15 tmpO, .bswap .rax, VG.Impl.AesOcb.X86_64.ld .rdx .r15 (tmpO + 8), .bswap .rdx,
       mvr .rcx .rax, .shift .ror .rcx 56, .movImm64 .r8 (BitVec.allOnes 64 <<< 8),
       .alu .and .rcx (.reg .r8), mvr .r8 .rdx, .shift .shr .r8 56, .alu .or .rcx (.reg .r8),
       .alu .xor .rcx (.reg .rax), VG.Impl.AesOcb.X86_64.ld .rbx .r15 botO] s = some s₁ ∧
      s₁.gpr .rax ++ s₁.gpr .rdx ++ s₁.gpr .rcx = VG.Proof.AesOcb.X86_64.stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO)) ∧
      s₁.gpr .rbx = BitVec.ofNat 64 v ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .rbx → r ≠ .r8 → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    have r₀ := E.perm.wR (show 112 + 8 ≤ 2560 by decide)
    have r₁ := E.perm.wR (show 120 + 8 ≤ 2560 by decide)
    have r₂ := E.perm.wR (show 256 + 8 ≤ 2560 by decide)
    have rm := ror_mask (bswap64 (s.mem.readW (W + BitVec.ofNat 64 112) 64)) (a := 8) (by decide) (by decide)
    simp only [show 64 - 8 = 56 from rfl] at rm
    refine ⟨_, by orun [h15, r₀, r₁, r₂, hbot], ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, rm]
      have hb : blockAtMem s.mem (W + BitVec.ofNat 64 tmpO) =
          bswap64 (s.mem.readW (W + BitVec.ofNat 64 112) 64) ++ bswap64 (s.mem.readW (W + BitVec.ofNat 64 120) 64) := by
        have := Proof.Gcm.X86_64.blockAt_bswap s.mem (W + BitVec.ofNat 64 112)
        rw [show W + BitVec.ofNat 64 112 + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 112 from BitVec.add_zero _,
          Offset.add_add] at this
        exact this.symm
      rw [VG.Proof.AesOcb.X86_64.stretch, hb, Proof.Ocb.stretch_words]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbot]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h1, h2, h3, h4, h5, ite_false]
    all_goals rfl
  -- the six stages
  have keep : ∀ {t t' : State}, (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
      t'.gpr r = t.gpr r) → t.gpr .rbx = BitVec.ofNat 64 v → t'.gpr .rbx = BitVec.ofNat 64 v := fun g h => by
    rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h]
  obtain ⟨s₂, run₂, w₂, g₂, m₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86_64.stage_ok s₁ (k := 0) (a := 1) (by decide) (by decide) (by decide) hv rbx₁
  obtain ⟨s₃, run₃, w₃, g₃, m₃, rd₃, wr₃⟩ := VG.Proof.AesOcb.X86_64.stage_ok s₂ (k := 1) (a := 2) (by decide) (by decide) (by decide) hv
    (keep g₂ rbx₁)
  obtain ⟨s₄, run₄, w₄, g₄, m₄, rd₄, wr₄⟩ := VG.Proof.AesOcb.X86_64.stage_ok s₃ (k := 2) (a := 4) (by decide) (by decide) (by decide) hv
    (keep g₃ (keep g₂ rbx₁))
  obtain ⟨s₅, run₅, w₅, g₅, m₅, rd₅, wr₅⟩ := VG.Proof.AesOcb.X86_64.stage_ok s₄ (k := 3) (a := 8) (by decide) (by decide) (by decide) hv
    (keep g₄ (keep g₃ (keep g₂ rbx₁)))
  obtain ⟨s₆, run₆, w₆, g₆, m₆, rd₆, wr₆⟩ := VG.Proof.AesOcb.X86_64.stage_ok s₅ (k := 4) (a := 16) (by decide) (by decide) (by decide) hv
    (keep g₅ (keep g₄ (keep g₃ (keep g₂ rbx₁))))
  obtain ⟨s₇, run₇, w₇, g₇, m₇, rd₇, wr₇⟩ := VG.Proof.AesOcb.X86_64.stage_ok s₆ (k := 5) (a := 32) (by decide) (by decide) (by decide) hv
    (keep g₆ (keep g₅ (keep g₄ (keep g₃ (keep g₂ rbx₁)))))
  have hw : s₇.gpr .rax ++ s₇.gpr .rdx ++ s₇.gpr .rcx =
      VG.Proof.AesOcb.X86_64.stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO)) <<< v := by
    rw [w₇, w₆, w₅, w₄, w₃, w₂, w₁, Proof.Ocb.shl_stages _ hv]
  have hO : s₇.gpr .rax ++ s₇.gpr .rdx =
      (VG.Proof.AesOcb.X86_64.stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [← VG.Proof.AesOcb.X86_64.top2 _ _ (s₇.gpr .rcx), hw, Proof.Ocb.offset_shl _ (by omega)]
  -- the stores
  have hm₇ : s₇.mem = s.mem := by rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁]
  have hrd₇ : s₇.rd = s.rd := by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]
  have hwr₇ : s₇.wr = s.wr := by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]
  have h15₇ : s₇.gpr .r15 = W := by
    rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), h15]
  have w₁₆ : InRegions s₇.wr (W + BitVec.ofNat 64 16) 8 := by rw [hwr₇]; exact E.perm.wW (by decide)
  have w₂₄ : InRegions s₇.wr (W + BitVec.ofNat 64 24) 8 := by rw [hwr₇]; exact E.perm.wW (by decide)
  have w₂₇₂ : InRegions s₇.wr (W + BitVec.ofNat 64 272) 8 := by rw [hwr₇]; exact E.perm.wW (by decide)
  have w₂₈₀ : InRegions s₇.wr (W + BitVec.ofNat 64 280) 8 := by rw [hwr₇]; exact E.perm.wW (by decide)
  obtain ⟨s₈, run₈, m₈, g₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa [.bswap .rax, .bswap .rdx, st .r15 ofsO .rax,
      st .r15 (ofsO + 8) .rdx, st .r15 o0O .rax, st .r15 (o0O + 8) .rdx] s₇ = some s₈ ∧
      s₈.mem = (((s₇.mem.writeW (W + BitVec.ofNat 64 16) (bswap64 (s₇.gpr .rax))).writeW (W + BitVec.ofNat 64 24)
        (bswap64 (s₇.gpr .rdx))).writeW (W + BitVec.ofNat 64 272) (bswap64 (s₇.gpr .rax))).writeW
        (W + BitVec.ofNat 64 280) (bswap64 (s₇.gpr .rdx)) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → s₈.gpr r = s₇.gpr r) ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by orun [h15₇, w₁₆, w₂₄, w₂₇₂, w₂₈₀], ?_, fun r h1 h2 => ?_, ?_, ?_⟩
    · simp only [mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, h1, h2, ite_false]
    all_goals rfl
  have val : Spec.Ocb.ofBytes (Proof.Cmac.le8 (bswap64 (s₇.gpr .rax)) ++ Proof.Cmac.le8 (bswap64 (s₇.gpr .rdx))) =
      (VG.Proof.AesOcb.X86_64.stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [Proof.CmacAes.X86_64.le8_bswap, ← Proof.Ocb.toBytes_eq, Proof.Ocb.ofBytes_toBytes, hO]
  have run : runBlock isa offset0 s = some s₈ := by
    unfold offset0
    rw [VG.Proof.AesCcm.X86_64.runBlock_append, VG.Proof.AesCcm.X86_64.runBlock_append, VG.Proof.AesCcm.X86_64.runBlock_append, VG.Proof.AesCcm.X86_64.runBlock_append, VG.Proof.AesCcm.X86_64.runBlock_append, VG.Proof.AesCcm.X86_64.runBlock_append,
      VG.Proof.AesCcm.X86_64.runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some, run₃, Option.bind_some, run₄,
      Option.bind_some, run₅, Option.bind_some, run₆, Option.bind_some, run₇, Option.bind_some, run₈]
  have f272 : ∀ M : Mem, Frame [⟨W + BitVec.ofNat 64 272, 16⟩] M
      ((M.writeW (W + BitVec.ofNat 64 272) (bswap64 (s₇.gpr .rax))).writeW (W + BitVec.ofNat 64 280)
        (bswap64 (s₇.gpr .rdx))) := fun M => by
    rw [← addr8 W 272]; exact frame_store2 _ _ _ _
  refine ⟨s₈, run, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 h7 h8 => ?_, by rw [rd₈, hrd₇], by rw [wr₈, hwr₇]⟩
  · rw [m₈, ← hm₇]
    show Frame [⟨W + BitVec.ofNat 64 16, 16⟩, ⟨W + BitVec.ofNat 64 272, 16⟩] _ _
    exact ((((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (VG.Proof.AesOcb.X86_64.contains_pre _ (by decide))).writeW
      (List.mem_cons_self ..) _ (Offset.contains W (e := 16) (k := 16) (d := 24) (n := 8) (by decide) (by decide)
        (by decide))).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (VG.Proof.AesOcb.X86_64.contains_pre _ (by decide))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
        (Offset.contains W (e := 272) (k := 16) (d := 280) (n := 8) (by decide) (by decide) (by decide))
  · show blockAtMem s₈.mem (W + BitVec.ofNat 64 16) = _
    rw [m₈, blockAtMem]
    rw [Proof.AesCcm.X86_64.bytesAt_frame (f272 _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 16) (n := 16) (d := 272) (k := 16) (.inl (by decide)) (by decide) (by decide)) (by decide)]
    rw [← blockAtMem, show W + BitVec.ofNat 64 24 = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 from (addr8 W 16).symm,
      blockAtMem_store2, val]
  · show blockAtMem s₈.mem (W + BitVec.ofNat 64 272) = _
    rw [m₈, show W + BitVec.ofNat 64 280 = W + BitVec.ofNat 64 272 + BitVec.ofNat 64 8 from (addr8 W 272).symm,
      blockAtMem_store2, val]
  · rw [g₈ r h1 h2, g₇ r h1 h2 h3 h5 h6 h7 h8, g₆ r h1 h2 h3 h5 h6 h7 h8, g₅ r h1 h2 h3 h5 h6 h7 h8,
      g₄ r h1 h2 h3 h5 h6 h7 h8, g₃ r h1 h2 h3 h5 h6 h7 h8, g₂ r h1 h2 h3 h5 h6 h7 h8, g₁ r h1 h2 h3 h4 h5]

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.Nonce`. -/
section

/-!
# AES-OCB on x86-64: `Offset_0` from the nonce (`nonce`)

Untrusted: everything here is checked by Lean. `nonce` writes `Nonce` with
its last 6 bits cleared and `bottom` (`nonceBlock_ok`), enciphers the block
(`Ktop`, `callBlocks_ok`), and computes `Offset_0` (`offset0_ok`), to
`W + ofsO` and `W + o0O` (`nonce_ok`): §4.2's `Offset_0`
(`Proof.Ocb.offset0_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxCiph)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (bytesAt_frame)

/-- The functions an instance calls. -/
def callees (v : BlocksImpl) : Callees := ⟨v.enc, v.dec, v.expand⟩

/-- A frame within the parts the pieces write. -/
theorem mut_of {W SP D : Addr} {n : Nat} {rs : List Region} {m m' : Mem} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, ∃ r' ∈ mutR W SP D n, Region.Sub r r') : Frame (mutR W SP D n) m m' := h.sub hs

/-- The key schedule, after a frame within the parts the pieces write. -/
theorem ctxCiph_mut {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩)
    {m m' : Mem} (h : Frame (mutR W SP D n) m m') {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    ctxCiph m' K R = ctxCiph m K R := by
  unfold ctxCiph
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [VG.Proof.AesCcm.X86_64.bytesAt_frame h (fun r hr => (k_mut L hD r hr).sub_left (Region.sub_prefix hRb)) (by omega)]

theorem sub_wA {W : Addr} {d k : Nat} (h : d + k ≤ 160) : Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ (wA W) := by
  simpa using Offset.sub W (d := d) (n := k) (e := 0) (k := 160) (by omega) (by omega)

theorem sub_wB {W : Addr} {d k : Nat} (h₁ : 248 ≤ d) (h : d + k ≤ 288) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ (wB W) := Offset.sub W (by omega) (by omega)

theorem sub_wC {W : Addr} {d k : Nat} (h₁ : 384 ≤ d) (h : d + k ≤ 2560) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ (wC W) := Offset.sub W (by omega) (by omega)

/-- A word of `W` that the pieces do not write. -/
theorem kept_read {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {m m' : Mem} (h : Frame (mutR W SP D n) m m') {d : Nat}
    (hd : 160 ≤ d ∧ d + 8 ≤ 248 ∨ 288 ≤ d ∧ d + 8 ≤ 384) :
    m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  h.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_mut L hDW hd) (by decide)

/-- The slots, after a frame within the parts the pieces write. -/
theorem Slots.of_mut {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {m m' : Mem} (h : Frame (mutR W SP D n) m m') {R : Nat} {N A D' : Addr} {nl n' tl : Nat}
    (S : Slots W R N A D' nl n' tl m) : Slots W R N A D' nl n' tl m' where
  data := by rw [VG.Proof.AesOcb.X86_64.kept_read L hDW h (by decide), S.data]
  len := by rw [VG.Proof.AesOcb.X86_64.kept_read L hDW h (by decide), S.len]
  tl := by rw [VG.Proof.AesOcb.X86_64.kept_read L hDW h (by decide), S.tl]
  rounds := by rw [VG.Proof.AesOcb.X86_64.kept_read L hDW h (by decide), S.rounds]
  aad := by rw [VG.Proof.AesOcb.X86_64.kept_read L hDW h (by decide), S.aad]
  nonce := by rw [VG.Proof.AesOcb.X86_64.kept_read L hDW h (by decide), S.nonce]
  nlen := by rw [VG.Proof.AesOcb.X86_64.kept_read L hDW h (by decide), S.nlen]

/-- What `nonce` writes: the parts of `W` the pieces write and the stack. -/
abbrev nonceR (W SP : Addr) : List Region := [⟨W + BitVec.ofNat 64 16, 144⟩, wB W, wC W, below SP 8]

theorem nonceR_mut {W SP D : Addr} {n : Nat} {m m' : Mem} (h : Frame (VG.Proof.AesOcb.X86_64.nonceR W SP) m m') :
    Frame (mutR W SP D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩
  all_goals exact ⟨_, by simp, fun _ h => h⟩

/-- What `nonce` leaves. -/
structure NonceOk (K W SP D : Addr) (n : Nat) (o : Block) (s s' : State) : Prop where
  env : Env K W SP s'
  frame : Frame (VG.Proof.AesOcb.X86_64.nonceR W SP) s.mem s'.mem
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) = o
  alen : s'.mem.readW (W + BitVec.ofNat 64 alenO) 64 = s.mem.readW (W + BitVec.ofNat 64 alenO) 64
  keep : ∀ {d : Nat}, 32 ≤ d → d + 16 ≤ 112 → blockAtMem s'.mem (W + BitVec.ofNat 64 d) = blockAtMem s.mem (W + BitVec.ofNat 64 d)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem nonce_ok (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {N D : Addr} {nl t n : Nat}
    (hrnd : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    (hN : s.mem.readW (W + BitVec.ofNat 64 nO) 64 = N) (hnl : s.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ nl) (h15 : nl ≤ 15) (ht : t < 2 ^ 64)
    (hB : Buf W SP s N nl) (hKD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa (nonce (VG.Proof.AesOcb.X86_64.callees v)) s
      (VG.Proof.AesOcb.X86_64.NonceOk K W SP D n (Spec.Ocb.offset0 (ctxCiph s.mem K R) t (bytesAt s.mem N nl)) s) := by
  unfold nonce
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.nonceBlock_ok L E hN hnl htl h1 h15 ht hB) fun s₁ P₁ => ?_)
  have E₁ : Env K W SP s₁ := E.keep (fun r hr => P₁.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    P₁.rd P₁.wr
  have F₁ : Frame (VG.Proof.AesOcb.X86_64.nonceR W SP) s.mem s₁.mem := P₁.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), VG.Proof.AesOcb.X86_64.sub_wB (by decide) (by decide)⟩
  have hrnd₁ : s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [VG.Proof.AesOcb.X86_64.kept_read L hDW (VG.Proof.AesOcb.X86_64.nonceR_mut F₁) (by decide), hrnd]
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNosp v.encDepth L E₁ hR
    hrnd₁ (oneBlock_ok E₁.r15 tmpO (by decide)) (dstW L E₁.perm (d := tmpO) (n := 1) (by decide))) fun s₂ P₂ => ?_)
  have E₂ : Env K W SP s₂ := E₁.of_saved P₂.saved P₂.rd P₂.wr
  have F₂ : Frame (VG.Proof.AesOcb.X86_64.nonceR W SP) s₁.mem s₂.mem := P₂.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), VG.Proof.AesOcb.X86_64.sub_wC (by decide) (by decide)⟩
    · rw [E₁.rsp]; exact ⟨_, by simp, fun _ h => h⟩
  have ktop : blockAtMem s₂.mem (W + BitVec.ofNat 64 tmpO) =
      ctxCiph s.mem K R (Proof.Ocb.nonceN t (bytesAt s.mem N nl) &&& ~~~(63 : Block)) := by
    have := P₂.enc (i := 0) (by decide)
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this, P₁.blk]
    exact congrFun (VG.Proof.AesOcb.X86_64.ctxCiph_mut L hKD (VG.Proof.AesOcb.X86_64.nonceR_mut F₁) hR) _
  have hbv : ((Proof.Ocb.nonceN t (bytesAt s.mem N nl)).extractLsb' 0 6).toNat < 64 :=
    (BitVec.extractLsb' 0 6 _).isLt
  have bot₂ : s₂.mem.readW (W + BitVec.ofNat 64 botO) 64 =
      BitVec.ofNat 64 ((Proof.Ocb.nonceN t (bytesAt s.mem N nl)).extractLsb' 0 6).toNat := by
    rw [P₂.frame.readW (r := ⟨W + BitVec.ofNat 64 botO, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · rw [E₁.rsp]; exact (L.stk_w' (by decide)).symm) (by decide), P₁.bot]
  obtain ⟨s₃, run₃, P₃⟩ := VG.Proof.AesOcb.X86_64.offset0_ok L E₂ hbv bot₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine ⟨E₂.keep (fun r hr => P₃.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) P₃.rd P₃.wr,
    F₁.trans (F₂.trans (P₃.frame.sub fun r hr => ?_)), ?_, ?_, ?_, fun {d} h₁ h₂ => ?_, by rw [P₃.rd, P₂.rd, P₁.rd],
    by rw [P₃.wr, P₂.wr, P₁.wr]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), VG.Proof.AesOcb.X86_64.sub_wB (by decide) (by decide)⟩
  · rw [P₃.ofs, ktop, Proof.Ocb.offset0_eq]; rfl
  · rw [P₃.o0, ktop, Proof.Ocb.offset0_eq]; rfl
  · have k : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' →
        (∀ r ∈ rs, (⟨W + BitVec.ofNat 64 alenO, 8⟩ : Region).Disjoint r) →
        m'.readW (W + BitVec.ofNat 64 alenO) 64 = m.readW (W + BitVec.ofNat 64 alenO) 64 :=
      fun h hd => h.readW (r := ⟨W + BitVec.ofNat 64 alenO, 8⟩) (Region.contains_self _ _) hd (by decide)
    rw [k P₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.w_w (by decide) (by decide) (by decide)),
      k P₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.w_w (by decide) (by decide) (by decide)
        · exact L.w_w (by decide) (by decide) (by decide)
        · rw [E₁.rsp]; exact (L.stk_w' (by decide)).symm),
      k P₁.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.w_w (by decide) (by decide) (by decide))]
  · rw [VG.Proof.AesOcb.X86_64.blockAtMem_frame P₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.w_w (by simp only [ofsO, o0O]; omega) (by omega) (by decide)),
      VG.Proof.AesOcb.X86_64.blockAtMem_frame P₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.w_w (by simp only [tmpO]; omega) (by omega) (by decide)
        · exact L.w_w (by omega) (by omega) (by decide)
        · rw [E₁.rsp]; exact (L.stk_w' (by omega)).symm),
      VG.Proof.AesOcb.X86_64.blockAtMem_frame P₁.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.w_w (by simp only [tmpO, botO]; omega) (by omega) (by decide))]


end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.LNtz`. -/
section

/-!
# AES-OCB on x86-64: `L_{ntz(i)}` (`lNtz`)

Untrusted: everything here is checked by Lean. `lNtz` copies `L_0` to
`W + lO` and doubles it while the block index `i` (in `rbp`), shifted right
once more each time (in `r11`), is even: `ntz(i)` times (`lNtz_ok`). The
invariant: after `j` doublings, `W + lO` holds `L_j`, `r11` is `i / 2^j`,
which is positive, and `ntz(i) = j + ntz(i / 2^j)`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Ocb (Block blockAtMem double lAt ntz)
open VG.Proof.AesCcm.X86_64 (runBlock_append eval_e eval_ne toNat_ofNat_of_lt)

theorem even_zf {v : Nat} (hv : v < 2 ^ 64) :
    (BitVec.ofNat 64 v &&& BitVec.signExtend 64 (1 : BitVec 32) == 0) = decide (v % 2 = 0) := by
  rw [sext1]
  have : BitVec.ofNat 64 v &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (v % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt hv, VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (by decide), Nat.and_one_is_mod,
      VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (by omega)]
  rw [this]
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> rw [h] <;> decide

theorem shr1 {v : Nat} (hv : v < 2 ^ 64) : BitVec.ofNat 64 v >>> 1 = BitVec.ofNat 64 (v / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt hv, VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (by omega), Nat.shiftRight_eq_div_pow]

/-- What `lNtz` leaves. -/
structure LNtzPost (W : Addr) (l : Block) (i : Nat) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem s'.mem
  val : blockAtMem s'.mem (W + BitVec.ofNat 64 lO) = lAt l (ntz i)
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r11 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem lNtz_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {l : Block} {i : Nat} (hi : 0 < i)
    (hi' : i < 2 ^ 64) (hbp : s.gpr .rbp = BitVec.ofNat 64 i)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa lNtz s (VG.Proof.AesOcb.X86_64.LNtzPost W l i s) := by
  have h15 := E.r15
  obtain ⟨s₁, run₁, B₁⟩ := copy16_ok (s := s) (a := l0O) (d := lO) h15 (E.perm.wR (by decide))
    (E.perm.wR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  obtain ⟨s₂, run₂, r11₂, zf₂, g₂, m₂, rd₂, wr₂⟩ : ∃ s₂,
      runBlock isa [mvr .r11 .rbp, .alu .test .r11 (.imm 1)] s₁ = some s₂ ∧
      s₂.gpr .r11 = BitVec.ofNat 64 i ∧ s₂.zf = some (decide (i % 2 = 0)) ∧
      (∀ r, r ≠ .r11 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have hbp₁ : s₁.gpr .rbp = BitVec.ofNat 64 i := by rw [B₁.gpr _ (by decide), hbp]
    refine ⟨_, by orun [hbp₁], ?_, ?_, fun r h => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hbp₁]
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hbp₁, VG.Proof.AesOcb.X86_64.even_zf hi']
    · simp only [gpr_setReg, gpr_arithFlags, h, ite_false]
    all_goals rfl
  have post_of : ∀ t : State, Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem →
      blockAtMem t.mem (W + BitVec.ofNat 64 lO) = lAt l (ntz i) →
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r11 → t.gpr r = s₂.gpr r) →
      t.rd = s.rd → t.wr = s.wr → VG.Proof.AesOcb.X86_64.LNtzPost W l i s t := fun t fr v g rd wr =>
    ⟨fr, v, fun r h1 h2 h3 h4 h5 => by
      rw [g r h1 h2 h3 h4 h5, g₂ r h5, B₁.gpr r (by simp [h1, h2])], rd, wr⟩
  have fr₂ : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem s₂.mem := by rw [m₂]; exact B₁.frame
  have v₂ : blockAtMem s₂.mem (W + BitVec.ofNat 64 lO) = lAt l 0 := by rw [m₂, B₁.val, hl0]
  unfold lNtz
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₁, Option.bind_some, run₂], ?_⟩)
  refine WP.ite (decide (i % 2 = 0)) (eval_e zf₂) (fun hb => ?_)
    (fun hb => WP.block_nil (post_of s₂ fr₂ ?_ (fun _ _ _ _ _ _ => rfl) (by rw [rd₂, B₁.rd]) (by rw [wr₂, B₁.wr])))
  rotate_left
  · rw [v₂, Proof.Ocb.ntz_odd (by simpa using hb)]
  have he : i % 2 = 0 := of_decide_eq_true hb
  refine WP.loop (M := isa) (c := .e)
    (fun (k : Nat) (t : State) => ∃ j, k = i / 2 ^ j ∧ 0 < i / 2 ^ j ∧ i / 2 ^ j % 2 = 0 ∧
      ntz i = j + ntz (i / 2 ^ j) ∧ t.gpr .r11 = BitVec.ofNat 64 (i / 2 ^ j) ∧
      Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem ∧ blockAtMem t.mem (W + BitVec.ofNat 64 lO) = lAt l j ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r11 → t.gpr r = s₂.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr) ?_ (i / 2 ^ 0) _
    ⟨0, rfl, by simpa using hi, by simpa using he, by simp, by simpa using r11₂, fr₂, v₂,
      fun _ _ _ _ _ _ => rfl, by rw [rd₂, B₁.rd], by rw [wr₂, B₁.wr]⟩
  rintro k t ⟨j, rfl, hpos, hev, hntz, r11, fr, v, g, rd, wr⟩
  have hv : i / 2 ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi'
  have h15t : t.gpr .r15 = W := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide),
    g₂ _ (by decide), B₁.gpr _ (by decide), h15]
  obtain ⟨t₁, runt₁, D₁⟩ := dbl_ok (s := t) (b := .r15) (a := lO) (d := lO) h15t h15t (by decide)
    (by rw [rd, wr]; exact E.perm.wR (by decide)) (by rw [rd, wr]; exact E.perm.wR (by decide))
    (by rw [wr]; exact E.perm.wW (by decide)) (by rw [wr]; exact E.perm.wW (by decide))
  have r11₁ : t₁.gpr .r11 = BitVec.ofNat 64 (i / 2 ^ j) := by rw [D₁.gpr _ (by decide), r11]
  obtain ⟨t₂, runt₂, r11₂', zf₂', g₂', m₂', rd₂', wr₂'⟩ : ∃ t₂,
      runBlock isa [.shift .shr .r11 1, .alu .test .r11 (.imm 1)] t₁ = some t₂ ∧
      t₂.gpr .r11 = BitVec.ofNat 64 (i / 2 ^ (j + 1)) ∧ t₂.zf = some (decide (i / 2 ^ (j + 1) % 2 = 0)) ∧
      (∀ r, r ≠ .r11 → t₂.gpr r = t₁.gpr r) ∧ t₂.mem = t₁.mem ∧ t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr := by
    have e : i / 2 ^ (j + 1) = i / 2 ^ j / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    refine ⟨_, by orun [r11₁], ?_, ?_, fun r h => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, r11₁, VG.Proof.AesOcb.X86_64.shr1 hv, e]
    · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, ite_true, r11₁, VG.Proof.AesOcb.X86_64.shr1 hv, e,
        VG.Proof.AesOcb.X86_64.even_zf (show i / 2 ^ j / 2 < 2 ^ 64 by omega)]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h, ite_false]
    all_goals rfl
  refine WP.of_runBlock ⟨t₂, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, runt₁, Option.bind_some, runt₂], ?_⟩
  have e : i / 2 ^ (j + 1) = i / 2 ^ j / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  have fr' : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t₂.mem := by
    rw [m₂']
    exact fun x hx => (D₁.frame x hx).trans (fr x hx)
  have v' : blockAtMem t₂.mem (W + BitVec.ofNat 64 lO) = lAt l (j + 1) := by rw [m₂', D₁.val, v]; rfl
  have g' : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r11 → t₂.gpr r = s₂.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [g₂' r h5, D₁.gpr r (by simp [h1, h2, h3, h4]), g r h1 h2 h3 h4 h5]
  have hntz' : ntz i = (j + 1) + ntz (i / 2 ^ (j + 1)) := by
    rw [hntz, Proof.Ocb.ntz_even hpos hev, e]; omega
  by_cases hodd : i / 2 ^ (j + 1) % 2 = 0
  · right
    refine ⟨(eval_e zf₂').trans (by simp [hodd]), i / 2 ^ (j + 1), by rw [e]; omega, j + 1, rfl,
      by rw [e]; omega, hodd, hntz', r11₂', fr', v', g', by rw [rd₂', D₁.rd, rd], by rw [wr₂', D₁.wr, wr]⟩
  · left
    refine ⟨(eval_e zf₂').trans (by simp [hodd]), post_of t₂ fr' ?_ g' (by rw [rd₂', D₁.rd, rd])
      (by rw [wr₂', D₁.wr, wr])⟩
    rw [v', hntz', Proof.Ocb.ntz_odd (by omega)]

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.HashFill`. -/
section

/-!
# AES-OCB on x86-64: filling the buffer of `HASH` (`hashFill`)

Untrusted: everything here is checked by Lean. `hashFill` computes the next
offset of `HASH`, `Offset_{i+1} = Offset_i ⊕ L_{ntz(i+1)}` (`lNtz_ok`,
`xor16_ok`), and writes the next block of the associated data XORed with it
to the next slot of the buffer at `W + bufO` (`hashFill_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt)
open VG.Proof.Cmac (le8)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt imm_eq)

theorem add_ofNat_imm (p : Addr) (a k : Nat) (hk : k < 2 ^ 31) :
    p + BitVec.ofNat 64 a + BitVec.signExtend 64 (BitVec.ofNat 32 k) = p + BitVec.ofNat 64 (a + k) := by
  rw [imm_eq hk, Offset.add_add]

theorem ofNat_imm (a k : Nat) (hk : k < 2 ^ 31) :
    BitVec.ofNat 64 a + BitVec.signExtend 64 (BitVec.ofNat 32 k) = BitVec.ofNat 64 (a + k) := by
  rw [imm_eq hk, ← BitVec.ofNat_add]

/-- What one `hashFill` leaves. -/
structure FillPost (W A : Addr) (l : Block) (j i c : Nat) (t t' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ohO, 16⟩,
    ⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩] t.mem t'.mem
  oh : blockAtMem t'.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1)
  buf : blockAtMem t'.mem (W + BitVec.ofNat 64 (384 + 16 * i)) =
    blockAtMem t.mem (A + BitVec.ofNat 64 (16 * (j + i))) ^^^ offAt 0 l (j + i + 1)
  rbx : t'.gpr .rbx = A + BitVec.ofNat 64 (16 * (j + i + 1))
  rbp : t'.gpr .rbp = BitVec.ofNat 64 (j + i + 2)
  rsi : t'.gpr .rsi = W + BitVec.ofNat 64 (384 + 16 * (i + 1))
  r13 : t'.gpr .r13 = BitVec.ofNat 64 (i + 1)
  zf : t'.zf = some (decide (i + 1 = c))
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r11 → r ≠ .rsi → r ≠ .rbx → r ≠ .rbp →
    r ≠ .r13 → t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem hashFill_ok {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {A : Addr} {l : Block}
    {j i c : Nat} (hi : i < c) (hc : c ≤ 8) (hj : j + i + 2 < 2 ^ 61)
    (hbp : t.gpr .rbp = BitVec.ofNat 64 (j + i + 1)) (hbx : t.gpr .rbx = A + BitVec.ofNat 64 (16 * (j + i)))
    (hsi : t.gpr .rsi = W + BitVec.ofNat 64 (384 + 16 * i)) (h13 : t.gpr .r13 = BitVec.ofNat 64 i)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 c)
    (hl0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hoh : blockAtMem t.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i))
    (hA : Covers [⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩] (t.rd ++ t.wr))
    (hAW : (⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa hashFill t (VG.Proof.AesOcb.X86_64.FillPost W A l j i c t) := by
  unfold hashFill
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.lNtz_ok E (by omega) (by omega) hbp hl0) fun t₁ P₁ => ?_)
  have h15₁ : t₁.gpr .r15 = W := by rw [P₁.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), E.r15]
  obtain ⟨t₂, run₂, B₂⟩ := xor16_ok (s := t₁) (b := .r15) (a := lO) (d := ohO) h15₁ h15₁ (by decide) (by decide)
    (by rw [P₁.rd, P₁.wr]; exact E.perm.wR (by decide)) (by rw [P₁.rd, P₁.wr]; exact E.perm.wR (by decide))
    (by rw [P₁.wr]; exact E.perm.wW (by decide)) (by rw [P₁.wr]; exact E.perm.wW (by decide))
  have oh₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1) := by
    rw [B₂.val, P₁.val, VG.Proof.AesOcb.X86_64.blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), hoh]
    rfl
  have g₂ : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r11 → t₂.gpr r = t.gpr r := fun r h1 h2 h3 h4 h5 => by
    rw [B₂.gpr r (by simp [h1, h2]), P₁.gpr r h1 h2 h3 h4 h5]
  have hbx₂ : t₂.gpr .rbx = A + BitVec.ofNat 64 (16 * (j + i)) := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), hbx]
  have hsi₂ : t₂.gpr .rsi = W + BitVec.ofNat 64 (384 + 16 * i) := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), hsi]
  have h15₂ : t₂.gpr .r15 = W := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), E.r15]
  have hbp₂ : t₂.gpr .rbp = BitVec.ofNat 64 (j + i + 1) := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), hbp]
  have h13₂ : t₂.gpr .r13 = BitVec.ofNat 64 i := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h13]
  have h12₂ : t₂.gpr .r12 = BitVec.ofNat 64 c := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h12]
  have rd₂ : t₂.rd = t.rd := by rw [B₂.rd, P₁.rd]
  have wr₂ : t₂.wr = t.wr := by rw [B₂.wr, P₁.wr]
  have fr₂ : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ohO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  have eA : blockAtMem t₂.mem (A + BitVec.ofNat 64 (16 * (j + i))) = blockAtMem t.mem (A + BitVec.ofNat 64 (16 * (j + i))) :=
    VG.Proof.AesOcb.X86_64.blockAtMem_frame fr₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hAW.sub_right (Lay.wSub (by decide))
  have ea0 : A + BitVec.ofNat 64 (16 * (j + i)) + BitVec.ofNat 64 0 = A + BitVec.ofNat 64 (16 * (j + i)) :=
    BitVec.add_zero _
  have ew0 : W + BitVec.ofNat 64 (384 + 16 * i) + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 (384 + 16 * i) :=
    BitVec.add_zero _
  have rA₀ : InRegions (t₂.rd ++ t₂.wr) (A + BitVec.ofNat 64 (16 * (j + i))) 8 := by
    rw [rd₂, wr₂]; simpa using Proof.AesCcm.X86_64.in_off (d := 0) (n := 8) hA (by decide) (by decide)
  have rA₈ : InRegions (t₂.rd ++ t₂.wr) (A + BitVec.ofNat 64 (16 * (j + i)) + BitVec.ofNat 64 8) 8 := by
    rw [rd₂, wr₂]; exact Proof.AesCcm.X86_64.in_off (d := 8) (n := 8) hA (by decide) (by decide)
  have rO₀ : InRegions (t₂.rd ++ t₂.wr) (W + BitVec.ofNat 64 144) 8 := by rw [rd₂, wr₂]; exact E.perm.wR (by decide)
  have rO₈ : InRegions (t₂.rd ++ t₂.wr) (W + BitVec.ofNat 64 152) 8 := by rw [rd₂, wr₂]; exact E.perm.wR (by decide)
  have wS₀ : InRegions t₂.wr (W + BitVec.ofNat 64 (384 + 16 * i)) 8 := by rw [wr₂]; exact E.perm.wW (by omega)
  have wS₈ : InRegions t₂.wr (W + BitVec.ofNat 64 (384 + 16 * i) + BitVec.ofNat 64 8) 8 := by
    rw [wr₂, Offset.add_add]; exact E.perm.wW (by omega)
  refine WP.of_runBlock ⟨_, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₂, Option.bind_some]; orun [hbx₂, hsi₂, h15₂, hbp₂, h13₂,
    h12₂, ea0, ew0, rA₀, rA₈, rO₀, rO₈, wS₀, wS₈], ?_⟩
  have fs : ∀ (M : Mem) (v₀ v₁ : BitVec 64), Frame [⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩] M
      ((M.writeW (W + BitVec.ofNat 64 (384 + 16 * i)) v₀).writeW (W + BitVec.ofNat 64 (384 + 16 * i) + 8#64) v₁) :=
    fun M v₀ v₁ => frame_store2 _ _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags]
    exact (fr₂.mono (by simp)).trans ((fs _ _ _).mono (by simp))
  · simp only [mem_setReg, mem_arithFlags]
    rw [VG.Proof.AesOcb.X86_64.blockAtMem_frame (fs _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 144) (n := 16) (d := 384 + 16 * i) (k := 16) (.inl (by omega)) (by decide) (by omega)), oh₂]
  · simp only [mem_setReg, mem_arithFlags]
    rw [blockAtMem_store2, show W + 152#64 = W + BitVec.ofNat 64 144 + BitVec.ofNat 64 8 from (addr8 W 144).symm,
      blockAtMem_xor_words, eA, show W + BitVec.ofNat 64 144 = W + BitVec.ofNat 64 ohO from rfl, oh₂]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx₂, Offset.add_add]
    rw [show 16 * (j + i) + 16 = 16 * (j + i + 1) by omega]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbp₂, ← BitVec.ofNat_add]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hsi₂, Offset.add_add]
    rw [show 384 + 16 * i + 16 = 384 + 16 * (i + 1) by omega]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h13₂, ← BitVec.ofNat_add]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h13₂, h12₂,
      ← BitVec.ofNat_add]
    rw [Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  · simp only [gpr_setReg, gpr_arithFlags, h1, h2, h3, h4, h5, h6, h7, h8, h9, ite_false]
    exact g₂ r h1 h2 h3 h4 h5
  · simp only [rd_setReg, rd_arithFlags]; exact rd₂
  · simp only [wr_setReg, wr_arithFlags]; exact wr₂

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.HashChunk`. -/
section

/-!
# AES-OCB on x86-64: a chunk of `HASH` (`hashChunk`)

Untrusted: everything here is checked by Lean. After `j` of the `m` whole
blocks of the associated data `a`, `HInv` holds: the sum and the offset of
`HASH` are `Sum_j` and `Offset_j` (`Proof.Ocb.hsum`, `Proof.Ocb.offAt`),
`rbx` points at block `j`, `rbp` is `j + 1`, and `m − j` is kept in `W`.
`hashChunk` takes `c = min(8, m − j)` blocks: fills the buffer with each
block XORed with its offset (`fill_ok`), enciphers the buffer, adds it to
the sum (`hashSum_ok`), and leaves `HInv` at `j + c` (`hashChunk_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz ctxCiph ctxLstar)
open VG.Proof.Ocb (offAt hsum)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt imm_eq eval_e eval_ne eval_b bytesAt_frame)

/-- What `HASH` writes: the sum, `L_{ntz(i)}`, the rest's length and the
offset (`[48, 64)`, `[96, 160)`), the blocks left, the buffer and the working
space of the functions called, and the stack below `SP`. -/
abbrev hashR (W SP : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 48, 16⟩, ⟨W + BitVec.ofNat 64 96, 64⟩, ⟨W + BitVec.ofNat 64 248, 8⟩, wC W, below SP 8]

theorem hashR_mut {W SP D : Addr} {n : Nat} {m m' : Mem} (h : Frame (VG.Proof.AesOcb.X86_64.hashR W SP) m m') :
    Frame (mutR W SP D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), VG.Proof.AesOcb.X86_64.sub_wB (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- What holds of `HASH` of `a` (at `A`) after `j` of its whole blocks, from
the state `s₀` at its start. -/
structure HInv (K W SP D : Addr) (n : Nat) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ s : State) (j : Nat) : Prop where
  env : Env K W SP s
  frame : Frame (VG.Proof.AesOcb.X86_64.hashR W SP) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  le : j ≤ a.length / 16
  sum : blockAtMem s.mem (W + BitVec.ofNat 64 sumO) = hsum ciph l a j
  oh : blockAtMem s.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l j
  rbx : s.gpr .rbx = A + BitVec.ofNat 64 (16 * j)
  rbp : s.gpr .rbp = BitVec.ofNat 64 (j + 1)
  alen : s.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 (a.length / 16 - j)
  rest : s.mem.readW (W + BitVec.ofNat 64 tmpO) 64 = BitVec.ofNat 64 (a.length % 16)
  l0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0

/-- What a chunk of `HASH` needs of its start, `s₀`: the key context's
cipher and `L_*`, the associated data (apart from `W`, the stack and the
data at `D`), the rounds in `W`. -/
structure HCtx (K W SP D : Addr) (n R : Nat) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ : State) : Prop where
  lay : Lay K W SP
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  ciph : ctxCiph s₀.mem K R = ciph
  lstar : ctxLstar s₀.mem K = l
  buf : Buf W SP s₀ A a.length
  aad : bytesAt s₀.mem A a.length = a
  ad : (⟨A, a.length⟩ : Region).Disjoint ⟨D, n⟩
  kd : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩
  dw : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩
  rnd : s₀.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R
  short : a.length < 2 ^ 64

namespace HCtx

variable {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte} {s₀ : State}
  (C : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph l A a s₀)
include C

/-- The associated data misses the parts the pieces write. -/
theorem a_mut : ∀ r ∈ mutR W SP D n, (⟨A, a.length⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact C.buf.w.sub_right (Region.sub_prefix (by decide))
  · exact C.buf.w.sub_right (Lay.wSub (by decide))
  · exact C.buf.w.sub_right (Lay.wSub (by decide))
  · exact C.buf.stk.symm
  · exact C.ad

/-- Block `i` of the associated data, in a state after `s₀`. -/
theorem blk {m : Mem} (h : Frame (mutR W SP D n) s₀.mem m) {i : Nat} (hi : i < a.length / 16) :
    blockAtMem m (A + BitVec.ofNat 64 (16 * i)) = blockAt a i := by
  rw [← C.aad, Proof.Ocb.blockAt_bytesAt _ _ (by omega), VG.Proof.AesOcb.X86_64.blockAtMem_frame h fun r hr =>
    (C.a_mut r hr).sub_left (Offset.sub_base A (by omega))]

theorem rnd' {m : Mem} (h : Frame (mutR W SP D n) s₀.mem m) :
    m.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
  rw [VG.Proof.AesOcb.X86_64.kept_read C.lay C.dw h (by decide), C.rnd]

theorem ciph' {m : Mem} (h : Frame (mutR W SP D n) s₀.mem m) : ctxCiph m K R = ciph := by
  rw [VG.Proof.AesOcb.X86_64.ctxCiph_mut C.lay C.kd h C.rounds, C.ciph]

theorem lstar' {m : Mem} (h : Frame (mutR W SP D n) s₀.mem m) : ctxLstar m K = l := by
  rw [← C.lstar]
  show blockAtMem m (K + BitVec.ofNat 64 240) = blockAtMem s₀.mem (K + BitVec.ofNat 64 240)
  exact VG.Proof.AesOcb.X86_64.blockAtMem_frame h fun r hr => (k_mut C.lay C.kd r hr).sub_left (Lay.kSub (by decide))

end HCtx

/-! ## Filling the buffer -/

/-- The fill loop after `i` of the `c` blocks of a chunk from block `j`. -/
structure FillInv (K W SP D : Addr) (n : Nat) (ciph : Cipher) (l : Block) (A : Addr) (a : List Byte)
    (s₀ : State) (j c : Nat) (t : State) (i : Nat) : Prop where
  env : Env K W SP t
  frame : Frame (VG.Proof.AesOcb.X86_64.hashR W SP) s₀.mem t.mem
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  rbx : t.gpr .rbx = A + BitVec.ofNat 64 (16 * (j + i))
  rbp : t.gpr .rbp = BitVec.ofNat 64 (j + i + 1)
  rsi : t.gpr .rsi = W + BitVec.ofNat 64 (384 + 16 * i)
  r13 : t.gpr .r13 = BitVec.ofNat 64 i
  r12 : t.gpr .r12 = BitVec.ofNat 64 c
  oh : blockAtMem t.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i)
  buf : ∀ k < i, blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k)) = blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)
  sum : blockAtMem t.mem (W + BitVec.ofNat 64 sumO) = hsum ciph l a j
  alen : t.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 (a.length / 16 - j)
  rest : t.mem.readW (W + BitVec.ofNat 64 tmpO) 64 = BitVec.ofNat 64 (a.length % 16)
  l0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0

theorem fill_step {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte}
    {s₀ : State} (C : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph l A a s₀) {j c : Nat} (hc : c ≤ 8) (hjc : j + c ≤ a.length / 16)
    {t : State} {i : Nat} (hi : i < c) (F : VG.Proof.AesOcb.X86_64.FillInv K W SP D n ciph l A a s₀ j c t i) :
    WP isa hashFill t fun t' => VG.Proof.AesOcb.X86_64.FillInv K W SP D n ciph l A a s₀ j c t' (i + 1) ∧
      t'.zf = some (decide (i + 1 = c)) := by
  have L := C.lay
  have hA : Covers [⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩] (t.rd ++ t.wr) := by
    rw [F.rd, F.wr]; exact (C.buf.slice (a := 16 * (j + i)) (k := 16) (by omega)).rd
  have hAW : (⟨A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint ⟨W, 2560⟩ :=
    (C.buf.slice (a := 16 * (j + i)) (k := 16) (by omega)).w
  refine WP.mono (VG.Proof.AesOcb.X86_64.hashFill_ok L F.env hi hc (by have := C.short; omega) F.rbp F.rbx F.rsi F.r13 F.r12 F.l0 F.oh hA hAW)
    fun t' P => ⟨?_, P.zf⟩
  have hfr : ∀ r ∈ [(⟨W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ohO, 16⟩,
      ⟨W + BitVec.ofNat 64 (384 + 16 * i), 16⟩], ∃ r' ∈ VG.Proof.AesOcb.X86_64.hashR W SP, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
        VG.Proof.AesOcb.X86_64.sub_wC (by omega) (by omega)⟩
  have keepB : ∀ {d : Nat}, (d + 16 ≤ 96 ∨ (112 ≤ d ∧ d + 16 ≤ 144) ∨ (160 ≤ d ∧ d + 16 ≤ 384 + 16 * i) ∨
      384 + 16 * (i + 1) ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t'.mem (W + BitVec.ofNat 64 d) = blockAtMem t.mem (W + BitVec.ofNat 64 d) := fun h₁ h₂ =>
    VG.Proof.AesOcb.X86_64.blockAtMem_frame P.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 96) (k := 16) (by omega) h₂ (by decide)
      · exact L.w_w (a := _) (d := 144) (k := 16) (by omega) h₂ (by decide)
      · exact L.w_w (a := _) (d := 384 + 16 * i) (k := 16) (by omega) h₂ (by omega)
  have keepW : ∀ {d : Nat}, (d + 8 ≤ 96 ∨ (112 ≤ d ∧ d + 8 ≤ 144) ∨ (160 ≤ d ∧ d + 8 ≤ 384)) → d + 8 ≤ 2560 →
      t'.mem.readW (W + BitVec.ofNat 64 d) 64 = t.mem.readW (W + BitVec.ofNat 64 d) 64 := fun h₁ h₂ =>
    P.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 96) (k := 16) (by omega) h₂ (by decide)
      · exact L.w_w (a := _) (d := 144) (k := 16) (by omega) h₂ (by decide)
      · exact L.w_w (a := _) (d := 384 + 16 * i) (k := 16) (by omega) h₂ (by omega)) (by decide)
  refine
    { env := F.env.keep (fun r hr => P.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
          (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
          (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
          (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
          (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
          P.rd P.wr
      frame := F.frame.trans (P.frame.sub hfr)
      rd := by rw [P.rd, F.rd]
      wr := by rw [P.wr, F.wr]
      rbx := by rw [P.rbx, show j + i + 1 = j + (i + 1) by omega]
      rbp := by rw [P.rbp, show j + i + 2 = j + (i + 1) + 1 by omega]
      rsi := P.rsi
      r13 := P.r13
      r12 := by rw [P.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), F.r12]
      oh := by rw [P.oh]; rfl
      buf := fun k hk => ?_
      sum := by rw [keepB (by simp only [sumO]; omega) (by decide), F.sum]
      alen := by rw [keepW (by simp only [alenO]; omega) (by decide), F.alen]
      rest := by rw [keepW (by simp only [tmpO]; omega) (by decide), F.rest]
      l0 := by rw [keepB (by simp only [l0O]; omega) (by decide), F.l0] }
  rcases Nat.lt_or_ge k i with hk' | hk'
  · rw [keepB (by omega) (by omega), F.buf k hk']
  · obtain rfl : k = i := by omega
    rw [P.buf, C.blk (VG.Proof.AesOcb.X86_64.hashR_mut F.frame) (by omega)]

theorem fill_ok {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte}
    {s₀ : State} (C : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph l A a s₀) {j c : Nat} (hc0 : 0 < c) (hc : c ≤ 8)
    (hjc : j + c ≤ a.length / 16) {t : State} (F : VG.Proof.AesOcb.X86_64.FillInv K W SP D n ciph l A a s₀ j c t 0) :
    WP isa (.loop hashFill .ne) t fun t' => VG.Proof.AesOcb.X86_64.FillInv K W SP D n ciph l A a s₀ j c t' c := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ i, k = c - i ∧ i < c ∧ VG.Proof.AesOcb.X86_64.FillInv K W SP D n ciph l A a s₀ j c u i) ?_ (c - 0) _
    ⟨0, rfl, hc0, F⟩
  rintro k u ⟨i, rfl, hi, F⟩
  refine WP.mono (VG.Proof.AesOcb.X86_64.fill_step C hc hjc hi F) fun u' ⟨F', hz⟩ => ?_
  by_cases he : i + 1 = c
  · left; exact ⟨(eval_ne hz).trans (by simp [he]), he ▸ F'⟩
  · right; exact ⟨(eval_ne hz).trans (by simp [he]), c - (i + 1), by omega, i + 1, rfl, by omega, F'⟩

/-! ## Adding the buffer to the sum -/

theorem bufStart_ok {W : Addr} {t : State} (h15 : t.gpr .r15 = W) :
    ∃ t', runBlock isa bufStart t = some t' ∧ t'.gpr .r13 = BitVec.ofNat 64 0 ∧
      t'.gpr .rsi = W + BitVec.ofNat 64 (384 + 16 * 0) ∧
      (∀ r, r ≠ .r13 → r ≠ .rsi → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by orun [bufStart, h15], ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, BitVec.xor_self, sext0]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_setReg, gpr_arithFlags, h1, h2, ite_false]
  all_goals rfl

/-- The sum loop after `k` of the `c` blocks of the buffer. -/
theorem sumStep_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {k c : Nat} (hk : k < c)
    (hc : c ≤ 8) (hsi : t.gpr .rsi = W + BitVec.ofNat 64 (384 + 16 * k)) (h13 : t.gpr .r13 = BitVec.ofNat 64 k)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 c) :
    ∃ t', runBlock isa (xor16 .rsi 0 sumO ++ [addi .rsi 16, addi .r13 1, .alu .cmp .r13 (.reg .r12)]) t = some t' ∧
      BlkStep W sumO (blockAtMem t.mem (W + BitVec.ofNat 64 sumO) ^^^
        blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k))) [.rax, .rdx, .rsi, .r13] t t' ∧
      t'.gpr .rsi = W + BitVec.ofNat 64 (384 + 16 * (k + 1)) ∧ t'.gpr .r13 = BitVec.ofNat 64 (k + 1) ∧
      t'.zf = some (decide (k + 1 = c)) := by
  have h15 := E.r15
  have e0 : W + BitVec.ofNat 64 (384 + 16 * k) + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 (384 + 16 * k) :=
    BitVec.add_zero _
  obtain ⟨t₁, run₁, B₁⟩ := xor16_ok (s := t) (b := .rsi) (a := 0) (d := sumO) h15 hsi (by decide) (by decide)
    (by rw [e0]; exact E.perm.wR (by omega)) (by rw [Offset.add_add]; exact E.perm.wR (by omega))
    (E.perm.wW (by decide)) (E.perm.wW (by decide))
  rw [e0] at B₁
  have hsi₁ : t₁.gpr .rsi = W + BitVec.ofNat 64 (384 + 16 * k) := by rw [B₁.gpr _ (by decide), hsi]
  have h13₁ : t₁.gpr .r13 = BitVec.ofNat 64 k := by rw [B₁.gpr _ (by decide), h13]
  have h12₁ : t₁.gpr .r12 = BitVec.ofNat 64 c := by rw [B₁.gpr _ (by decide), h12]
  refine ⟨_, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₁, Option.bind_some]; orun [hsi₁, h13₁, h12₁], ?_, ?_, ?_, ?_⟩
  · exact ⟨B₁.frame, B₁.val, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
      exact B₁.gpr r (by simp [hr.1, hr.2.1]), B₁.rd, B₁.wr⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hsi₁, Offset.add_add]
    rw [show 384 + 16 * k + 16 = 384 + 16 * (k + 1) by omega]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h13₁, ← BitVec.ofNat_add]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h13₁, h12₁,
      ← BitVec.ofNat_add]
    rw [Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]

/-- `x` XORed with `g 0`, …, `g (k − 1)`. -/
def sumOf (x : Block) (g : Nat → Block) : Nat → Block
  | 0 => x
  | k + 1 => VG.Proof.AesOcb.X86_64.sumOf x g k ^^^ g k

theorem hsum_add (ciph : Cipher) (l : Block) (a : List Byte) (j : Nat) :
    ∀ c, hsum ciph l a (j + c) =
      VG.Proof.AesOcb.X86_64.sumOf (hsum ciph l a j) (fun k => ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1))) c
  | 0 => rfl
  | c + 1 => by rw [← Nat.add_assoc, hsum, VG.Proof.AesOcb.X86_64.hsum_add ciph l a j c]; rfl

theorem hashSum_ok {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {c : Nat} (hc0 : 0 < c)
    (hc : c ≤ 8) (h12 : t.gpr .r12 = BitVec.ofNat 64 c) {g : Nat → Block}
    (hg : ∀ k < c, blockAtMem t.mem (W + BitVec.ofNat 64 (384 + 16 * k)) = g k) :
    WP isa hashSum t fun t' => Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem t'.mem ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = VG.Proof.AesOcb.X86_64.sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g c ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rsi → r ≠ .r13 → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain ⟨t₁, run₁, r13₁, rsi₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86_64.bufStart_ok (W := W) (t := t) E.r15
  unfold hashSum
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ i, k = c - i ∧ i < c ∧ Env K W SP u ∧
      u.gpr .rsi = W + BitVec.ofNat 64 (384 + 16 * i) ∧ u.gpr .r13 = BitVec.ofNat 64 i ∧
      Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem u.mem ∧
      blockAtMem u.mem (W + BitVec.ofNat 64 sumO) = VG.Proof.AesOcb.X86_64.sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g i ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rsi → r ≠ .r13 → u.gpr r = t.gpr r) ∧ u.rd = t.rd ∧ u.wr = t.wr)
    ?_ (c - 0) _ ⟨0, rfl, hc0, E.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₁ wr₁, rsi₁, r13₁, by rw [m₁]; exact Frame.refl _ _,
      by rw [m₁]; rfl, fun r _ _ h3 h4 => g₁ r h4 h3, rd₁, wr₁⟩
  rintro k u ⟨i, rfl, hi, Eu, rsi, r13, fr, sum, gu, rd, wr⟩
  obtain ⟨u', run', B, rsi', r13', zf'⟩ := VG.Proof.AesOcb.X86_64.sumStep_ok Eu hi hc rsi r13 (by
    rw [gu _ (by decide) (by decide) (by decide) (by decide), h12])
  refine WP.of_runBlock ⟨u', run', ?_⟩
  have Eu' : Env K W SP u' := Eu.keep (fun r hr => B.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    B.rd B.wr
  have hbuf : blockAtMem u.mem (W + BitVec.ofNat 64 (384 + 16 * i)) = g i := by
    rw [VG.Proof.AesOcb.X86_64.blockAtMem_frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 384 + 16 * i) (n := 16) (d := 48) (k := 16) (.inr (by omega)) (by omega) (by decide),
      hg i hi]
  have fr' : Frame [⟨W + BitVec.ofNat 64 sumO, 16⟩] t.mem u'.mem := fr.trans B.frame
  have sum' : blockAtMem u'.mem (W + BitVec.ofNat 64 sumO) = VG.Proof.AesOcb.X86_64.sumOf (blockAtMem t.mem (W + BitVec.ofNat 64 sumO)) g (i + 1) := by
    rw [B.val, sum, hbuf]; rfl
  have gu' : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rsi → r ≠ .r13 → u'.gpr r = t.gpr r := fun r h1 h2 h3 h4 => by
    rw [B.gpr r (by simp [h1, h2, h3, h4]), gu r h1 h2 h3 h4]
  by_cases he : i + 1 = c
  · left
    exact ⟨(eval_ne zf').trans (by simp [he]), fr', he ▸ sum', gu', by rw [B.rd, rd], by rw [B.wr, wr]⟩
  · right
    exact ⟨(eval_ne zf').trans (by simp [he]), c - (i + 1), by omega, i + 1, rfl, by omega, Eu', rsi', r13', fr',
      sum', gu', by rw [B.rd, rd], by rw [B.wr, wr]⟩

/-! ## A chunk -/

/-- The `c` blocks of the buffer. -/
theorem bufArgs_ok {W : Addr} {t : State} (h15 : t.gpr .r15 = W) {c : Nat} (h12 : t.gpr .r12 = BitVec.ofNat 64 c) :
    ArgsOk [mvr .rdx .r15, addi .rdx bufO, mvr .rcx .r12] t (W + BitVec.ofNat 64 384) c := by
  refine ⟨_, by orun [h15, h12], ?_, ?_, fun r h1 h2 _ => ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h12]
  · simp only [gpr_setReg, gpr_arithFlags, h1, h2, ite_false]
  all_goals rfl

/-- The buffer of a chunk, with its `c` blocks in `r12`. -/
theorem chunkFill_ok {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph l A a s₀) {t : State} {j c : Nat}
    (H : VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ t j) (hc0 : 0 < c) (hc : c ≤ 8) (hjc : j + c ≤ a.length / 16)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 c) :
    WP isa (.seq (.block bufStart) (.loop hashFill .ne)) t fun t' => VG.Proof.AesOcb.X86_64.FillInv K W SP D n ciph l A a s₀ j c t' c := by
  have L := C.lay
  obtain ⟨t₁, run₁, r13₁, rsi₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86_64.bufStart_ok (W := W) (t := t) H.env.r15
  have F₀ : VG.Proof.AesOcb.X86_64.FillInv K W SP D n ciph l A a s₀ j c t₁ 0 :=
    { env := H.env.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
          (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₁ wr₁
      frame := by rw [m₁]; exact H.frame
      rd := by rw [rd₁, H.rd]
      wr := by rw [wr₁, H.wr]
      rbx := by rw [g₁ _ (by decide) (by decide), H.rbx]; rfl
      rbp := by rw [g₁ _ (by decide) (by decide), H.rbp]
      rsi := rsi₁
      r13 := r13₁
      r12 := by rw [g₁ _ (by decide) (by decide), h12]
      oh := by rw [m₁, H.oh]; rfl
      buf := fun k hk => absurd hk (Nat.not_lt_zero _)
      sum := by rw [m₁, H.sum]
      alen := by rw [m₁, H.alen]
      rest := by rw [m₁, H.rest]
      l0 := by rw [m₁, H.l0] }
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  exact WP.mono (VG.Proof.AesOcb.X86_64.fill_ok C hc0 hc hjc F₀) fun _ F => F

/-- A chunk from `bufStart` on, with its `c` blocks in `r12`. -/
theorem chunkRest_ok (v : BlocksImpl) {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph l A a s₀) {t : State} {j c : Nat}
    (H : VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ t j) (hc0 : 0 < c) (hc : c ≤ 8) (hjc : j + c ≤ a.length / 16)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 c) :
    WP isa (.seq (.block bufStart) (.seq (.loop hashFill .ne)
        (.seq (callBlocks (VG.Proof.AesOcb.X86_64.callees v).enc [mvr .rdx .r15, addi .rdx bufO, mvr .rcx .r12])
          (.seq hashSum (.block [VG.Impl.AesOcb.X86_64.ld .rax .r15 alenO, .alu .sub .rax (.reg .r12), st .r15 alenO .rax]))))) t
      fun t' => VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ t' (j + c) ∧ t'.zf = some (decide (a.length / 16 - (j + c) = 0)) := by
  have L := C.lay
  obtain ⟨t₁, run₁, r13₁, rsi₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86_64.bufStart_ok (W := W) (t := t) H.env.r15
  have F₀ : VG.Proof.AesOcb.X86_64.FillInv K W SP D n ciph l A a s₀ j c t₁ 0 :=
    { env := H.env.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
          (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₁ wr₁
      frame := by rw [m₁]; exact H.frame
      rd := by rw [rd₁, H.rd]
      wr := by rw [wr₁, H.wr]
      rbx := by rw [g₁ _ (by decide) (by decide), H.rbx]; rfl
      rbp := by rw [g₁ _ (by decide) (by decide), H.rbp]
      rsi := rsi₁
      r13 := r13₁
      r12 := by rw [g₁ _ (by decide) (by decide), h12]
      oh := by rw [m₁, H.oh]; rfl
      buf := fun k hk => absurd hk (Nat.not_lt_zero _)
      sum := by rw [m₁, H.sum]
      alen := by rw [m₁, H.alen]
      rest := by rw [m₁, H.rest]
      l0 := by rw [m₁, H.l0] }
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.fill_ok C hc0 hc hjc F₀) fun t₂ F => ?_)
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNosp v.encDepth L F.env
    C.rounds (C.rnd' (VG.Proof.AesOcb.X86_64.hashR_mut F.frame)) (VG.Proof.AesOcb.X86_64.bufArgs_ok F.env.r15 F.r12) (dstW L F.env.perm (d := 384) (n := c) (by omega)))
    fun t₃ P₃ => ?_)
  have E₃ : Env K W SP t₃ := F.env.of_saved P₃.saved P₃.rd P₃.wr
  have F₃ : Frame (VG.Proof.AesOcb.X86_64.hashR W SP) t₂.mem t₃.mem := P₃.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, VG.Proof.AesOcb.X86_64.sub_wC (by decide) (by omega)⟩
    · exact ⟨_, by simp, VG.Proof.AesOcb.X86_64.sub_wC (by decide) (by decide)⟩
    · rw [F.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩
  have k₃ : ∀ {d : Nat}, d + 16 ≤ 384 → blockAtMem t₃.mem (W + BitVec.ofNat 64 d) = blockAtMem t₂.mem (W + BitVec.ofNat 64 d) :=
    fun hd => VG.Proof.AesOcb.X86_64.blockAtMem_frame P₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by omega)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · rw [F.env.rsp]; exact (L.stk_w' (by omega)).symm
  have kw₃ : ∀ {d : Nat}, d + 8 ≤ 384 → t₃.mem.readW (W + BitVec.ofNat 64 d) 64 = t₂.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun hd => P₃.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by omega)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · rw [F.env.rsp]; exact (L.stk_w' (by omega)).symm) (by decide)
  have hg : ∀ k < c, blockAtMem t₃.mem (W + BitVec.ofNat 64 (384 + 16 * k)) =
      ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1)) := fun k hk => by
    have := P₃.enc hk
    rw [Offset.add_add] at this
    rw [this, F.buf k hk]
    exact congrFun (C.ciph' (VG.Proof.AesOcb.X86_64.hashR_mut F.frame)) _
  have h12₃ : t₃.gpr .r12 = BitVec.ofNat 64 c := by rw [P₃.saved _ (by decide), F.r12]
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.hashSum_ok L E₃ hc0 hc h12₃ hg) fun t₄ ⟨fr₄, sum₄, g₄, rd₄, wr₄⟩ => ?_)
  have E₄ : Env K W SP t₄ := E₃.keep (fun r hr => g₄ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₄ wr₄
  have k₄ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ 64 ≤ d) → d + 16 ≤ 2560 →
      blockAtMem t₄.mem (W + BitVec.ofNat 64 d) = blockAtMem t₃.mem (W + BitVec.ofNat 64 d) := fun h₁ h₂ =>
    VG.Proof.AesOcb.X86_64.blockAtMem_frame fr₄ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (a := _) (d := 48) (k := 16) (by omega) h₂ (by decide)
  have kw₄ : ∀ {d : Nat}, (d + 8 ≤ 48 ∨ 64 ≤ d) → d + 8 ≤ 2560 →
      t₄.mem.readW (W + BitVec.ofNat 64 d) 64 = t₃.mem.readW (W + BitVec.ofNat 64 d) 64 := fun h₁ h₂ =>
    fr₄.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (a := _) (d := 48) (k := 16) (by omega) h₂ (by decide))
      (by decide)
  have alen₄ : t₄.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 (a.length / 16 - j) := by
    rw [kw₄ (by simp only [alenO]; omega) (by decide), kw₃ (by simp only [alenO]; omega), F.alen]
  have h15₄ := E₄.r15
  have h12₄ : t₄.gpr .r12 = BitVec.ofNat 64 c := by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), h12₃]
  have r₄ : InRegions (t₄.rd ++ t₄.wr) (W + BitVec.ofNat 64 alenO) 8 := E₄.perm.wR (by decide)
  have w₄ : InRegions t₄.wr (W + BitVec.ofNat 64 alenO) 8 := E₄.perm.wW (by decide)
  simp only [alenO] at alen₄ r₄ w₄
  refine WP.of_runBlock ⟨_, by orun [h15₄, h12₄, alen₄, r₄, w₄], ?_⟩
  have fw : ∀ (M : Mem) (x : BitVec 64), Frame [⟨W + BitVec.ofNat 64 248, 8⟩] M
      (M.writeW (W + BitVec.ofNat 64 248) x) := fun M x =>
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have kf : ∀ (M : Mem) (x : BitVec 64) {d : Nat}, d + 16 ≤ 248 →
      blockAtMem (M.writeW (W + BitVec.ofNat 64 248) x) (W + BitVec.ofNat 64 d) = blockAtMem M (W + BitVec.ofNat 64 d) :=
    fun M x d hd => VG.Proof.AesOcb.X86_64.blockAtMem_frame (fw M x) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by omega) (by decide)
  refine ⟨⟨E₄.keep (fun r hr => by
        simp at hr; rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false])
      (by simp only [rd_setReg, rd_arithFlags]) (by simp only [wr_setReg, wr_arithFlags]), ?_, ?_, ?_, by omega,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [mem_setReg, mem_arithFlags]
    exact F.frame.trans (F₃.trans ((fr₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., fun _ h => h⟩).trans ((fw _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, fun _ h => h⟩)))
  · simp only [rd_setReg, rd_arithFlags]; rw [rd₄, P₃.rd, F.rd]
  · simp only [wr_setReg, wr_arithFlags]; rw [wr₄, P₃.wr, F.wr]
  · simp only [mem_setReg, mem_arithFlags]
    rw [kf _ _ (by decide), sum₄, k₃ (by decide), F.sum, VG.Proof.AesOcb.X86_64.hsum_add]
  · simp only [mem_setReg, mem_arithFlags]
    rw [kf _ _ (by decide), k₄ (by simp only [ohO]; omega) (by decide), k₃ (by decide), F.oh]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide), P₃.saved _ (by decide), F.rbx]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide), P₃.saved _ (by decide), F.rbp]
  · simp only [mem_setReg, mem_arithFlags, Mem.readW_writeW_self64]
    have hs := C.short
    rw [Proof.AesCcm.X86_64.ofNat_sub (show c ≤ a.length / 16 - j by omega) (by omega),
      show a.length / 16 - j - c = a.length / 16 - (j + c) by omega]
    exact Mem.readW_writeW_self64 _ _ _
  · simp only [mem_setReg, mem_arithFlags]
    rw [Mem.readW_writeW_sep (Offset.sep W (by decide) (by decide) (by decide)) (by decide),
      kw₄ (by simp only [tmpO]; omega) (by decide), kw₃ (by simp only [tmpO]; omega), F.rest]
  · simp only [mem_setReg, mem_arithFlags]
    rw [kf _ _ (by decide), k₄ (by simp only [l0O]; omega) (by decide), k₃ (by decide), F.l0]
  · simp only [zf_arithFlags, gpr_setReg, ite_true]
    have hs := C.short
    rw [Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

/-- A chunk of `min(8, m − j)` blocks, after `j` of the `m` whole blocks. -/
theorem chunkHead_ok {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph l A a s₀) {t : State} {j : Nat}
    (H : VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ t j) (hj : j < a.length / 16) :
    WP isa (.seq (.block [VG.Impl.AesOcb.X86_64.ld .r12 .r15 alenO, .alu .cmp .r12 (.imm 8)]) (.ite .b (.block []) (.block [.mov .r12 (.imm 8)])))
      t fun t' => VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ t' j ∧ t'.gpr .r12 = BitVec.ofNat 64 (min 8 (a.length / 16 - j)) := by
  have hs := C.short
  have h15 := H.env.r15
  have r₁ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 248) 8 := H.env.perm.wR (by decide)
  have alen := H.alen
  simp only [alenO] at alen
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 := by decide
  obtain ⟨t₁, run₁, r12₁, cf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [VG.Impl.AesOcb.X86_64.ld .r12 .r15 alenO, .alu .cmp .r12 (.imm 8)] t =
      some t₁ ∧ t₁.gpr .r12 = BitVec.ofNat 64 (a.length / 16 - j) ∧ t₁.cf = some (decide (a.length / 16 - j < 8)) ∧
      (∀ r, r ≠ .r12 → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by orun [h15, r₁, alen], ?_, ?_, fun r h => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true]
    · simp only [cf_arithFlags, gpr_setReg, ite_true, e8, VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (show a.length / 16 - j < 2 ^ 64 by omega),
        VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (show 8 < 2 ^ 64 by decide)]
    · simp only [gpr_setReg, gpr_arithFlags, h, ite_false]
    all_goals rfl
  have H₁ : VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ t₁ j :=
    { H with
      env := H.env.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₁ wr₁
      frame := by rw [m₁]; exact H.frame
      rd := by rw [rd₁, H.rd]
      wr := by rw [wr₁, H.wr]
      sum := by rw [m₁, H.sum]
      oh := by rw [m₁, H.oh]
      rbx := by rw [g₁ _ (by decide), H.rbx]
      rbp := by rw [g₁ _ (by decide), H.rbp]
      alen := by rw [m₁, H.alen]
      rest := by rw [m₁, H.rest]
      l0 := by rw [m₁, H.l0] }
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (a.length / 16 - j < 8)) (eval_b cf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hlt : a.length / 16 - j < 8 := of_decide_eq_true hb
    rw [show min 8 (a.length / 16 - j) = a.length / 16 - j by omega]
    exact ⟨H₁, r12₁⟩
  · have hge : ¬ a.length / 16 - j < 8 := of_decide_eq_false hb
    obtain ⟨t₂, run₂, r12₂, g₂, m₂, rd₂, wr₂⟩ : ∃ t₂, runBlock isa [.mov .r12 (.imm 8)] t₁ = some t₂ ∧
        t₂.gpr .r12 = BitVec.ofNat 64 8 ∧ (∀ r, r ≠ .r12 → t₂.gpr r = t₁.gpr r) ∧ t₂.mem = t₁.mem ∧ t₂.rd = t₁.rd ∧
        t₂.wr = t₁.wr := by
      refine ⟨_, by orun [], ?_, fun r h => ?_, ?_, ?_, ?_⟩
      · simp only [gpr_setReg, ite_true, e8]
      · simp only [gpr_setReg, h, ite_false]
      all_goals rfl
    have H₂ : VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ t₂ j :=
      { H₁ with
        env := H₁.env.keep (fun r hr => g₂ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₂ wr₂
        frame := by rw [m₂]; exact H₁.frame
        rd := by rw [rd₂, H₁.rd]
        wr := by rw [wr₂, H₁.wr]
        sum := by rw [m₂, H₁.sum]
        oh := by rw [m₂, H₁.oh]
        rbx := by rw [g₂ _ (by decide), H₁.rbx]
        rbp := by rw [g₂ _ (by decide), H₁.rbp]
        alen := by rw [m₂, H₁.alen]
        rest := by rw [m₂, H₁.rest]
        l0 := by rw [m₂, H₁.l0] }
    refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
    rw [show min 8 (a.length / 16 - j) = 8 by omega]
    exact ⟨H₂, r12₂⟩

theorem hashChunk_ok (v : BlocksImpl) {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph l A a s₀) {t : State} {j : Nat}
    (H : VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ t j) (hj : j < a.length / 16) :
    WP isa (hashChunk (VG.Proof.AesOcb.X86_64.callees v)) t fun t' =>
      VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ t' (j + min 8 (a.length / 16 - j)) ∧
        t'.zf = some (decide (a.length / 16 - (j + min 8 (a.length / 16 - j)) = 0)) := by
  unfold hashChunk
  refine wp_seq_assoc (WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.chunkHead_ok C H hj) fun t₁ ⟨H₁, h12⟩ =>
    VG.Proof.AesOcb.X86_64.chunkRest_ok v C H₁ (by omega) (by omega) (by omega) h12))

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.Hash`. -/
section

/-!
# AES-OCB on x86-64: `HASH` (`hash`)

Untrusted: everything here is checked by Lean. `hash` zeroes the sum and the
offset, keeps the number of whole blocks of the associated data and the
length of the rest in `W`, takes the whole blocks a chunk at a time
(`hashChunk_ok`), and the rest, padded, XORed with `Offset_m ⊕ L_*` and
enciphered (`hashRest_ok`): the sum is §4.1's `HASH(K, A)` (`hash_ok`,
`Proof.Ocb.hash_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt hsum)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt imm_eq eval_e eval_ne bytesAt_frame)

/-- The padded rest of the associated data, after its `m` whole blocks. -/
theorem hashRest_ok (v : BlocksImpl) {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph l A a s₀) {t : State}
    (H : VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ t (a.length / 16)) (hr : 0 < a.length % 16)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 (a.length % 16)) :
    WP isa (hashRest (VG.Proof.AesOcb.X86_64.callees v)) t fun t' => Env K W SP t' ∧ Frame (VG.Proof.AesOcb.X86_64.hashR W SP) s₀.mem t'.mem ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧ t'.wr = s₀.wr := by
  have L := C.lay
  have E := H.env
  have hs := C.short
  generalize hm : a.length / 16 = m at H
  have hrest : a.length - 16 * m = a.length % 16 := by omega
  -- `Offset_m ⊕ L_*`
  obtain ⟨t₁, run₁, B₁⟩ := xor16_ok (s := t) (b := .r14) (a := 240) (d := ohO) E.r15 E.r14 (by decide) (by decide)
    (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => B₁.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    B₁.rd B₁.wr
  have oh₁ : blockAtMem t₁.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l m ^^^ l := by
    rw [B₁.val, H.oh, ← C.lstar' (VG.Proof.AesOcb.X86_64.hashR_mut H.frame)]; rfl
  have fr₁ : Frame (VG.Proof.AesOcb.X86_64.hashR W SP) s₀.mem t₁.mem := H.frame.trans (B₁.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩)
  -- `pad(A_*)`
  have hB := C.buf.slice (a := 16 * m) (k := a.length % 16) (by omega)
  have hS : Covers [⟨A + BitVec.ofNat 64 (16 * m), a.length % 16⟩] (t₁.rd ++ t₁.wr) := by
    rw [B₁.rd, B₁.wr, H.rd, H.wr]; exact hB.rd
  have hSD : (⟨A + BitVec.ofNat 64 (16 * m), a.length % 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 bufO, 16⟩ :=
    hB.w.sub_right (Lay.wSub (by decide))
  have hrestb : bytesAt t₁.mem (A + BitVec.ofNat 64 (16 * m)) (a.length % 16) = a.drop (16 * m) := by
    have hd := Proof.Ocb.bytesAt_drop s₀.mem A (a := 16 * m) (n := a.length) (by omega)
    rw [C.aad, hrest] at hd
    rw [VG.Proof.AesCcm.X86_64.bytesAt_frame (VG.Proof.AesOcb.X86_64.hashR_mut (D := D) (n := n) fr₁) (fun r hr =>
      (C.a_mut r hr).sub_left (Offset.sub_base A (by omega))) (by omega), hd]
  unfold hashRest
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.padTo_ok E₁ hr (by omega) (by decide) (by rw [B₁.gpr _ (by decide), H.rbx])
    (by rw [B₁.gpr _ (by decide), h12]) hS hSD) fun t₂ ⟨fr₂, pad₂, g₂, rd₂, wr₂⟩ => ?_)
  rw [hrestb] at pad₂
  have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => g₂ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₂ wr₂
  have oh₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ohO) = offAt 0 l m ^^^ l := by
    rw [VG.Proof.AesOcb.X86_64.blockAtMem_frame fr₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide), oh₁]
  -- XORed with the offset
  obtain ⟨t₃, run₃, B₃⟩ := xor16_ok (s := t₂) (b := .r15) (a := ohO) (d := bufO) E₂.r15 E₂.r15 (by decide) (by decide)
    (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide)) (E₂.perm.wW (by decide)) (E₂.perm.wW (by decide))
  have E₃ : Env K W SP t₃ := E₂.keep (fun r hr => B₃.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    B₃.rd B₃.wr
  have buf₃ : blockAtMem t₃.mem (W + BitVec.ofNat 64 bufO) =
      pad (a.drop (16 * m)) ^^^ (offAt 0 l m ^^^ l) := by rw [B₃.val, pad₂, oh₂]
  have fr₃ : Frame (VG.Proof.AesOcb.X86_64.hashR W SP) s₀.mem t₃.mem := fr₁.trans ((fr₂.trans B₃.frame).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, VG.Proof.AesOcb.X86_64.sub_wC (by decide) (by decide)⟩)
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  -- enciphered
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNosp v.encDepth L E₃
    C.rounds (C.rnd' (VG.Proof.AesOcb.X86_64.hashR_mut fr₃)) (oneBlock_ok E₃.r15 bufO (by decide))
    (dstW L E₃.perm (d := bufO) (n := 1) (by decide))) fun t₄ P₄ => ?_)
  have E₄ : Env K W SP t₄ := E₃.of_saved P₄.saved P₄.rd P₄.wr
  have buf₄ : blockAtMem t₄.mem (W + BitVec.ofNat 64 bufO) = ciph (pad (a.drop (16 * m)) ^^^ (offAt 0 l m ^^^ l)) := by
    have := P₄.enc (i := 0) (by decide)
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this, buf₃]
    exact congrFun (C.ciph' (VG.Proof.AesOcb.X86_64.hashR_mut fr₃)) _
  have fr₄ : Frame (VG.Proof.AesOcb.X86_64.hashR W SP) s₀.mem t₄.mem := fr₃.trans (P₄.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, VG.Proof.AesOcb.X86_64.sub_wC (by decide) (by decide)⟩
    · exact ⟨_, by simp, VG.Proof.AesOcb.X86_64.sub_wC (by decide) (by decide)⟩
    · rw [E₃.rsp]; exact ⟨_, by simp, fun _ h => h⟩)
  have kSum : ∀ {u u' : State}, Frame [⟨W + BitVec.ofNat 64 bufO, 16⟩] u.mem u'.mem →
      blockAtMem u'.mem (W + BitVec.ofNat 64 sumO) = blockAtMem u.mem (W + BitVec.ofNat 64 sumO) := fun h =>
    VG.Proof.AesOcb.X86_64.blockAtMem_frame h fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have sum₄ : blockAtMem t₄.mem (W + BitVec.ofNat 64 sumO) = hsum ciph l a m := by
    rw [VG.Proof.AesOcb.X86_64.blockAtMem_frame P₄.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · rw [E₃.rsp]; exact (L.stk_w' (by decide)).symm),
      kSum B₃.frame, kSum fr₂, VG.Proof.AesOcb.X86_64.blockAtMem_frame B₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), H.sum]
  -- added to the sum
  obtain ⟨t₅, run₅, B₅⟩ := xor16_ok (s := t₄) (b := .r15) (a := bufO) (d := sumO) E₄.r15 E₄.r15 (by decide) (by decide)
    (E₄.perm.wR (by decide)) (E₄.perm.wR (by decide)) (E₄.perm.wW (by decide)) (E₄.perm.wW (by decide))
  refine WP.of_runBlock ⟨t₅, run₅, E₄.keep (fun r hr => B₅.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    B₅.rd B₅.wr, fr₄.trans (B₅.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩), ?_,
    by rw [B₅.rd, P₄.rd, B₃.rd, rd₂, B₁.rd, H.rd], by rw [B₅.wr, P₄.wr, B₃.wr, wr₂, B₁.wr, H.wr]⟩
  rw [B₅.val, sum₄, buf₄, Proof.Ocb.hash_eq]
  have hlen : (a.drop (16 * m)).length = a.length % 16 := by simp; omega
  simp only [hlen, show a.length % 16 > 0 from hr, ↓reduceIte, hm]

/-- After the whole blocks: the rest, if any. -/
theorem hashTail_ok (v : BlocksImpl) {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph l A a s₀) {t : State}
    (H : VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ t (a.length / 16)) :
    WP isa (.seq (.block [VG.Impl.AesOcb.X86_64.ld .r12 .r15 tmpO, .alu .test .r12 (.reg .r12)]) (.ite .e (.block []) (hashRest (VG.Proof.AesOcb.X86_64.callees v))))
      t fun t' => Env K W SP t' ∧ Frame (VG.Proof.AesOcb.X86_64.hashR W SP) s₀.mem t'.mem ∧
        blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧ t'.wr = s₀.wr := by
  have r₁ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 112) 8 := H.env.perm.wR (by decide)
  have rest := H.rest
  simp only [tmpO] at rest
  obtain ⟨t₁, run₁, r12₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [VG.Impl.AesOcb.X86_64.ld .r12 .r15 tmpO, .alu .test .r12 (.reg .r12)] t =
      some t₁ ∧ t₁.gpr .r12 = BitVec.ofNat 64 (a.length % 16) ∧ t₁.zf = some (decide (a.length % 16 = 0)) ∧
      (∀ r, r ≠ .r12 → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by orun [H.env.r15, r₁, rest], ?_, ?_, fun r h => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true]
    · simp only [zf_arithFlags, gpr_setReg, ite_true,
        Proof.AesCcm.X86_64.and_self_beq (show a.length % 16 < 2 ^ 64 by omega)]
    · simp only [gpr_setReg, gpr_arithFlags, h, ite_false]
    all_goals rfl
  have H₁ : VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ t₁ (a.length / 16) :=
    { H with
      env := H.env.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₁ wr₁
      frame := by rw [m₁]; exact H.frame
      rd := by rw [rd₁, H.rd]
      wr := by rw [wr₁, H.wr]
      sum := by rw [m₁, H.sum]
      oh := by rw [m₁, H.oh]
      rbx := by rw [g₁ _ (by decide), H.rbx]
      rbp := by rw [g₁ _ (by decide), H.rbp]
      alen := by rw [m₁, H.alen]
      rest := by rw [m₁, H.rest]
      l0 := by rw [m₁, H.l0] }
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (a.length % 16 = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h0 : a.length % 16 = 0 := of_decide_eq_true hb
    refine ⟨H₁.env, H₁.frame, ?_, H₁.rd, H₁.wr⟩
    rw [H₁.sum, Proof.Ocb.hash_eq]
    have hlen : (a.drop (16 * (a.length / 16))).length = 0 := by simp; omega
    simp [hlen]
  · exact VG.Proof.AesOcb.X86_64.hashRest_ok v C H₁ (by have := of_decide_eq_false hb; omega) r12₁

/-- `HASH(K, A)` to `W + sumO`, with `aad` and `aad_len` in `W`. -/
theorem hashHead_ok {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph l A a s₀) (E : Env K W SP s₀)
    (haad : s₀.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length)
    (hl0 : blockAtMem s₀.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (.block (zero16 sumO ++ zero16 ohO ++
      [VG.Impl.AesOcb.X86_64.ld .rbx .r15 aadO, VG.Impl.AesOcb.X86_64.ld .rax .r15 alenO, mvr .rcx .rax, .alu .and .rcx (.imm 15),
       st .r15 tmpO .rcx, .shift .shr .rax 4, st .r15 alenO .rax, .mov .rbp (.imm 1),
       .alu .test .rax (.reg .rax)])) s₀ fun s =>
      VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ s 0 ∧ s.zf = some (decide (a.length / 16 = 0)) := by
  have L := C.lay
  have hs := C.short
  -- the sum, the offset, the counts
  obtain ⟨s₁, run₁, B₁⟩ := zero16_ok (s := s₀) (d := sumO) E.r15 (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have h15₁ : s₁.gpr .r15 = W := by rw [B₁.gpr _ (by decide), E.r15]
  obtain ⟨s₂, run₂, B₂⟩ := zero16_ok (s := s₁) (d := ohO) h15₁ (by rw [B₁.wr]; exact E.perm.wW (by decide))
    (by rw [B₁.wr]; exact E.perm.wW (by decide))
  have h15₂ : s₂.gpr .r15 = W := by rw [B₂.gpr _ (by decide), h15₁]
  have kA : ∀ {d : Nat}, (d + 8 ≤ 48 ∨ (64 ≤ d ∧ d + 8 ≤ 144) ∨ 160 ≤ d) → d + 8 ≤ 2560 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₀.mem.readW (W + BitVec.ofNat 64 d) 64 := fun h₁ h₂ => by
    rw [B₂.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := _) (d := 144) (k := 16) (by omega) h₂ (by decide)) (by decide),
      B₁.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := _) (d := 48) (k := 16) (by omega) h₂ (by decide)) (by decide)]
  have haad₂ := (kA (d := 240) (by decide) (by decide)).trans haad
  have halen₂ := (kA (d := 248) (by decide) (by decide)).trans halen
  have r₁ : InRegions (s₂.rd ++ s₂.wr) (W + BitVec.ofNat 64 240) 8 := by rw [B₂.rd, B₂.wr, B₁.rd, B₁.wr]; exact E.perm.wR (by decide)
  have r₂ : InRegions (s₂.rd ++ s₂.wr) (W + BitVec.ofNat 64 248) 8 := by rw [B₂.rd, B₂.wr, B₁.rd, B₁.wr]; exact E.perm.wR (by decide)
  have w₁ : InRegions s₂.wr (W + BitVec.ofNat 64 112) 8 := by rw [B₂.wr, B₁.wr]; exact E.perm.wW (by decide)
  have w₂ : InRegions s₂.wr (W + BitVec.ofNat 64 248) 8 := by rw [B₂.wr, B₁.wr]; exact E.perm.wW (by decide)
  have e15 : BitVec.signExtend 64 (15 : BitVec 32) = 15#64 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 := by decide
  obtain ⟨s₃, run₃, rbx₃, rbp₃, zf₃, m₃, g₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa
      [VG.Impl.AesOcb.X86_64.ld .rbx .r15 aadO, VG.Impl.AesOcb.X86_64.ld .rax .r15 alenO, mvr .rcx .rax, .alu .and .rcx (.imm 15),
       st .r15 tmpO .rcx, .shift .shr .rax 4, st .r15 alenO .rax, .mov .rbp (.imm 1),
       .alu .test .rax (.reg .rax)] s₂ = some s₃ ∧
      s₃.gpr .rbx = A ∧ s₃.gpr .rbp = BitVec.ofNat 64 1 ∧ s₃.zf = some (decide (a.length / 16 = 0)) ∧
      s₃.mem = (s₂.mem.writeW (W + BitVec.ofNat 64 112) (BitVec.ofNat 64 (a.length % 16))).writeW
        (W + BitVec.ofNat 64 248) (BitVec.ofNat 64 (a.length / 16)) ∧
      (∀ r, r ≠ .rbx → r ≠ .rax → r ≠ .rcx → r ≠ .rbp → s₃.gpr r = s₂.gpr r) ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by orun [h15₂, r₁, r₂, w₁, w₂, haad₂, halen₂], ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e1]
    · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
        Proof.AesCcm.X86_64.shr4 _ (show a.length < 2 ^ 64 by omega),
        Proof.AesCcm.X86_64.and_self_beq (show a.length / 16 < 2 ^ 64 by omega)]
    · simp only [mem_setReg, mem_setFlags, mem_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true,
        ite_false, reduceCtorEq, e15, Proof.AesCcm.X86_64.and15', VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt (show a.length < 2 ^ 64 by omega),
        Proof.AesCcm.X86_64.shr4 _ (show a.length < 2 ^ 64 by omega)]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h1, h2, h3, h4, ite_false]
    all_goals try rfl
  have f₁₁₂ : ∀ (M : Mem) (x y : BitVec 64), Frame [⟨W + BitVec.ofNat 64 112, 8⟩, ⟨W + BitVec.ofNat 64 248, 8⟩] M
      ((M.writeW (W + BitVec.ofNat 64 112) x).writeW (W + BitVec.ofNat 64 248) y) := fun M x y =>
    ((Frame.refl _ _).writeW (List.mem_cons_self ..) x (Region.contains_self (W + BitVec.ofNat 64 112) 8)).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) y (Region.contains_self (W + BitVec.ofNat 64 248) 8)
  have kB : ∀ {d : Nat}, (d + 16 ≤ 112 ∨ (120 ≤ d ∧ d + 16 ≤ 248)) →
      blockAtMem s₃.mem (W + BitVec.ofNat 64 d) = blockAtMem s₂.mem (W + BitVec.ofNat 64 d) :=
    fun hd => by
      rw [m₃]
      exact VG.Proof.AesOcb.X86_64.blockAtMem_frame (f₁₁₂ _ _ _) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.w_w (by omega) (by omega) (by decide)
        · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  have H₀ : VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ s₃ 0 :=
    { env := E.keep (fun r hr => by
          simp at hr
          rcases hr with rfl | rfl | rfl <;>
            rw [g₃ _ (by decide) (by decide) (by decide) (by decide), B₂.gpr _ (by decide), B₁.gpr _ (by decide)])
        (by rw [rd₃, B₂.rd, B₁.rd]) (by rw [wr₃, B₂.wr, B₁.wr])
      frame := by
        rw [m₃]
        refine (B₁.frame.sub fun r hr => ?_).trans ((B₂.frame.sub fun r hr => ?_).trans ((f₁₁₂ _ _ _).sub fun r hr => ?_))
        · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
          · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
      rd := by rw [rd₃, B₂.rd, B₁.rd]
      wr := by rw [wr₃, B₂.wr, B₁.wr]
      le := Nat.zero_le _
      sum := by
        rw [kB (by decide), VG.Proof.AesOcb.X86_64.blockAtMem_frame B₂.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), B₁.val]
        rfl
      oh := by rw [kB (by decide), B₂.val]; rfl
      rbx := by rw [rbx₃]; simp
      rbp := rbp₃
      alen := by rw [m₃]; simp only [alenO, Nat.sub_zero]; exact Mem.readW_writeW_self64 _ _ _
      rest := by
        rw [m₃]; simp only [tmpO]
        rw [Mem.readW_writeW_sep (Offset.sep W (by decide) (by decide) (by decide)) (by decide),
          Mem.readW_writeW_self64]
      l0 := by
        rw [kB (by decide), VG.Proof.AesOcb.X86_64.blockAtMem_frame B₂.frame (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
          VG.Proof.AesOcb.X86_64.blockAtMem_frame B₁.frame (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), hl0] }
  exact WP.of_runBlock ⟨s₃, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, VG.Proof.AesCcm.X86_64.runBlock_append, run₁, Option.bind_some, run₂,
    Option.bind_some, run₃], H₀, zf₃⟩

/-- The chunks of `HASH`, from the first. -/
theorem hashLoop_ok (v : BlocksImpl) {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph l A a s₀) {t : State}
    (H₀ : VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ t 0) (hm : 0 < a.length / 16) :
    WP isa (.loop (hashChunk (VG.Proof.AesOcb.X86_64.callees v)) .ne) t fun u => VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ u (a.length / 16) := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ j, k = a.length / 16 - j ∧ j < a.length / 16 ∧
      VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ u j) ?_ (a.length / 16 - 0) _ ⟨0, rfl, hm, H₀⟩
  rintro k u ⟨j, rfl, hj, H⟩
  refine WP.mono (VG.Proof.AesOcb.X86_64.hashChunk_ok v C H hj) fun u' ⟨H', hz⟩ => ?_
  by_cases he : a.length / 16 - (j + min 8 (a.length / 16 - j)) = 0
  · left
    have hje : j + min 8 (a.length / 16 - j) = a.length / 16 := by omega
    exact ⟨(eval_ne hz).trans (by simp [he]), hje ▸ H'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), a.length / 16 - (j + min 8 (a.length / 16 - j)), by omega,
      j + min 8 (a.length / 16 - j), rfl, by omega, H'⟩

theorem hash_ok (v : BlocksImpl) {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr}
    {a : List Byte} {s₀ : State} (C : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph l A a s₀) (E : Env K W SP s₀)
    (haad : s₀.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length)
    (hl0 : blockAtMem s₀.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (Impl.AesOcb.X86_64.hash (VG.Proof.AesOcb.X86_64.callees v)) s₀ fun t' => Env K W SP t' ∧ Frame (VG.Proof.AesOcb.X86_64.hashR W SP) s₀.mem t'.mem ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧ t'.wr = s₀.wr := by
  unfold Impl.AesOcb.X86_64.hash
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.hashHead_ok C E haad halen hl0) fun s₃ ⟨H₀, zf₃⟩ => ?_)
  refine WP.seq (WP.ite (decide (a.length / 16 = 0)) (eval_e zf₃) (fun hb => WP.block_nil ?_) (fun hb => ?_))
  · have h0 : a.length / 16 = 0 := of_decide_eq_true hb
    exact VG.Proof.AesOcb.X86_64.hashTail_ok v C (h0 ▸ H₀)
  · exact WP.mono (VG.Proof.AesOcb.X86_64.hashLoop_ok v C H₀ (Nat.pos_of_ne_zero (of_decide_eq_false hb))) fun u H => VG.Proof.AesOcb.X86_64.hashTail_ok v C H

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.Pass`. -/
section

/-!
# AES-OCB on x86-64: a pass over the whole blocks (`pass`)

Untrusted: everything here is checked by Lean. `pass body` goes over the
`m` whole blocks of the data at `D`: for block `i` it computes
`Offset_{i+1}` (`lNtz_ok`, `xor16_ok`), then runs `body` on the block, which
replaces it with `fB` of it and the offset, and the checksum with `fC` of
them (`BodyOk`: `xorOfs`, `addCk ++ xorOfs`, `xorOfs ++ addCk`); `pass_ok`
gives the blocks and the checksum after all `m`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt)
open VG.Proof.Cmac (le8)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt imm_eq eval_e eval_ne in_left)

/-- What a body does to the block at `B` (in `rbx`) and the checksum, with
the offset at `W + ofsO`. -/
def BodyOk (W : Addr) (body : List Instr) (fB : Block → Block → Block) (fC : Block → Block → Block → Block) : Prop :=
  ∀ (t : State) (B : Addr), t.gpr .rbx = B → t.gpr .r15 = W →
    InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 0) 8 → InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 8) 8 →
    InRegions t.wr (B + BitVec.ofNat 64 0) 8 → InRegions t.wr (B + BitVec.ofNat 64 8) 8 →
    InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 16) 8 → InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 24) 8 →
    InRegions t.wr (W + BitVec.ofNat 64 32) 8 → InRegions t.wr (W + BitVec.ofNat 64 40) 8 →
    (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩ →
    ∃ t', runBlock isa body t = some t' ∧
      blockAtMem t'.mem B = fB (blockAtMem t.mem B) (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)) ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) = fC (blockAtMem t.mem (W + BitVec.ofNat 64 ckO))
        (blockAtMem t.mem B) (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)) ∧
      Frame [⟨B, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩] t.mem t'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr

theorem xorOfs_ok {W : Addr} : VG.Proof.AesOcb.X86_64.BodyOk W xorOfs (fun b o => b ^^^ o) (fun c _ _ => c) := by
  intro t B hbx h15 rB₀ rB₈ wB₀ wB₈ rO₀ rO₈ _ _ hBW
  have e0 : B + BitVec.ofNat 64 0 = B := BitVec.add_zero _
  rw [e0] at rB₀ wB₀
  refine ⟨_, by orun [xorOfs, hbx, h15, e0, rB₀, rB₈, wB₀, wB₈, rO₀, rO₈], ?_, ?_, ?_, fun r h1 h2 => ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags]
    rw [blockAtMem_store2, show W + 24#64 = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 from (addr8 W 16).symm,
      blockAtMem_xor_words]; rfl
  · simp only [mem_setReg, mem_arithFlags]
    rw [VG.Proof.AesOcb.X86_64.blockAtMem_frame (frame_store2 _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hBW.sub_right (Lay.wSub (W := W) (d := 32) (n := 16) (by decide))).symm]
  · simp only [mem_setReg, mem_arithFlags]
    exact (frame_store2 _ _ _ _).mono (by simp)
  · simp only [gpr_setReg, gpr_arithFlags, h1, h2, ite_false]
  all_goals rfl

/-- `addCk`: the checksum XORed with the block at `B`. -/
theorem addCk_ok {W B : Addr} {t : State} (hbx : t.gpr .rbx = B) (h15 : t.gpr .r15 = W)
    (rB₀ : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 0) 8) (rB₈ : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 8) 8)
    (wC₀ : InRegions t.wr (W + BitVec.ofNat 64 32) 8) (wC₈ : InRegions t.wr (W + BitVec.ofNat 64 40) 8) :
    ∃ t', runBlock isa addCk t = some t' ∧
      BlkStep W ckO (blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem B) [.rax, .rdx] t t' := by
  obtain ⟨t', run, Bk⟩ := xor16_ok (s := t) (b := .rbx) (a := 0) (d := ckO) h15 hbx (by decide) (by decide) rB₀ rB₈
    wC₀ wC₈
  rw [BitVec.add_zero] at Bk
  exact ⟨t', run, Bk⟩

theorem blockAtMem_ck {W B : Addr} (hBW : (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩) {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 ckO, 16⟩] m m') : blockAtMem m' B = blockAtMem m B :=
  VG.Proof.AesOcb.X86_64.blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hBW.sub_right (Lay.wSub (by decide))

theorem blockAtMem_ofs_ck {W : Addr} {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 ckO, 16⟩] m m') :
    blockAtMem m' (W + BitVec.ofNat 64 ofsO) = blockAtMem m (W + BitVec.ofNat 64 ofsO) :=
  VG.Proof.AesOcb.X86_64.blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint W (d := 16) (n := 16) (e := 32) (k := 16) (.inl (by decide)) (by omega) (by omega)

/-- `seal`'s first pass: the checksum of the block, then the block XORed with the offset. -/
theorem sealPre_ok {W : Addr} :
    VG.Proof.AesOcb.X86_64.BodyOk W (addCk ++ xorOfs) (fun b o => b ^^^ o) (fun c b _ => c ^^^ b) := by
  intro t B hbx h15 rB₀ rB₈ wB₀ wB₈ rO₀ rO₈ wC₀ wC₈ hBW
  obtain ⟨t₁, run₁, B₁⟩ := VG.Proof.AesOcb.X86_64.addCk_ok hbx h15 rB₀ rB₈ wC₀ wC₈
  obtain ⟨t₂, run₂, b₂, c₂, f₂, g₂, rd₂, wr₂⟩ := VG.Proof.AesOcb.X86_64.xorOfs_ok t₁ B (by rw [B₁.gpr _ (by decide), hbx])
    (by rw [B₁.gpr _ (by decide), h15]) (by rw [B₁.rd, B₁.wr]; exact rB₀) (by rw [B₁.rd, B₁.wr]; exact rB₈)
    (by rw [B₁.wr]; exact wB₀) (by rw [B₁.wr]; exact wB₈) (by rw [B₁.rd, B₁.wr]; exact rO₀)
    (by rw [B₁.rd, B₁.wr]; exact rO₈) (by rw [B₁.wr]; exact wC₀) (by rw [B₁.wr]; exact wC₈) hBW
  refine ⟨t₂, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₁, Option.bind_some, run₂], ?_, ?_, ?_, fun r h1 h2 => ?_,
    by rw [rd₂, B₁.rd], by rw [wr₂, B₁.wr]⟩
  · rw [b₂, VG.Proof.AesOcb.X86_64.blockAtMem_ck hBW B₁.frame, VG.Proof.AesOcb.X86_64.blockAtMem_ofs_ck B₁.frame]
  · rw [c₂, B₁.val]
  · exact (B₁.frame.mono (by simp)).trans f₂
  · rw [g₂ r h1 h2, B₁.gpr r (by simp [h1, h2])]

/-- `open`'s third pass: the block XORed with the offset, then its checksum. -/
theorem openPost_ok {W : Addr} :
    VG.Proof.AesOcb.X86_64.BodyOk W (xorOfs ++ addCk) (fun b o => b ^^^ o) (fun c b o => c ^^^ (b ^^^ o)) := by
  intro t B hbx h15 rB₀ rB₈ wB₀ wB₈ rO₀ rO₈ wC₀ wC₈ hBW
  obtain ⟨t₁, run₁, b₁, c₁, f₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86_64.xorOfs_ok t B hbx h15 rB₀ rB₈ wB₀ wB₈ rO₀ rO₈ wC₀ wC₈ hBW
  obtain ⟨t₂, run₂, B₂⟩ := VG.Proof.AesOcb.X86_64.addCk_ok (t := t₁) (by rw [g₁ _ (by decide) (by decide), hbx])
    (by rw [g₁ _ (by decide) (by decide), h15]) (by rw [rd₁, wr₁]; exact rB₀) (by rw [rd₁, wr₁]; exact rB₈)
    (by rw [wr₁]; exact wC₀) (by rw [wr₁]; exact wC₈)
  refine ⟨t₂, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₁, Option.bind_some, run₂], ?_, ?_, ?_, fun r h1 h2 => ?_,
    by rw [B₂.rd, rd₁], by rw [B₂.wr, wr₁]⟩
  · rw [VG.Proof.AesOcb.X86_64.blockAtMem_ck hBW B₂.frame, b₁]
  · rw [B₂.val, c₁, b₁]
  · exact f₁.trans (B₂.frame.mono (by simp))
  · rw [B₂.gpr r (by simp [h1, h2]), g₁ r h1 h2]

/-- A pass over the `m` whole blocks at `D` (`X k` at its start, `t₀`), after
`i` of them. -/
structure PassInv (K W SP D : Addr) (m : Nat) (O0 l : Block) (X : Nat → Block) (fB : Block → Block → Block)
    (ckF : Nat → Block) (t₀ t : State) (i : Nat) : Prop where
  env : Env K W SP t
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩,
    ⟨D, 16 * m⟩] t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  rbx : t.gpr .rbx = D + BitVec.ofNat 64 (16 * i)
  rbp : t.gpr .rbp = BitVec.ofNat 64 (i + 1)
  r12 : t.gpr .r12 = BitVec.ofNat 64 (m - i)
  ofs : blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) = offAt O0 l i
  ck : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = ckF i
  blk : ∀ k < m, blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) =
    if k < i then fB (X k) (offAt O0 l (k + 1)) else X k
  l0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r11 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 →
    t.gpr r = t₀.gpr r

theorem pass_step {K W SP D : Addr} (L : Lay K W SP) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : VG.Proof.AesOcb.X86_64.BodyOk W body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hD : DBuf K W SP t₀ D (16 * m)) (hm : m < 2 ^ 60) {t : State} {i : Nat} (hi : i < m)
    (P : VG.Proof.AesOcb.X86_64.PassInv K W SP D m O0 l X fB ckF t₀ t i) :
    WP isa (.seq nextOffset (.block (body ++ nextBlock))) t fun t' =>
      VG.Proof.AesOcb.X86_64.PassInv K W SP D m O0 l X fB ckF t₀ t' (i + 1) ∧ t'.zf = some (decide (m - (i + 1) = 0)) := by
  have hDt : DBuf K W SP t D (16 * m) := hD.of_eq P.rd P.wr
  have hBi := hDt.slice (a := 16 * i) (k := 16) (by omega)
  unfold nextOffset
  refine WP.seq (WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.lNtz_ok P.env (by omega) (by omega) P.rbp P.l0) fun t₁ P₁ => ?_))
  have h15₁ : t₁.gpr .r15 = W := by rw [P₁.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), P.env.r15]
  obtain ⟨t₂, run₂, B₂⟩ := xor16_ok (s := t₁) (b := .r15) (a := lO) (d := ofsO) h15₁ h15₁ (by decide) (by decide)
    (by rw [P₁.rd, P₁.wr]; exact P.env.perm.wR (by decide)) (by rw [P₁.rd, P₁.wr]; exact P.env.perm.wR (by decide))
    (by rw [P₁.wr]; exact P.env.perm.wW (by decide)) (by rw [P₁.wr]; exact P.env.perm.wW (by decide))
  refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
  have g₂ : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r11 → t₂.gpr r = t.gpr r := fun r h1 h2 h3 h4 h5 => by
    rw [B₂.gpr r (by simp [h1, h2]), P₁.gpr r h1 h2 h3 h4 h5]
  have rd₂ : t₂.rd = t.rd := by rw [B₂.rd, P₁.rd]
  have wr₂ : t₂.wr = t.wr := by rw [B₂.wr, P₁.wr]
  have h15₂ : t₂.gpr .r15 = W := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), P.env.r15]
  have hbx₂ : t₂.gpr .rbx = D + BitVec.ofNat 64 (16 * i) := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), P.rbx]
  have fW₂ : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ofsO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  have kW₂ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨W, 2560⟩ → blockAtMem t₂.mem Q = blockAtMem t.mem Q :=
    fun hQ => VG.Proof.AesOcb.X86_64.blockAtMem_frame fW₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hQ.sub_right (Lay.wSub (by decide))
  have ofs₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ofsO) = offAt O0 l (i + 1) := by
    rw [B₂.val, VG.Proof.AesOcb.X86_64.blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), P.ofs,
      P₁.val]
    rfl
  have ck₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ckO) = ckF i := by
    rw [VG.Proof.AesOcb.X86_64.blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.ck]
  have Bi₂ : blockAtMem t₂.mem (D + BitVec.ofNat 64 (16 * i)) = X i := by
    rw [kW₂ hBi.w, P.blk i hi]; simp
  have e0 : D + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 0 = D + BitVec.ofNat 64 (16 * i) := BitVec.add_zero _
  obtain ⟨t₃, run₃, blk₃, ck₃, fr₃, g₃, rd₃, wr₃⟩ := hB t₂ _ hbx₂ h15₂
    (by rw [e0, rd₂, wr₂]; exact hBi.rd _ _ ⟨_, List.mem_singleton_self _,
      by simpa using Offset.contains_base (D + BitVec.ofNat 64 (16 * i)) (d := 0) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [rd₂, wr₂]; exact hBi.rd _ _ ⟨_, List.mem_singleton_self _,
      Offset.contains_base _ (d := 8) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [e0, wr₂]; exact hBi.wr _ _ ⟨_, List.mem_singleton_self _,
      by simpa using Offset.contains_base (D + BitVec.ofNat 64 (16 * i)) (d := 0) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [wr₂]; exact hBi.wr _ _ ⟨_, List.mem_singleton_self _,
      Offset.contains_base _ (d := 8) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [rd₂, wr₂]; exact P.env.perm.wR (by decide)) (by rw [rd₂, wr₂]; exact P.env.perm.wR (by decide))
    (by rw [wr₂]; exact P.env.perm.wW (by decide)) (by rw [wr₂]; exact P.env.perm.wW (by decide)) hBi.w
  have g₃' : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r11 → t₃.gpr r = t.gpr r := fun r h1 h2 h3 h4 h5 => by
    rw [g₃ r h1 h2, g₂ r h1 h2 h3 h4 h5]
  have r12₃ : t₃.gpr .r12 = BitVec.ofNat 64 (m - i) := by
    rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), P.r12]
  have rbp₃ : t₃.gpr .rbp = BitVec.ofNat 64 (i + 1) := by
    rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), P.rbp]
  have rbx₃ : t₃.gpr .rbx = D + BitVec.ofNat 64 (16 * i) := by
    rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide), P.rbx]
  have kB₃ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * i), 16⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨W, 2560⟩ → blockAtMem t₃.mem Q = blockAtMem t.mem Q := fun h₁ h₂ => by
    rw [VG.Proof.AesOcb.X86_64.blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂.sub_right (Lay.wSub (by decide))), kW₂ h₂]
  refine WP.of_runBlock ⟨_, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₃, Option.bind_some]; orun [nextBlock, rbx₃, rbp₃, r12₃], ?_⟩
  have hw := hD.wrap
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, fun r h1 h2 h3 h4 h5 h6 h7 h8 => ?_⟩, ?_⟩
  · exact P.env.keep (fun r hr => by
      simp at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false] <;>
        exact g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (by simp only [rd_setReg, rd_arithFlags]; rw [rd₃, rd₂]) (by simp only [wr_setReg, wr_arithFlags]; rw [wr₃, wr₂])
  · simp only [mem_setReg, mem_arithFlags]
    exact P.frame.trans ((fW₂.mono (by simp)).trans (fr₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨D, 16 * m⟩, by simp, Offset.sub_base D (by omega)⟩
      · exact ⟨⟨W + BitVec.ofNat 64 ckO, 16⟩, by simp, fun _ h => h⟩))
  · simp only [rd_setReg, rd_arithFlags]; rw [rd₃, rd₂, P.rd]
  · simp only [wr_setReg, wr_arithFlags]; rw [wr₃, wr₂, P.wr]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, rbx₃, Offset.add_add]
    rw [show 16 * i + 16 = 16 * (i + 1) by omega]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, rbp₃, ← BitVec.ofNat_add]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, r12₃, sext1]
    rw [Proof.AesCcm.X86_64.ofNat_sub (by omega) (by omega), show m - i - 1 = m - (i + 1) by omega]
  · simp only [mem_setReg, mem_arithFlags]
    rw [VG.Proof.AesOcb.X86_64.blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hBi.w.sub_right (Lay.wSub (W := W) (d := 16) (n := 16) (by decide))).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)), ofs₂]
  · simp only [mem_setReg, mem_arithFlags]
    rw [ck₃, ck₂, Bi₂, ofs₂, hckF i hi]
  · simp only [mem_setReg, mem_arithFlags]
    by_cases hki : k = i
    · subst hki
      rw [blk₃, Bi₂, ofs₂]; simp
    · have hBk := hDt.slice (a := 16 * k) (k := 16) (by omega)
      rw [kB₃ (Offset.disjoint D (by omega) (by omega) (by omega)) hBk.w, P.blk k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega]
      · simp [hk', show ¬ k < i + 1 by omega]
  · simp only [mem_setReg, mem_arithFlags]
    rw [VG.Proof.AesOcb.X86_64.blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hBi.w.sub_right (Lay.wSub (W := W) (d := 80) (n := 16) (by decide))).symm
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), VG.Proof.AesOcb.X86_64.blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.l0]
  · simp only [gpr_setReg, gpr_arithFlags, h6, h7, h8, ite_false]
    rw [g₃' r h1 h2 h3 h4 h5, P.gpr r h1 h2 h3 h4 h5 h6 h7 h8]
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, r12₃, sext1]
    rw [Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

theorem pass_ok {K W SP D : Addr} (L : Lay K W SP) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : VG.Proof.AesOcb.X86_64.BodyOk W body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hD : DBuf K W SP t₀ D (16 * m)) (hm0 : 0 < m) (hm : m < 2 ^ 60) {t : State}
    (P : VG.Proof.AesOcb.X86_64.PassInv K W SP D m O0 l X fB ckF t₀ t 0) :
    WP isa (pass body) t (fun t' => VG.Proof.AesOcb.X86_64.PassInv K W SP D m O0 l X fB ckF t₀ t' m) := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ i, k = m - i ∧ i < m ∧ VG.Proof.AesOcb.X86_64.PassInv K W SP D m O0 l X fB ckF t₀ u i) ?_ (m - 0) _
    ⟨0, rfl, hm0, P⟩
  rintro k u ⟨i, rfl, hi, P⟩
  refine WP.mono (VG.Proof.AesOcb.X86_64.pass_step L hB hckF hD hm hi P) fun u' ⟨P', hz⟩ => ?_
  by_cases he : m - (i + 1) = 0
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), (show i + 1 = m by omega) ▸ P'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), m - (i + 1), by omega, i + 1, rfl, by omega, P'⟩

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.Whole`. -/
section

/-!
# AES-OCB on x86-64: the whole blocks (`whole`)

Untrusted: everything here is checked by Lean. `whole f pre post` runs the
first pass (each block XORed with its offset, `pre`), `f` on all the blocks
(`ENCIPHER` or `DECIPHER`), and the second pass from `Offset_0` again
(`post`), each pass also updating the checksum (`whole_ok`): block `k`
becomes `Offset_{k+1} ⊕ g(X_k ⊕ Offset_{k+1})`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt imm_eq eval_e eval_ne)

/-- What `whole` writes: the offset and the checksum, `L_{ntz(i)}`, the
working space of the functions called, the stack below `SP` and the data. -/
abbrev wholeR (W SP D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, wC W, below SP 8, ⟨D, n⟩]

theorem wholeR_mut {W SP D : Addr} {n : Nat} {m m' : Mem} (h : Frame (VG.Proof.AesOcb.X86_64.wholeR W SP D n) m m') :
    Frame (mutR W SP D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The first `k` bytes of a buffer, as a buffer at the same place. -/
theorem DBuf.take' {K W SP : Addr} {s : State} {D : Addr} {n k : Nat} (h : DBuf K W SP s D n) (hk : k ≤ n) :
    DBuf K W SP s D k := by
  have := h.slice (a := 0) (k := k) (by omega)
  rwa [BitVec.add_zero] at this

/-- The `m` blocks of the data. -/
theorem dataArgs_ok {W D : Addr} {t : State} (h15 : t.gpr .r15 = W) {m : Nat}
    (hdata : t.mem.readW (W + BitVec.ofNat 64 208) 64 = D) (h13 : t.gpr .r13 = BitVec.ofNat 64 m)
    (r : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 208) 8) :
    ArgsOk [VG.Impl.AesOcb.X86_64.ld .rdx .r15 dataO, mvr .rcx .r13] t D m := by
  refine ⟨_, by orun [h15, hdata, r], ?_, ?_, fun r h1 h2 _ => ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h13]
  · simp only [gpr_setReg, h1, h2, ite_false]
  all_goals rfl

/-- What `whole` leaves. -/
structure WholePost (K W SP D : Addr) (n m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block) (t t' : State) : Prop where
  env : Env K W SP t'
  frame : Frame (VG.Proof.AesOcb.X86_64.wholeR W SP D n) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  blk : ∀ k < m, blockAtMem t'.mem (D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) = ck

theorem whole_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp b.code) (depth : b.code.depth = 0) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : ∀ {W}, VG.Proof.AesOcb.X86_64.BodyOk W pre (fun b o => b ^^^ o) fC1) (hB2 : ∀ {W}, VG.Proof.AesOcb.X86_64.BodyOk W post (fun b o => b ^^^ o) fC2)
    {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : Addr} {n m : Nat} (hD : DBuf K W SP t D n) (hmn : 16 * m ≤ n) (hm0 : 0 < m) (hm : m < 2 ^ 60)
    {O0 l : Block} (hdata : t.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D) (h13 : t.gpr .r13 = BitVec.ofNat 64 m)
    (hrnd : t.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    (hofs : blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem t.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 m)
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt t.mem K (16 * (R + 1))) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (whole b pre post) t (VG.Proof.AesOcb.X86_64.WholePost K W SP D n m O0 l
      (fun k => G (bytesAt t.mem K (16 * (R + 1))) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
      (ckF2 m) t) := by
  have hDm := hD.take' hmn
  have r₁ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 208) 8 := E.perm.wR (by decide)
  simp only [dataO] at hdata
  -- the first pass
  obtain ⟨s₁, run₁, rbx₁, r12₁, rbp₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [VG.Impl.AesOcb.X86_64.ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)] t = some s₁ ∧
      s₁.gpr .rbx = D + BitVec.ofNat 64 (16 * 0) ∧ s₁.gpr .r12 = BitVec.ofNat 64 (m - 0) ∧
      s₁.gpr .rbp = BitVec.ofNat 64 (0 + 1) ∧
      (∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .rbp → s₁.gpr r = t.gpr r) ∧ s₁.mem = t.mem ∧ s₁.rd = t.rd ∧ s₁.wr = t.wr := by
    refine ⟨_, by orun [E.r15, r₁, hdata], ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]; simp
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h13, Nat.sub_zero]
    · simp only [gpr_setReg, ite_true, sext1]
    · simp only [gpr_setReg, h1, h2, h3, ite_false]
    all_goals rfl
  have E₁ : Env K W SP s₁ := E.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₁ wr₁
  have hD₁ : DBuf K W SP s₁ D (16 * m) := hDm.of_eq rd₁ wr₁
  have P₀ : VG.Proof.AesOcb.X86_64.PassInv K W SP D m O0 l (fun k => blockAtMem s₁.mem (D + BitVec.ofNat 64 (16 * k))) (fun b o => b ^^^ o)
      ckF1 s₁ s₁ 0 :=
    { env := E₁, frame := Frame.refl _ _, rd := rfl, wr := rfl, rbx := rbx₁, rbp := rbp₁, r12 := r12₁
      ofs := by rw [m₁, hofs]; rfl
      ck := by rw [m₁, hck]
      blk := fun k _ => by simp
      l0 := by rw [m₁, hl0]
      gpr := fun _ _ _ _ _ _ _ _ _ => rfl }
  unfold whole
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.pass_ok L hB1 (fun i _ => by rw [hckF1, m₁]) hD₁ hm0 hm P₀) fun s₂ P₂ => ?_)
  have hw := hD.wrap
  -- the slots and the blocks of `W` that the pass does not write
  have kP : ∀ {u : State} {d : Nat}, Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ofsO, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨D, 16 * m⟩] s₁.mem u.mem → (d + 8 ≤ 16 ∨ (48 ≤ d ∧ d + 8 ≤ 96) ∨ 112 ≤ d) →
      d + 8 ≤ 2560 → u.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun h h₁ h₂ => h.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 96) (k := 16) (by omega) h₂ (by decide)
      · exact L.w_w (a := _) (d := 16) (k := 16) (by omega) h₂ (by decide)
      · exact L.w_w (a := _) (d := 32) (k := 16) (by omega) h₂ (by decide)
      · exact (hD₁.w.sub_left (Region.sub_prefix (Nat.le_refl _))).symm.sub_left (Lay.wSub h₂)) (by decide)
  have h15₂ : s₂.gpr .r15 = W := P₂.env.r15
  have h13₂ : s₂.gpr .r13 = BitVec.ofNat 64 m := by
    rw [P₂.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide), h13]
  have hdata₂ : s₂.mem.readW (W + BitVec.ofNat 64 208) 64 = D := by rw [kP P₂.frame (by decide) (by decide), m₁, hdata]
  have hrnd₂ : s₂.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [kP P₂.frame (by decide) (by decide), m₁, hrnd]
  have hD₂ : DBuf K W SP s₂ D (16 * m) := hD₁.of_eq P₂.rd P₂.wr
  refine WP.seq (WP.mono (callBlocks_ok (f := f) (b := b) ok nosp depth L P₂.env hR hrnd₂
    (VG.Proof.AesOcb.X86_64.dataArgs_ok h15₂ hdata₂ h13₂ (P₂.env.perm.wR (by decide))) (dstD hD₂)) fun s₃ P₃ => ?_)
  have E₃ : Env K W SP s₃ := P₂.env.of_saved P₃.saved P₃.rd P₃.wr
  have kC : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨D, 16 * m⟩ → (⟨Q, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 2048⟩ →
      (below SP 8).Disjoint ⟨Q, 16⟩ → blockAtMem s₃.mem Q = blockAtMem s₂.mem Q := fun h₁ h₂ h₃ =>
    VG.Proof.AesOcb.X86_64.blockAtMem_frame P₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h₁
      · exact h₂
      · rw [P₂.env.rsp]; exact h₃.symm
  have kWP : ∀ {d : Nat}, (d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (112 ≤ d ∧ d + 16 ≤ 512)) →
      blockAtMem s₃.mem (W + BitVec.ofNat 64 d) = blockAtMem s₁.mem (W + BitVec.ofNat 64 d) := fun hd => by
    rw [kC ((hD₂.w.sub_right (Lay.wSub (by omega))).symm) (L.w_w (.inl (by omega)) (by omega) (by decide))
      (L.stk_w' (by omega)), VG.Proof.AesOcb.X86_64.blockAtMem_frame P₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 96) (k := 16) (by omega) (by omega) (by decide)
      · exact L.w_w (a := _) (d := 16) (k := 16) (by omega) (by omega) (by decide)
      · exact L.w_w (a := _) (d := 32) (k := 16) (by omega) (by omega) (by decide)
      · exact (hD₁.w.sub_right (Lay.wSub (by omega))).symm)]
  have o0₃ : blockAtMem s₃.mem (W + BitVec.ofNat 64 o0O) = O0 := by rw [kWP (by decide), m₁, ho0]
  -- `Offset_0` again
  obtain ⟨s₄a, run₄a, B₄⟩ := copy16_ok (s := s₃) (a := o0O) (d := ofsO) E₃.r15 (E₃.perm.wR (by decide))
    (E₃.perm.wR (by decide)) (E₃.perm.wW (by decide)) (E₃.perm.wW (by decide))
  have E₄a : Env K W SP s₄a := E₃.keep (fun r hr => B₄.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    B₄.rd B₄.wr
  have hdata₄ : s₄a.mem.readW (W + BitVec.ofNat 64 208) 64 = D := by
    rw [B₄.frame.readW (r := ⟨W + BitVec.ofNat 64 208, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide),
      P₃.frame.readW (r := ⟨W + BitVec.ofNat 64 208, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hD₂.w.sub_right (Lay.wSub (by decide))).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · rw [P₂.env.rsp]; exact (L.stk_w' (by decide)).symm) (by decide), hdata₂]
  have h13₄ : s₄a.gpr .r13 = BitVec.ofNat 64 m := by rw [B₄.gpr _ (by decide), P₃.saved _ (by decide), h13₂]
  have r₄ : InRegions (s₄a.rd ++ s₄a.wr) (W + BitVec.ofNat 64 208) 8 := E₄a.perm.wR (by decide)
  obtain ⟨s₄, run₄, rbx₄, r12₄, rbp₄, g₄, m₄, rd₄, wr₄⟩ : ∃ s₄, runBlock isa
      [VG.Impl.AesOcb.X86_64.ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)] s₄a = some s₄ ∧
      s₄.gpr .rbx = D + BitVec.ofNat 64 (16 * 0) ∧ s₄.gpr .r12 = BitVec.ofNat 64 (m - 0) ∧
      s₄.gpr .rbp = BitVec.ofNat 64 (0 + 1) ∧
      (∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .rbp → s₄.gpr r = s₄a.gpr r) ∧ s₄.mem = s₄a.mem ∧ s₄.rd = s₄a.rd ∧
      s₄.wr = s₄a.wr := by
    refine ⟨_, by orun [E₄a.r15, r₄, hdata₄], ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]; simp
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h13₄, Nat.sub_zero]
    · simp only [gpr_setReg, ite_true, sext1]
    · simp only [gpr_setReg, h1, h2, h3, ite_false]
    all_goals rfl
  have E₄ : Env K W SP s₄ := E₄a.keep (fun r hr => g₄ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₄ wr₄
  have hD₄ : DBuf K W SP s₄ D (16 * m) := hD₂.of_eq (by rw [rd₄, B₄.rd, P₃.rd]) (by rw [wr₄, B₄.wr, P₃.wr])
  have kB₄ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨W, 2560⟩ → blockAtMem s₄.mem Q = blockAtMem s₃.mem Q :=
    fun hQ => by
      rw [m₄]; exact VG.Proof.AesOcb.X86_64.blockAtMem_frame B₄.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hQ.sub_right (Lay.wSub (by decide))
  have hK : bytesAt s₂.mem K (16 * (R + 1)) = bytesAt t.mem K (16 * (R + 1)) := by
    have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
    rw [Proof.AesCcm.X86_64.bytesAt_frame P₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact hD₁.k.sub_left (Region.sub_prefix hRb)) (by omega), m₁]
  have X₄ : ∀ k < m, blockAtMem s₄.mem (D + BitVec.ofNat 64 (16 * k)) =
      G (bytesAt t.mem K (16 * (R + 1))) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)) :=
    fun k hk => by
      rw [kB₄ (hD₂.slice (a := 16 * k) (k := 16) (by omega)).w, hcall P₃ k hk, hK, P₂.blk k hk]
      simp only [hk, ↓reduceIte, m₁]
  have ck₃ : blockAtMem s₃.mem (W + BitVec.ofNat 64 ckO) = ckF2 0 := by
    rw [kC ((hD₂.w.sub_right (Lay.wSub (by decide))).symm) (L.w_w (.inl (by decide)) (by decide) (by decide))
      (L.stk_w' (by decide)), P₂.ck, hckF2₀]
  have P₀' : VG.Proof.AesOcb.X86_64.PassInv K W SP D m O0 l (fun k => blockAtMem s₄.mem (D + BitVec.ofNat 64 (16 * k))) (fun b o => b ^^^ o)
      ckF2 s₄ s₄ 0 :=
    { env := E₄, frame := Frame.refl _ _, rd := rfl, wr := rfl, rbx := rbx₄, rbp := rbp₄, r12 := r12₄
      ofs := by rw [m₄, B₄.val, o0₃]; rfl
      ck := by
        rw [m₄, VG.Proof.AesOcb.X86_64.blockAtMem_frame B₄.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), ck₃]
      blk := fun k _ => by simp
      l0 := by
        rw [m₄, VG.Proof.AesOcb.X86_64.blockAtMem_frame B₄.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
          kWP (by decide), m₁, hl0]
      gpr := fun _ _ _ _ _ _ _ _ _ => rfl }
  refine WP.seq (WP.of_runBlock ⟨s₄, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₄a, Option.bind_some, run₄], ?_⟩)
  refine WP.mono (VG.Proof.AesOcb.X86_64.pass_ok L hB2 (fun i hi => by rw [hckF2, X₄ i hi]) hD₄ hm0 hm P₀') fun s₅ P₅ => ?_
  have subW : ∀ r ∈ [(⟨W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ofsO, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨D, 16 * m⟩], ∃ r' ∈ VG.Proof.AesOcb.X86_64.wholeR W SP D n, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (d := 32) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix hmn⟩
  refine ⟨P₅.env, ?_, by rw [P₅.rd, rd₄, B₄.rd, P₃.rd, P₂.rd, rd₁], by rw [P₅.wr, wr₄, B₄.wr, P₃.wr, P₂.wr, wr₁],
    fun k hk => ?_, P₅.ofs, P₅.ck⟩
  · rw [← m₁]
    refine (P₂.frame.sub subW).trans ((P₃.frame.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix hmn⟩
      · exact ⟨wC W, by simp, VG.Proof.AesOcb.X86_64.sub_wC (by decide) (by decide)⟩
      · rw [P₂.env.rsp]; exact ⟨below SP 8, by simp, fun _ h => h⟩
    · have F₅ := P₅.frame
      rw [m₄] at F₅
      exact (B₄.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., Offset.sub W (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩).trans
        (F₅.sub subW)
  · rw [P₅.blk k hk]
    simp only [hk, ↓reduceIte]
    rw [X₄ k hk]

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.XorPad`. -/
section

/-!
# AES-OCB on x86-64: the rest of the data XORed with `Pad` (`xorPad`)

Untrusted: everything here is checked by Lean. `xorPad` XORs the `r` bytes
at `rbx` with the first `r` bytes of the block at `W + tmpO`, a byte at a
time, counting up in `rcx` (`xorPad_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt eval_e eval_ne length_bytesAt)
open VG.Proof.AesGcm.X86_64 (in_of_covers succ_ofNat bytesAt_succ)

theorem xor_byte (a b : Byte) : ((a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 : Byte) = a ^^^ b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_xor]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega), Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow a.isLt b.isLt)

theorem ea_index_disp (s : State) {b i : Reg} {B : Addr} {j d : Nat} (hb : s.gpr b = B)
    (hi : s.gpr i = BitVec.ofNat 64 j) :
    s.gpr b + s.gpr i * BitVec.ofNat 64 1 + BitVec.ofInt 64 (d : Int) = B + BitVec.ofNat 64 d + BitVec.ofNat 64 j := by
  rw [hb, hi, BitVec.mul_one, Proof.AesCcm.X86_64.offset_nat, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j)]

theorem xor_snoc (xs ys : List Byte) (hl : xs.length = ys.length) (a b : Byte) :
    Spec.Ocb.xor (xs ++ [a]) (ys ++ [b]) = Spec.Ocb.xor xs ys ++ [a ^^^ b] := by
  simp [Spec.Ocb.xor, List.zipWith_append hl]

theorem length_xor_bytes (m : Mem) (p q : Addr) (j : Nat) : (Spec.Ocb.xor (bytesAt m p j) (bytesAt m q j)).length = j := by
  simp [Spec.Ocb.xor, VG.Proof.AesCcm.X86_64.length_bytesAt]

/-- One step of `xorPad`. -/
theorem xorStep_ok (s : State) {P T : Addr} {j r : Nat} (h3 : s.gpr .rbx = P) (h15 : s.gpr .r15 = T)
    (h1 : s.gpr .rcx = BitVec.ofNat 64 j) (h12 : s.gpr .r12 = BitVec.ofNat 64 r)
    (rP : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 j) 1) (wP : InRegions s.wr (P + BitVec.ofNat 64 j) 1)
    (rT : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 112 + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa [.movzx8 .rax { base := .rbx, index := some .rcx },
        .movzx8 .rdx { base := .r15, index := some .rcx, disp := tmpO }, .alu .xor .rax (.reg .rdx),
        .store8 { base := .rbx, index := some .rcx } .rax, addi .rcx 1, .alu .cmp .rcx (.reg .r12)] s = some s' ∧
      s'.mem = s.mem.writeW (P + BitVec.ofNat 64 j)
        (s.mem (P + BitVec.ofNat 64 j) ^^^ s.mem (T + BitVec.ofNat 64 112 + BitVec.ofNat 64 j)) ∧
      s'.gpr .rcx = BitVec.ofNat 64 (j + 1) ∧
      s'.zf = some (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 r == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea₁ := VG.Proof.AesOcb.X86_64.ea_index s h3 h1
  have ea₂ : s.gpr .r15 + s.gpr .rcx * BitVec.ofNat 64 1 + BitVec.ofNat 64 112 =
      T + BitVec.ofNat 64 112 + BitVec.ofNat 64 j := VG.Proof.AesOcb.X86_64.ea_index_disp s (d := 112) h15 h1
  refine ⟨_, by orun [ea₁, ea₂, rP, wP, rT], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, VG.Proof.AesOcb.X86_64.xor_byte]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h1, sext1, ← BitVec.ofNat_add]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h1, h12, sext1,
      ← BitVec.ofNat_add]
  · intro r h₁ h₂ h₃; simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, ite_false]
  all_goals rfl

/-- `xorPad`: the `r` bytes at `P` (in `rbx`), `0 < r < 16`, XORed with the
first `r` bytes at `W + tmpO`. -/
theorem xorPad_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {P : Addr} {r : Nat} (hr : 0 < r) (hr' : r < 16)
    (h3 : s.gpr .rbx = P) (h12 : s.gpr .r12 = BitVec.ofNat 64 r) (hP : DBuf K W SP s P r) :
    WP isa xorPad s fun t => t.mem = writeBytes s.mem P
        (Spec.Ocb.xor (bytesAt s.mem P r) (bytesAt s.mem (W + BitVec.ofNat 64 112) r)) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨s₁, run₁, rcx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov .rcx (.imm 0)] s = some s₁ ∧
      s₁.gpr .rcx = BitVec.ofNat 64 0 ∧ (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by orun [], ?_, fun r h => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, BitVec.xor_self, sext0]
    · simp only [gpr_setReg, gpr_arithFlags, h, ite_false]
    all_goals rfl
  unfold xorPad
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hT : ∀ j < r, InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 112 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [Offset.add_add]; exact E.perm.wR (by omega)
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ j, k = r - j ∧ j < r ∧ u.gpr .rcx = BitVec.ofNat 64 j ∧
      u.mem = writeBytes s.mem P (Spec.Ocb.xor (bytesAt s.mem P j) (bytesAt s.mem (W + BitVec.ofNat 64 112) j)) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr) ?_ (r - 0) _
    ⟨0, rfl, hr, rcx₁, by rw [m₁]; simp [bytesAt, Spec.Ocb.xor, writeBytes_nil], fun r _ _ h => g₁ r h, rd₁, wr₁⟩
  rintro k u ⟨j, rfl, hj, rcx, mem, g, rd, wr⟩
  obtain ⟨u', run', mem', rcx', zf', g', rd', wr'⟩ := VG.Proof.AesOcb.X86_64.xorStep_ok u (P := P) (T := W) (j := j) (r := r)
    (by rw [g _ (by decide) (by decide) (by decide), h3]) (by rw [g _ (by decide) (by decide) (by decide), E.r15]) rcx
    (by rw [g _ (by decide) (by decide) (by decide), h12]) (by rw [rd, wr]; exact in_of_covers hP.rd hj hP.lt)
    (by rw [wr]; exact in_of_covers hP.wr hj hP.lt) (by rw [rd, wr]; exact hT j hj)
  refine WP.of_runBlock ⟨u', run', ?_⟩
  have fr : Frame [⟨P, j⟩] s.mem u.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [VG.Proof.AesOcb.X86_64.length_xor_bytes]; exact VG.Proof.AesOcb.X86_64.contains_pre _ (by omega))
  have hq : u.mem (P + BitVec.ofNat 64 j) = s.mem (P + BitVec.ofNat 64 j) :=
    fr _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat P (show j < 2 ^ 64 by omega)] at hc; omega
  have hqT : u.mem (W + BitVec.ofNat 64 112 + BitVec.ofNat 64 j) = s.mem (W + BitVec.ofNat 64 112 + BitVec.ofNat 64 j) :=
    fr _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      have hdis : (⟨P, r⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 112 + BitVec.ofNat 64 j, 1⟩ := by
        rw [Offset.add_add]; exact hP.w.sub_right (Lay.wSub (by omega))
      exact hdis.sub_left (Region.sub_prefix (by omega)) _ hc (Region.contains_self _ _)
  have hmem : u'.mem = writeBytes s.mem P (Spec.Ocb.xor (bytesAt s.mem P (j + 1)) (bytesAt s.mem (W + BitVec.ofNat 64 112) (j + 1))) := by
    rw [mem', hq, hqT, mem, VG.Proof.AesGcm.X86_64.bytesAt_succ, VG.Proof.AesGcm.X86_64.bytesAt_succ, VG.Proof.AesOcb.X86_64.xor_snoc _ _ (by simp [VG.Proof.AesCcm.X86_64.length_bytesAt]),
      writeBytes_snoc _ _ _ _ (by rw [VG.Proof.AesOcb.X86_64.length_xor_bytes]; omega), VG.Proof.AesOcb.X86_64.length_xor_bytes]
  have hz : u'.zf = some (decide (j + 1 = r)) := by
    rw [zf', Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → u'.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  by_cases he : j + 1 = r
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), r - (j + 1), by omega, j + 1, rfl, by omega, rcx', hmem, gg,
      by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.RestTag`. -/
section

/-!
# AES-OCB on x86-64: the rest of the data and the tag (`rest`, `tag`)

Untrusted: everything here is checked by Lean. `rest` computes
`Offset_* = Offset_m ⊕ L_*` and `Pad = ENCIPHER(K, Offset_*)` (`restHead_ok`),
then for `seal` adds `pad(P_*)` to the checksum and XORs `P_*` with `Pad`
(`restSeal_ok`), and for `open` XORs `C_*` with `Pad` and adds the padded
result to the checksum (`restOpen_ok`). `tag d` writes
`ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ HASH(K, A)` to `W + d` (`tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem pad ctxCiph)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt length_bytesAt bytesAt_frame)

/-- `padCk`: `W + t2O ← pad(S)` and the checksum XORed with it, for the
`r` bytes `S` at `rbx`. -/
theorem padCk_ok {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {S : Addr} {r : Nat} (hr : 0 < r)
    (hr' : r < 16) (h3 : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 r)
    (hS : Covers [⟨S, r⟩] (s.rd ++ s.wr)) (hSW : (⟨S, r⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa padCk s fun t => Frame [⟨W + BitVec.ofNat 64 t2O, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = blockAtMem s.mem (W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt s.mem S r) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rsi → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold padCk
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.padTo_ok E hr hr' (by decide) h3 h12 hS (hSW.sub_right (Lay.wSub (by decide))))
    fun t₁ ⟨fr₁, pad₁, g₁, rd₁, wr₁⟩ => ?_)
  have h15₁ : t₁.gpr .r15 = W := by rw [g₁ _ (by decide) (by decide) (by decide), E.r15]
  obtain ⟨t₂, run₂, B₂⟩ := xor16_ok (s := t₁) (b := .r15) (a := t2O) (d := ckO) h15₁ h15₁ (by decide) (by decide)
    (by rw [rd₁, wr₁]; exact E.perm.wR (by decide)) (by rw [rd₁, wr₁]; exact E.perm.wR (by decide))
    (by rw [wr₁]; exact E.perm.wW (by decide)) (by rw [wr₁]; exact E.perm.wW (by decide))
  refine WP.of_runBlock ⟨t₂, run₂, (fr₁.mono (by simp)).trans (B₂.frame.mono (by simp)), ?_,
    fun r h1 h2 h3 h4 => by rw [B₂.gpr r (by simp [h1, h4]), g₁ r h1 h2 h3], by rw [B₂.rd, rd₁], by rw [B₂.wr, wr₁]⟩
  rw [B₂.val, pad₁, VG.Proof.AesOcb.X86_64.blockAtMem_frame fr₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)]

/-- What the head of `rest` leaves: `Offset_*` and `Pad`. -/
structure RestHead (K W SP : Addr) (R : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩, wC W, below SP 8] t.mem t'.mem
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K
  tmp : blockAtMem t'.mem (W + BitVec.ofNat 64 tmpO) =
    ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K)
  saved : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem restHead_ok (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hrnd : t.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R) :
    WP isa (.seq (.block (xor16 .r14 240 ofsO ++ copy16 ofsO tmpO)) (callBlocks (VG.Proof.AesOcb.X86_64.callees v).enc (oneBlock tmpO))) t
      (VG.Proof.AesOcb.X86_64.RestHead K W SP R t) := by
  obtain ⟨t₁, run₁, B₁⟩ := xor16_ok (s := t) (b := .r14) (a := 240) (d := ofsO) E.r15 E.r14 (by decide) (by decide)
    (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have h15₁ : t₁.gpr .r15 = W := by rw [B₁.gpr _ (by decide), E.r15]
  obtain ⟨t₂, run₂, B₂⟩ := copy16_ok (s := t₁) (a := ofsO) (d := tmpO) h15₁
    (by rw [B₁.rd, B₁.wr]; exact E.perm.wR (by decide)) (by rw [B₁.rd, B₁.wr]; exact E.perm.wR (by decide))
    (by rw [B₁.wr]; exact E.perm.wW (by decide)) (by rw [B₁.wr]; exact E.perm.wW (by decide))
  have E₂ : Env K W SP t₂ := E.keep (fun r hr => by
    rw [B₂.gpr r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide),
      B₁.gpr r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide)]) (by rw [B₂.rd, B₁.rd]) (by rw [B₂.wr, B₁.wr])
  have fr₂ : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₂.mem :=
    (B₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  have hrnd₂ : t₂.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [fr₂.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide), hrnd]
  have ofs₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ofsO) =
      blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K := by
    rw [VG.Proof.AesOcb.X86_64.blockAtMem_frame B₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), B₁.val]
    rfl
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  have cK : ctxCiph t₂.mem K R = ctxCiph t.mem K R := by
    unfold ctxCiph
    rw [VG.Proof.AesCcm.X86_64.bytesAt_frame fr₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide)))
      (by omega)]
  refine WP.seq (WP.of_runBlock ⟨t₂, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₁, Option.bind_some, run₂], ?_⟩)
  refine WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNosp v.encDepth L E₂ hR hrnd₂
    (oneBlock_ok E₂.r15 tmpO (by decide)) (dstW L E₂.perm (d := tmpO) (n := 1) (by decide))) fun t₃ P₃ => ?_
  refine ⟨E₂.of_saved P₃.saved P₃.rd P₃.wr, ?_, ?_, ?_, fun r hr => ?_, by rw [P₃.rd, B₂.rd, B₁.rd],
    by rw [P₃.wr, B₂.wr, B₁.wr]⟩
  · refine (fr₂.mono (by simp)).trans (P₃.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, VG.Proof.AesOcb.X86_64.sub_wC (by decide) (by decide)⟩
    · rw [E₂.rsp]; exact ⟨_, by simp, fun _ h => h⟩
  · rw [VG.Proof.AesOcb.X86_64.blockAtMem_frame P₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · rw [E₂.rsp]; exact (L.stk_w' (by decide)).symm), ofs₂]
  · have := P₃.enc (i := 0) (by decide)
    rw [show 16 * 0 = 0 from rfl, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
    rw [this, B₂.val, B₁.val]
    show ctxCiph t₂.mem K R _ = _
    rw [cK]; rfl
  · have hr' : r ≠ .rax ∧ r ≠ .rdx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hn : r ∉ [Reg.rax, .rdx] := by simp [hr'.1, hr'.2]
    rw [P₃.saved r hr, B₂.gpr r hn, B₁.gpr r hn]

theorem xor_append_right (xs ys zs : List Byte) (h : xs.length = ys.length) :
    Spec.Ocb.xor xs (ys ++ zs) = Spec.Ocb.xor xs ys := by
  simpa [Spec.Ocb.xor] using List.zipWith_append (f := fun x1 x2 : Byte => x1 ^^^ x2) (l₁' := []) (l₂' := zs) h

/-- `r` bytes XORed with the first `r` bytes of a block. -/
theorem xor_bytesAt_block (xs : List Byte) (m : Mem) (Q : Addr) {r : Nat} (hl : xs.length = r) (hr : r ≤ 16) :
    Spec.Ocb.xor xs (bytesAt m Q r) = Spec.Ocb.xor xs (Spec.Ocb.toBytes (blockAtMem m Q)) := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (VG.Proof.AesCcm.X86_64.length_bytesAt _ _ _), show (16 : Nat) = r + (16 - r) by omega,
    Proof.Ocb.bytesAt_append, VG.Proof.AesOcb.X86_64.xor_append_right _ _ _ (by rw [hl, VG.Proof.AesCcm.X86_64.length_bytesAt])]

/-- What `rest` leaves: `Offset_*`, the data XORed with `Pad`, and the
checksum with the padded plaintext (before the XOR for `seal`, after it for
`open`). -/
structure RestPost (enc : Bool) (K W SP : Addr) (R : Nat) (P : Addr) (r : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
    ⟨W + BitVec.ofNat 64 ckO, 16⟩, wC W, below SP 8, ⟨P, r⟩] t.mem t'.mem
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) =
    blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K
  out : bytesAt t'.mem P r = Spec.Ocb.xor (bytesAt t.mem P r)
    (Spec.Ocb.toBytes (ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K)))
  ck : blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) =
    blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) P r)
  saved : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem rest_ok (v : BlocksImpl) (enc : Bool) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hrnd : t.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {P : Addr} {r : Nat} (hr : 0 < r) (hr' : r < 16) (h3 : t.gpr .rbx = P) (h12 : t.gpr .r12 = BitVec.ofNat 64 r)
    (hP : DBuf K W SP t P r) :
    WP isa (VG.Impl.AesOcb.X86_64.rest (VG.Proof.AesOcb.X86_64.callees v) enc) t (VG.Proof.AesOcb.X86_64.RestPost enc K W SP R P r t) := by
  unfold VG.Impl.AesOcb.X86_64.rest
  refine wp_seq_assoc (WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.restHead_ok v L E hR hrnd) fun t₃ H => ?_))
  have h3₃ : t₃.gpr .rbx = P := by rw [H.saved _ (by decide), h3]
  have h12₃ : t₃.gpr .r12 = BitVec.ofNat 64 r := by rw [H.saved _ (by decide), h12]
  have hP₃ : DBuf K W SP t₃ P r := hP.of_eq H.rd H.wr
  have hS₃ : Covers [⟨P, r⟩] (t₃.rd ++ t₃.wr) := hP₃.rd
  -- `P` is apart from what the pieces write in `W` and from the stack.
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨P, r⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
    fun h => hP.w.sub_right (Lay.wSub h)
  have dH : ∀ q ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, wC W, below SP 8],
      (⟨P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact dW (by decide)
    · exact dW (by decide)
    · exact dW (by decide)
    · exact hP.stk.symm
  have dT : ∀ q ∈ [(⟨W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨P, r⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact dW (by decide)
  have dTmp : ∀ q ∈ [(⟨W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨W + BitVec.ofNat 64 tmpO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  have dOfs : ∀ q ∈ [(⟨W + BitVec.ofNat 64 t2O, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ckO, 16⟩],
      (⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have pP₃ : bytesAt t₃.mem P r = bytesAt t.mem P r := VG.Proof.AesCcm.X86_64.bytesAt_frame H.frame dH (by omega)
  have hl : (bytesAt t.mem P r).length = r := VG.Proof.AesCcm.X86_64.length_bytesAt _ _ _
  have hlx : ∀ ys, (Spec.Ocb.xor (bytesAt t.mem P r) (Spec.Ocb.toBytes ys)).length = r := fun ys => by
    simp [Spec.Ocb.xor, VG.Proof.AesCcm.X86_64.length_bytesAt, Proof.Ocb.toBytes_length]; omega
  have fP : ∀ (m : Mem) (xs : List Byte), xs.length = r → Frame [⟨P, r⟩] m (writeBytes m P xs) :=
    fun m xs h => writeBytes_frame _ _ _ (by rw [h]; exact Region.contains_self _ _)
  -- What `xorPad` writes, from the state it starts in.
  have xP : ∀ u : State, bytesAt u.mem P r = bytesAt t.mem P r →
      blockAtMem u.mem (W + BitVec.ofNat 64 tmpO) = blockAtMem t₃.mem (W + BitVec.ofNat 64 tmpO) →
      bytesAt (writeBytes u.mem P (Spec.Ocb.xor (bytesAt u.mem P r) (bytesAt u.mem (W + BitVec.ofNat 64 112) r))) P r =
        Spec.Ocb.xor (bytesAt t.mem P r) (Spec.Ocb.toBytes
          (ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ Spec.Ocb.ctxLstar t.mem K))) := by
    intro u hu ht
    rw [hu, VG.Proof.AesOcb.X86_64.xor_bytesAt_block _ _ _ hl (by omega), show (112 : Nat) = tmpO from rfl, ht, H.tmp,
      Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by rw [hlx]) (by omega), hlx, List.drop_of_length_le
        (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]), List.append_nil]
  have dCk : ∀ q ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, wC W, below SP 8],
      (⟨W + BitVec.ofNat 64 ckO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
  have ck₃ : blockAtMem t₃.mem (W + BitVec.ofNat 64 ckO) = blockAtMem t.mem (W + BitVec.ofNat 64 ckO) :=
    VG.Proof.AesOcb.X86_64.blockAtMem_frame H.frame dCk
  have pW : ∀ {d : Nat}, d + 16 ≤ 2560 → ∀ q ∈ [(⟨P, r⟩ : Region)], (⟨W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q :=
    fun h q hq => by simp only [List.mem_singleton] at hq; subst hq; exact (dW h).symm
  have g7 : ∀ {u u' : State} (a b c d : Reg), (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → u'.gpr r = u.gpr r) →
      a ∉ calleeSaved → b ∉ calleeSaved → c ∉ calleeSaved → d ∉ calleeSaved →
      ∀ r ∈ calleeSaved, u'.gpr r = u.gpr r :=
    fun a b c d g ha hb hc hd r hr => g r (fun h => ha (h ▸ hr)) (fun h => hb (h ▸ hr)) (fun h => hc (h ▸ hr))
      (fun h => hd (h ▸ hr))
  have E' : ∀ {u : State}, (∀ r ∈ calleeSaved, u.gpr r = t₃.gpr r) → u.rd = t₃.rd → u.wr = t₃.wr → Env K W SP u :=
    fun g hrd hwr => H.env.of_saved g hrd hwr
  cases enc
  · -- `open`: the XOR, then the checksum.
    refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.xorPad_ok H.env hr hr' h3₃ h12₃ hP₃) fun t₄ ⟨m₄, g₄, rd₄, wr₄⟩ => ?_)
    have s₄ : ∀ r ∈ calleeSaved, t₄.gpr r = t₃.gpr r :=
      g7 .rax .rdx .rcx .rax (fun r h1 h2 h3 _ => g₄ r h1 h2 h3) (by decide) (by decide) (by decide) (by decide)
    have E₄ : Env K W SP t₄ := E' s₄ rd₄ wr₄
    have fr₄ : Frame [⟨P, r⟩] t₃.mem t₄.mem := by rw [m₄]; exact fP _ _ (by simp [Spec.Ocb.xor, VG.Proof.AesCcm.X86_64.length_bytesAt])
    refine WP.mono (VG.Proof.AesOcb.X86_64.padCk_ok L E₄ hr hr' (by rw [s₄ _ (by decide), h3₃]) (by rw [s₄ _ (by decide), h12₃])
      (by rw [rd₄, wr₄]; exact hS₃) hP.w) fun t₅ ⟨fr₅, ck₅, g₅, rd₅, wr₅⟩ => ?_
    have s₅ : ∀ r ∈ calleeSaved, t₅.gpr r = t₄.gpr r :=
      g7 .rax .rcx .rsi .rdx g₅ (by decide) (by decide) (by decide) (by decide)
    have p₅ : bytesAt t₅.mem P r = bytesAt t₄.mem P r := VG.Proof.AesCcm.X86_64.bytesAt_frame fr₅ dT (by omega)
    refine ⟨E' (fun r hr => by rw [s₅ r hr, s₄ r hr]) (by rw [rd₅, rd₄]) (by rw [wr₅, wr₄]),
      ((H.frame.mono (by simp)).trans (fr₄.mono (by simp))).trans (fr₅.mono (by simp)), ?_, ?_, ?_,
      fun r hr => by rw [s₅ r hr, s₄ r hr, H.saved r hr], by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [VG.Proof.AesOcb.X86_64.blockAtMem_frame fr₅ dOfs, VG.Proof.AesOcb.X86_64.blockAtMem_frame fr₄ (pW (by decide)), H.ofs]
    · rw [p₅, m₄, xP t₃ pP₃ rfl]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ck₅, p₅, VG.Proof.AesOcb.X86_64.blockAtMem_frame fr₄ (pW (by decide)), ck₃]
  · -- `seal`: the checksum, then the XOR.
    refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.padCk_ok L H.env hr hr' h3₃ h12₃ hS₃ hP.w) fun t₄ ⟨fr₄, ck₄, g₄, rd₄, wr₄⟩ => ?_)
    have s₄ : ∀ r ∈ calleeSaved, t₄.gpr r = t₃.gpr r :=
      g7 .rax .rcx .rsi .rdx g₄ (by decide) (by decide) (by decide) (by decide)
    have E₄ : Env K W SP t₄ := E' s₄ rd₄ wr₄
    have p₄ : bytesAt t₄.mem P r = bytesAt t₃.mem P r := VG.Proof.AesCcm.X86_64.bytesAt_frame fr₄ dT (by omega)
    refine WP.mono (VG.Proof.AesOcb.X86_64.xorPad_ok E₄ hr hr' (by rw [s₄ _ (by decide), h3₃]) (by rw [s₄ _ (by decide), h12₃])
      (hP₃.of_eq rd₄ wr₄)) fun t₅ ⟨m₅, g₅, rd₅, wr₅⟩ => ?_
    have s₅ : ∀ r ∈ calleeSaved, t₅.gpr r = t₄.gpr r :=
      g7 .rax .rdx .rcx .rax (fun r h1 h2 h3 _ => g₅ r h1 h2 h3) (by decide) (by decide) (by decide) (by decide)
    have fr₅ : Frame [⟨P, r⟩] t₄.mem t₅.mem := by rw [m₅]; exact fP _ _ (by simp [Spec.Ocb.xor, VG.Proof.AesCcm.X86_64.length_bytesAt])
    refine ⟨E' (fun r hr => by rw [s₅ r hr, s₄ r hr]) (by rw [rd₅, rd₄]) (by rw [wr₅, wr₄]),
      ((H.frame.mono (by simp)).trans (fr₄.mono (by simp))).trans (fr₅.mono (by simp)), ?_, ?_, ?_,
      fun r hr => by rw [s₅ r hr, s₄ r hr, H.saved r hr], by rw [rd₅, rd₄, H.rd], by rw [wr₅, wr₄, H.wr]⟩
    · rw [VG.Proof.AesOcb.X86_64.blockAtMem_frame fr₅ (pW (by decide)), VG.Proof.AesOcb.X86_64.blockAtMem_frame fr₄ dOfs, H.ofs]
    · rw [m₅, xP t₄ (by rw [p₄, pP₃]) (VG.Proof.AesOcb.X86_64.blockAtMem_frame fr₄ dTmp)]
    · simp only [↓reduceIte]
      rw [VG.Proof.AesOcb.X86_64.blockAtMem_frame fr₅ (pW (by decide)), ck₄, ck₃, pP₃]

/-- What `tag d` leaves. -/
structure TagPost (K W SP : Addr) (R d : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 d, 16⟩, wC W, below SP 8] t.mem t'.mem
  val : blockAtMem t'.mem (W + BitVec.ofNat 64 d) =
    ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^
      blockAtMem t.mem (W + BitVec.ofNat 64 ldO)) ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 sumO)
  saved : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem tag_ok (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hrnd : t.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {d : Nat} (hd : d = tagO ∨ d = t2O) :
    WP isa (tag (VG.Proof.AesOcb.X86_64.callees v) d) t (VG.Proof.AesOcb.X86_64.TagPost K W SP R d t) := by
  have hd' : d = 0 ∨ d = 128 := hd
  have nr : ∀ r ∈ calleeSaved, r ∉ [Reg.rax, .rdx] := by decide
  have nE : ∀ r ∈ [Reg.r14, .r15, .rsp], r ∉ [Reg.rax, .rdx] := by decide
  obtain ⟨t₁, run₁, B₁⟩ := copy16_ok (s := t) (a := ckO) (d := tmpO) E.r15
    (E.perm.wR (by decide)) (E.perm.wR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => B₁.gpr r (nE r hr)) B₁.rd B₁.wr
  obtain ⟨t₂, run₂, B₂⟩ := xor16_ok (s := t₁) (b := .r15) (a := ofsO) (d := tmpO) E₁.r15 E₁.r15 (by decide) (by decide)
    (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide)) (E₁.perm.wW (by decide)) (E₁.perm.wW (by decide))
  have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => B₂.gpr r (nE r hr)) B₂.rd B₂.wr
  obtain ⟨t₃, run₃, B₃⟩ := xor16_ok (s := t₂) (b := .r15) (a := ldO) (d := tmpO) E₂.r15 E₂.r15 (by decide) (by decide)
    (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide)) (E₂.perm.wW (by decide)) (E₂.perm.wW (by decide))
  have E₃ : Env K W SP t₃ := E₂.keep (fun r hr => B₃.gpr r (nE r hr)) B₃.rd B₃.wr
  have tW : ∀ {a : Nat}, (a + 16 ≤ 112 ∨ 128 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨W + BitVec.ofNat 64 tmpO, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w h h' (by decide)
  have fr₃ : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩] t.mem t₃.mem :=
    (B₁.frame.trans B₂.frame).trans B₃.frame
  have hrnd₃ : t₃.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [fr₃.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide), hrnd]
  have tmp₃ : blockAtMem t₃.mem (W + BitVec.ofNat 64 tmpO) =
      blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (W + BitVec.ofNat 64 ldO) := by
    rw [B₃.val, B₂.val, B₁.val, VG.Proof.AesOcb.X86_64.blockAtMem_frame B₁.frame (tW (by decide) (by decide)),
      VG.Proof.AesOcb.X86_64.blockAtMem_frame (B₁.frame.trans B₂.frame) (tW (by decide) (by decide))]
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  have cK : ctxCiph t₃.mem K R = ctxCiph t.mem K R := by
    unfold ctxCiph
    rw [VG.Proof.AesCcm.X86_64.bytesAt_frame fr₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))) (by omega)]
  unfold tag
  refine WP.seq (WP.of_runBlock ⟨t₃, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, VG.Proof.AesCcm.X86_64.runBlock_append, run₁, Option.bind_some, run₂,
    Option.bind_some, run₃], ?_⟩)
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNosp v.encDepth L E₃ hR
    hrnd₃ (oneBlock_ok E₃.r15 tmpO (by decide)) (dstW L E₃.perm (d := tmpO) (n := 1) (by decide))) fun t₄ P₄ => ?_)
  have E₄ : Env K W SP t₄ := E₃.of_saved P₄.saved P₄.rd P₄.wr
  have tmp₄ : blockAtMem t₄.mem (W + BitVec.ofNat 64 tmpO) =
      ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^
        blockAtMem t.mem (W + BitVec.ofNat 64 ldO)) := by
    have := P₄.enc (i := 0) (by decide)
    rw [show 16 * 0 = 0 from rfl, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
    rw [this, tmp₃, ← cK]; rfl
  obtain ⟨t₅, run₅, B₅⟩ := copy16_ok (s := t₄) (a := tmpO) (d := d) E₄.r15
    (E₄.perm.wR (by decide)) (E₄.perm.wR (by decide)) (E₄.perm.wW (by omega)) (E₄.perm.wW (by omega))
  have E₅ : Env K W SP t₅ := E₄.keep (fun r hr => B₅.gpr r (nE r hr)) B₅.rd B₅.wr
  obtain ⟨t₆, run₆, B₆⟩ := xor16_ok (s := t₅) (b := .r15) (a := sumO) (d := d) E₅.r15 E₅.r15 (by decide) (by decide)
    (E₅.perm.wR (by decide)) (E₅.perm.wR (by decide)) (E₅.perm.wW (by omega)) (E₅.perm.wW (by omega))
  refine WP.of_runBlock ⟨t₆, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₅, Option.bind_some, run₆], ?_⟩
  have dD : ∀ {a : Nat}, (a + 16 ≤ d ∨ d + 16 ≤ a) → a + 16 ≤ 2560 →
      ∀ q ∈ [(⟨W + BitVec.ofNat 64 d, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 a, 16⟩ : Region).Disjoint q :=
    fun h h' q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w h h' (by omega)
  have dCall : ∀ q ∈ [(⟨W + BitVec.ofNat 64 tmpO, 16 * 1⟩ : Region), ⟨W + BitVec.ofNat 64 512, 2048⟩,
      below (t₃.gpr .rsp) 8], (⟨W + BitVec.ofNat 64 sumO, 16⟩ : Region).Disjoint q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [E₃.rsp]; exact (L.stk_w' (by decide)).symm
  refine ⟨E₅.keep (fun r hr => B₆.gpr r (nE r hr)) B₆.rd B₆.wr, ?_, ?_,
    fun r hr => by rw [B₆.gpr r (nr r hr), B₅.gpr r (nr r hr), P₄.saved r hr, B₃.gpr r (nr r hr),
      B₂.gpr r (nr r hr), B₁.gpr r (nr r hr)],
    by rw [B₆.rd, B₅.rd, P₄.rd, B₃.rd, B₂.rd, B₁.rd], by rw [B₆.wr, B₅.wr, P₄.wr, B₃.wr, B₂.wr, B₁.wr]⟩
  · refine (((fr₃.mono (by simp)).trans (P₄.frame.sub fun r hr => ?_)).trans (B₅.frame.mono (by simp))).trans
      (B₆.frame.mono (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, by simp, VG.Proof.AesOcb.X86_64.sub_wC (by decide) (by decide)⟩
    · rw [E₃.rsp]; exact ⟨_, by simp, fun _ h => h⟩
  · rw [B₆.val, B₅.val, tmp₄, VG.Proof.AesOcb.X86_64.blockAtMem_frame B₅.frame (dD (by simp only [sumO]; omega) (by decide)),
      VG.Proof.AesOcb.X86_64.blockAtMem_frame P₄.frame dCall, VG.Proof.AesOcb.X86_64.blockAtMem_frame fr₃ (tW (by decide) (by decide))]

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.Body`. -/
section

/-!
# AES-OCB on x86-64: the data (`body`)

Untrusted: everything here is checked by Lean. `body` runs `whole` on the
`m = len / 16` whole blocks if there are any (`wholeIte_ok`), then `rest` on
the `len mod 16` bytes after them if there are any (`restIte_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt eval_e length_bytesAt bytesAt_frame)

/-- The number of whole blocks, in `r13`. -/
theorem bodyHead_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {n : Nat} (hn : n < 2 ^ 64)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) :
    ∃ s₁, runBlock isa [VG.Impl.AesOcb.X86_64.ld .r13 .r15 lenO, .shift .shr .r13 4, .alu .test .r13 (.reg .r13)] s = some s₁ ∧
      s₁.gpr .r13 = BitVec.ofNat 64 (n / 16) ∧ s₁.zf = some (decide (n / 16 = 0)) ∧ s₁.mem = s.mem ∧
      (∀ r, r ≠ .r13 → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 216) 8 := E.perm.wR (by decide)
  refine ⟨_, by orun [E.r15, r₁, hlen], ?_, ?_, ?_, fun r h => ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, Proof.AesCcm.X86_64.shr4 _ hn]
  · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, Proof.AesCcm.X86_64.shr4 _ hn,
      Proof.AesCcm.X86_64.and_self_beq (show n / 16 < 2 ^ 64 by omega)]
  · rfl
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h, ite_false]
  all_goals rfl

/-- The whole blocks, if there are any. -/
theorem wholeIte_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp b.code) (depth : b.code.depth = 0) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : ∀ {W}, VG.Proof.AesOcb.X86_64.BodyOk W pre (fun b o => b ^^^ o) fC1) (hB2 : ∀ {W}, VG.Proof.AesOcb.X86_64.BodyOk W post (fun b o => b ^^^ o) fC2)
    {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : Addr} {n : Nat} (hD : DBuf K W SP s D n) {O0 l : Block}
    (hdata : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n)
    (hrnd : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (n / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (.seq (.block [VG.Impl.AesOcb.X86_64.ld .r13 .r15 lenO, .shift .shr .r13 4, .alu .test .r13 (.reg .r13)])
        (.ite .e (.block []) (whole b pre post))) s
      (VG.Proof.AesOcb.X86_64.WholePost K W SP D (16 * (n / 16)) (n / 16) O0 l
        (fun k => G (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
        (ckF2 (n / 16)) s) := by
  have hn := hD.lt
  obtain ⟨s₁, run₁, r13₁, zf₁, m₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86_64.bodyHead_ok E hn hlen
  have E₁ : Env K W SP s₁ := E.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite _ (eval_e zf₁) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hm : n / 16 = 0 := of_decide_eq_true h0
    exact ⟨E₁, by rw [m₁]; exact Frame.refl _ _, rd₁, wr₁, fun k hk => absurd hk (by omega),
      by rw [m₁, hofs, hm]; rfl, by rw [m₁, hck, hm, hckF2₀, hm]⟩
  · have hm : n / 16 ≠ 0 := of_decide_eq_false h0
    rw [← m₁]
    refine WP.mono (VG.Proof.AesOcb.X86_64.whole_ok (O0 := O0) (l := l) ok nosp depth hcall hB1 hB2 L E₁ hR (hD.take' (Nat.mul_div_le n 16) |>.of_eq rd₁ wr₁)
      (Nat.le_refl _) (by omega) (by omega) (by rw [m₁]; exact hdata) r13₁ (by rw [m₁]; exact hrnd)
      (by rw [m₁]; exact hofs) (by rw [m₁]; exact ho0) (by rw [m₁]; exact hck) (by rw [m₁]; exact hl0)
      (fun i => by rw [m₁]; exact hckF1 i) hckF2₀ (fun i => by rw [m₁]; exact hckF2 i)) fun t P => ?_
    exact ⟨P.env, by rw [← m₁]; exact P.frame, by rw [P.rd, rd₁], by rw [P.wr, wr₁], P.blk, P.ofs, P.ck⟩

/-- Where the rest of the data is, and how long it is. -/
theorem bodyTail_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {D : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (hdata : t.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D)
    (hlen : t.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) :
    ∃ t₁, runBlock isa [VG.Impl.AesOcb.X86_64.ld .rbx .r15 dataO, VG.Impl.AesOcb.X86_64.ld .rax .r15 lenO, mvr .r12 .rax, .alu .and .r12 (.imm 15),
        .alu .sub .rax (.reg .r12), .alu .add .rbx (.reg .rax), .alu .test .r12 (.reg .r12)] t = some t₁ ∧
      t₁.gpr .rbx = D + BitVec.ofNat 64 (16 * (n / 16)) ∧ t₁.gpr .r12 = BitVec.ofNat 64 (n % 16) ∧
      t₁.zf = some (decide (n % 16 = 0)) ∧ t₁.mem = t.mem ∧
      (∀ r, r ≠ .rbx → r ≠ .rax → r ≠ .r12 → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have r₁ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 208) 8 := E.perm.wR (by decide)
  have r₂ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 216) 8 := E.perm.wR (by decide)
  simp only [dataO] at hdata
  have e15 : BitVec.signExtend 64 (15 : BitVec 32) = 15#64 := by decide
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 (n % 16) = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [Proof.AesCcm.X86_64.ofNat_sub (Nat.mod_le _ _) hn, show n - n % 16 = 16 * (n / 16) by omega]
  refine ⟨_, by orun [E.r15, r₁, r₂, hdata, hlen], ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e15, Proof.AesCcm.X86_64.and15',
      VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt hn, hsub]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e15, Proof.AesCcm.X86_64.and15',
      VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt hn]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, e15,
      Proof.AesCcm.X86_64.and15', VG.Proof.AesCcm.X86_64.toNat_ofNat_of_lt hn,
      Proof.AesCcm.X86_64.and_self_beq (show n % 16 < 2 ^ 64 by omega)]
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, h1, h2, h3, ite_false]
  all_goals rfl

/-- What the rest of the data leaves, if there is any: `r` bytes at `P`. -/
structure TailPost (enc : Bool) (K W SP : Addr) (R : Nat) (P : Addr) (r : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
    ⟨W + BitVec.ofNat 64 ckO, 16⟩, wC W, below SP 8, ⟨P, r⟩] t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) =
    if 0 < r then blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem K
    else blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)
  out : bytesAt t'.mem P r =
    if 0 < r then Spec.Ocb.xor (bytesAt t.mem P r)
      (Spec.Ocb.toBytes (ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem K)))
    else bytesAt t.mem P r
  ck : blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) =
    if 0 < r then blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) P r)
    else blockAtMem t.mem (W + BitVec.ofNat 64 ckO)

/-- The rest of the data, if there is any. -/
theorem restIte_ok (v : BlocksImpl) (enc : Bool) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hrnd : t.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {D : Addr} {n : Nat} (hD : DBuf K W SP t D n)
    (hdata : t.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D)
    (hlen : t.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) :
    WP isa (.seq (.block [VG.Impl.AesOcb.X86_64.ld .rbx .r15 dataO, VG.Impl.AesOcb.X86_64.ld .rax .r15 lenO, mvr .r12 .rax, .alu .and .r12 (.imm 15),
        .alu .sub .rax (.reg .r12), .alu .add .rbx (.reg .rax), .alu .test .r12 (.reg .r12)])
        (.ite .e (.block []) (VG.Impl.AesOcb.X86_64.rest (VG.Proof.AesOcb.X86_64.callees v) enc))) t
      (VG.Proof.AesOcb.X86_64.TailPost enc K W SP R (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) t) := by
  have hn := hD.lt
  obtain ⟨t₁, run₁, rbx₁, r12₁, zf₁, m₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86_64.bodyTail_ok E hn hdata hlen
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite _ (eval_e zf₁) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hr : ¬ 0 < n % 16 := by have := of_decide_eq_true h0; omega
    refine ⟨E₁, by rw [m₁]; exact Frame.refl _ _, rd₁, wr₁, ?_, ?_, ?_⟩ <;> simp only [hr, ↓reduceIte, m₁]
  · have hr : 0 < n % 16 := by have := of_decide_eq_false h0; omega
    have hP : DBuf K W SP t₁ (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
      (hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)).of_eq rd₁ wr₁
    refine WP.mono (VG.Proof.AesOcb.X86_64.rest_ok v enc L E₁ hR (by rw [m₁]; exact hrnd) hr (Nat.mod_lt _ (by decide)) rbx₁ r12₁ hP)
      fun t' P => ?_
    refine ⟨P.env, by rw [← m₁]; exact P.frame, by rw [P.rd, rd₁], by rw [P.wr, wr₁], ?_, ?_, ?_⟩ <;>
      simp only [hr, ↓reduceIte]
    · rw [P.ofs, m₁]
    · rw [P.out, m₁]
    · rw [P.ck, m₁]

/-- What `body` writes: the offset and the checksum, `L_{ntz(i)}`, `Pad` and
`pad(·)`, the working space of the functions called, the stack and the data. -/
abbrev bodyR (W SP D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 48⟩, wC W, below SP 8, ⟨D, n⟩]

theorem bodyR_mut {W SP D : Addr} {n : Nat} {m m' : Mem} (h : Frame (VG.Proof.AesOcb.X86_64.bodyR W SP D n) m m') :
    Frame (mutR W SP D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- What `body` leaves: the data, the offset and the checksum. -/
structure BodyPost (K W SP D : Addr) (n : Nat) (out : List Byte) (ofs ck : Block) (s t : State) : Prop where
  env : Env K W SP t
  frame : Frame (VG.Proof.AesOcb.X86_64.bodyR W SP D n) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : bytesAt t.mem D n = out
  ofs : blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) = ofs
  ck : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = ck

/-- A checksum of blocks `X i`. -/
def ckOf (X : Nat → Block) : Nat → Block
  | 0 => 0
  | i + 1 => VG.Proof.AesOcb.X86_64.ckOf X i ^^^ X i

theorem ckOf_eq {X : Nat → Block} {p : List Byte} {m : Nat} (h : ∀ i < m, X i = Spec.Ocb.blockAt p i) :
    VG.Proof.AesOcb.X86_64.ckOf X m = Proof.Ocb.ckAt p m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [VG.Proof.AesOcb.X86_64.ckOf, Proof.Ocb.ckAt, ih (fun i hi => h i (by omega)), h m (by omega)]

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} {m : Nat} (h : ∀ i < m, f i = g i) :
    (List.range m).flatMap f = (List.range m).flatMap g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun i hi => h i (by omega))]
    simp only [List.flatMap_cons, List.flatMap_nil, h m (by omega)]

/-- `ENCIPHER` from the key schedule, whatever its length. -/
def encG (ks : List Byte) : Cipher := Spec.Ocb.aesWith (ks.length / 16 - 1) ks

/-- `DECIPHER` from the key schedule, whatever its length. -/
def decG (ks : List Byte) : Cipher := Spec.Ocb.aesInvWith (ks.length / 16 - 1) ks

theorem encG_eq (m : Mem) (K : Addr) (R : Nat) : VG.Proof.AesOcb.X86_64.encG (bytesAt m K (16 * (R + 1))) = ctxCiph m K R := by
  rw [VG.Proof.AesOcb.X86_64.encG, VG.Proof.AesCcm.X86_64.length_bytesAt, show 16 * (R + 1) / 16 - 1 = R by omega]; rfl

theorem decG_eq (m : Mem) (K : Addr) (R : Nat) : VG.Proof.AesOcb.X86_64.decG (bytesAt m K (16 * (R + 1))) = Spec.Ocb.ctxInv m K R := by
  rw [VG.Proof.AesOcb.X86_64.decG, VG.Proof.AesCcm.X86_64.length_bytesAt, show 16 * (R + 1) / 16 - 1 = R by omega]; rfl

theorem hcall_enc {s s' : State} {K D S : Addr} {R n : Nat} (h : BPost Spec.Aes.cipher s K D S R n s') :
    ∀ i < n, blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      VG.Proof.AesOcb.X86_64.encG (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) := fun i hi => by
  rw [h.enc hi, VG.Proof.AesOcb.X86_64.encG_eq]; rfl

theorem hcall_dec {s s' : State} {K D S : Addr} {R n : Nat} (h : BPost Spec.Aes.invCipher s K D S R n s') :
    ∀ i < n, blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      VG.Proof.AesOcb.X86_64.decG (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) := fun i hi => by
  rw [h.dec hi, VG.Proof.AesOcb.X86_64.decG_eq]; rfl

/-- A buffer apart from `W`, the stack and `⟨P, r⟩` misses what `rest` writes. -/
theorem disj_tail {W SP Q P : Addr} {k r : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hs : (below SP 8).Disjoint ⟨Q, k⟩) (hp : (⟨Q, k⟩ : Region).Disjoint ⟨P, r⟩) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, wC W, below SP 8, ⟨P, r⟩], (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hs.symm
  · exact hp

/-- A buffer apart from `W`, the stack and `⟨D, n⟩` misses what `whole` writes. -/
theorem disj_whole {W SP Q D : Addr} {k n : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hs : (below SP 8).Disjoint ⟨Q, k⟩) (hp : (⟨Q, k⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ x ∈ VG.Proof.AesOcb.X86_64.wholeR W SP D n, (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hs.symm
  · exact hp

theorem wholeR_sub {W SP D : Addr} {k n : Nat} (hk : k ≤ n) :
    ∀ r ∈ VG.Proof.AesOcb.X86_64.wholeR W SP D k, ∃ r' ∈ VG.Proof.AesOcb.X86_64.bodyR W SP D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Region.sub_prefix hk⟩

theorem tailR_sub {W SP D : Addr} {n a r : Nat} (h : a + r ≤ n) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, wC W, below SP 8, ⟨D + BitVec.ofNat 64 a, r⟩],
      ∃ r' ∈ VG.Proof.AesOcb.X86_64.bodyR W SP D n, Region.Sub x r' := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Offset.sub_base D h⟩

/-- `body` for `seal`. -/
theorem bodySeal_ok (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hrnd : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {D : Addr} {n : Nat} (hD : DBuf K W SP s D n) (hdata : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) {O0 : Block}
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0) :
    WP isa (VG.Impl.AesOcb.X86_64.body (VG.Proof.AesOcb.X86_64.callees v) true) s (VG.Proof.AesOcb.X86_64.BodyPost K W SP D n
      (if 0 < n % 16 then
        Proof.Ocb.encBlocks (ctxCiph s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem K R (offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K)))
      else Proof.Ocb.encBlocks (ctxCiph s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K
       else offAt O0 (ctxLstar s.mem K) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16) ^^^ pad ((bytesAt s.mem D n).drop (16 * (n / 16)))
      else Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : DBuf K W SP s D (16 * (n / 16)) := hD.take' hmn
  have hP : DBuf K W SP s (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)
  have dDP : (⟨D, 16 * (n / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega)
  have hl : ∀ i < n / 16, blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem D (by omega)).symm
  simp only [VG.Impl.AesOcb.X86_64.body, ↓reduceIte]
  refine wp_seq_assoc (WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.wholeIte_ok (O0 := O0) (l := ctxLstar s.mem K)
    (ckF1 := VG.Proof.AesOcb.X86_64.ckOf fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => VG.Proof.AesOcb.X86_64.ckOf (fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (n / 16))
    v.encOk v.encNosp v.encDepth VG.Proof.AesOcb.X86_64.hcall_enc VG.Proof.AesOcb.X86_64.sealPre_ok VG.Proof.AesOcb.X86_64.xorOfs_ok L E hR hD hdata hlen hrnd hofs ho0 hck hl0
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR W SP D (16 * (n / 16))) s.mem t.mem := VG.Proof.AesOcb.X86_64.wholeR_mut Pw.frame
  have hrnd₁ := (VG.Proof.AesOcb.X86_64.kept_read L hDm.w fW (d := 232) (by decide)).trans hrnd
  have hdata₁ := (VG.Proof.AesOcb.X86_64.kept_read L hDm.w fW (d := 208) (by decide)).trans hdata
  have hlen₁ := (VG.Proof.AesOcb.X86_64.kept_read L hDm.w fW (d := 216) (by decide)).trans hlen
  refine WP.mono (VG.Proof.AesOcb.X86_64.restIte_ok v true L Pw.env hR hrnd₁ (hD.of_eq Pw.rd Pw.wr) hdata₁ hlen₁) fun t' Pt => ?_
  have cT : ctxCiph t.mem K R = ctxCiph s.mem K R := VG.Proof.AesOcb.X86_64.ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem K = ctxLstar s.mem K :=
    VG.Proof.AesOcb.X86_64.blockAtMem_frame fW fun r hr => (k_mut L hDm.k r hr).sub_left (Lay.kSub (by decide))
  have pT : bytesAt t.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    VG.Proof.AesCcm.X86_64.bytesAt_frame Pw.frame (VG.Proof.AesOcb.X86_64.disj_whole hP.w hP.stk dDP.symm) (by omega)
  have rest : (bytesAt s.mem D n).drop (16 * (n / 16)) = bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem D hmn, show n - 16 * (n / 16) = n % 16 by omega]
  have ckT : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16) := by
    rw [Pw.ck, VG.Proof.AesOcb.X86_64.ckOf_eq hl]
  have blk : bytesAt t'.mem D (16 * (n / 16)) =
      Proof.Ocb.encBlocks (ctxCiph s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) := by
    rw [VG.Proof.AesCcm.X86_64.bytesAt_frame Pt.frame (VG.Proof.AesOcb.X86_64.disj_tail hDm.w hDm.stk dDP) (by omega), Proof.Ocb.bytesAt_blocks, Proof.Ocb.encBlocks]
    refine VG.Proof.AesOcb.X86_64.flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (VG.Proof.AesCcm.X86_64.length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, VG.Proof.AesOcb.X86_64.encG_eq, hl i hi,
      BitVec.xor_comm]
  refine ⟨Pt.env, (Pw.frame.sub (VG.Proof.AesOcb.X86_64.wholeR_sub hmn)).trans (Pt.frame.sub (VG.Proof.AesOcb.X86_64.tailR_sub (by omega))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · have e := Proof.Ocb.bytesAt_append t'.mem D (16 * (n / 16)) (n % 16)
    rw [show 16 * (n / 16) + n % 16 = n by omega] at e
    rw [e, blk, Pt.out]
    by_cases hr : 0 < n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
      simp only [hr, ↓reduceIte, show n % 16 = 0 by omega, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    simp only [↓reduceIte, pT, rest]

theorem ckOf_dck {X : Nat → Block} {inv : Cipher} {o0 l : Block} {c : List Byte} {m : Nat}
    (h : ∀ i < m, X i = Proof.Ocb.decBlock inv o0 l c i) : VG.Proof.AesOcb.X86_64.ckOf X m = Proof.Ocb.dckAt inv o0 l c m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [VG.Proof.AesOcb.X86_64.ckOf, Proof.Ocb.dckAt, ih (fun i hi => h i (by omega)), h m (by omega)]

/-- `body` for `open`. -/
theorem bodyOpen_ok (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hrnd : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {D : Addr} {n : Nat} (hD : DBuf K W SP s D n) (hdata : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) {O0 : Block}
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0) :
    WP isa (VG.Impl.AesOcb.X86_64.body (VG.Proof.AesOcb.X86_64.callees v) false) s (VG.Proof.AesOcb.X86_64.BodyPost K W SP D n
      (if 0 < n % 16 then
        Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem K R (offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K)))
      else Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K
       else offAt O0 (ctxLstar s.mem K) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) ^^^
          pad (Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem K R (offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K))))
      else Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16)) s) := by
  have hn := hD.lt
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hDm : DBuf K W SP s D (16 * (n / 16)) := hD.take' hmn
  have hP : DBuf K W SP s (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)
  have dDP : (⟨D, 16 * (n / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega)
  have hl : ∀ i < n / 16, blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem D (by omega)).symm
  simp only [VG.Impl.AesOcb.X86_64.body, Bool.false_eq_true, ↓reduceIte]
  refine wp_seq_assoc (WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.wholeIte_ok (O0 := O0) (l := ctxLstar s.mem K) (ckF1 := fun _ => 0)
    (ckF2 := VG.Proof.AesOcb.X86_64.ckOf fun i => VG.Proof.AesOcb.X86_64.decG (bytesAt s.mem K (16 * (R + 1)))
      (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (ctxLstar s.mem K) (i + 1)) ^^^
        offAt O0 (ctxLstar s.mem K) (i + 1))
    v.decOk v.decNosp v.decDepth VG.Proof.AesOcb.X86_64.hcall_dec VG.Proof.AesOcb.X86_64.xorOfs_ok VG.Proof.AesOcb.X86_64.openPost_ok L E hR hD hdata hlen hrnd hofs ho0 hck hl0
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR W SP D (16 * (n / 16))) s.mem t.mem := VG.Proof.AesOcb.X86_64.wholeR_mut Pw.frame
  have hrnd₁ := (VG.Proof.AesOcb.X86_64.kept_read L hDm.w fW (d := 232) (by decide)).trans hrnd
  have hdata₁ := (VG.Proof.AesOcb.X86_64.kept_read L hDm.w fW (d := 208) (by decide)).trans hdata
  have hlen₁ := (VG.Proof.AesOcb.X86_64.kept_read L hDm.w fW (d := 216) (by decide)).trans hlen
  refine WP.mono (VG.Proof.AesOcb.X86_64.restIte_ok v false L Pw.env hR hrnd₁ (hD.of_eq Pw.rd Pw.wr) hdata₁ hlen₁) fun t' Pt => ?_
  have cT : ctxCiph t.mem K R = ctxCiph s.mem K R := VG.Proof.AesOcb.X86_64.ctxCiph_mut L hDm.k fW hR
  have lT : ctxLstar t.mem K = ctxLstar s.mem K :=
    VG.Proof.AesOcb.X86_64.blockAtMem_frame fW fun r hr => (k_mut L hDm.k r hr).sub_left (Lay.kSub (by decide))
  have pT : bytesAt t.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    VG.Proof.AesCcm.X86_64.bytesAt_frame Pw.frame (VG.Proof.AesOcb.X86_64.disj_whole hP.w hP.stk dDP.symm) (by omega)
  have rest : (bytesAt s.mem D n).drop (16 * (n / 16)) = bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem D hmn, show n - 16 * (n / 16) = n % 16 by omega]
  have ckT : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) =
      Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) := by
    rw [Pw.ck, VG.Proof.AesOcb.X86_64.ckOf_dck fun i hi => by rw [VG.Proof.AesOcb.X86_64.decG_eq, hl i hi, Proof.Ocb.decBlock, BitVec.xor_comm]]
  have blk : bytesAt t'.mem D (16 * (n / 16)) =
      Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) := by
    rw [VG.Proof.AesCcm.X86_64.bytesAt_frame Pt.frame (VG.Proof.AesOcb.X86_64.disj_tail hDm.w hDm.stk dDP) (by omega), Proof.Ocb.bytesAt_blocks, Proof.Ocb.decBlocks]
    refine VG.Proof.AesOcb.X86_64.flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (VG.Proof.AesCcm.X86_64.length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, VG.Proof.AesOcb.X86_64.decG_eq, hl i hi,
      Proof.Ocb.decBlock, BitVec.xor_comm]
  have e := Proof.Ocb.bytesAt_append t'.mem D (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega] at e
  refine ⟨Pt.env, (Pw.frame.sub (VG.Proof.AesOcb.X86_64.wholeR_sub hmn)).trans (Pt.frame.sub (VG.Proof.AesOcb.X86_64.tailR_sub (by omega))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · rw [e, blk, Pt.out]
    by_cases hr : 0 < n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
      simp only [hr, ↓reduceIte, show n % 16 = 0 by omega, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < n % 16
    · simp only [hr, Bool.false_eq_true, ↓reduceIte, Pt.out, pT, cT, lT, Pw.ofs, rest]
    · simp only [hr, ↓reduceIte]

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.CTBase`. -/
section

/-!
# AES-OCB on x86-64: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs piece by piece (`RelCT`). Both runs have the same public
arguments, kept in the slots of `W` (`Slots`), so the taint analysis starts
from the registers that agree, those slots and the words `ex` of `W` that
also agree, public (`ocbT`, `both_agree`); what correctness says about each
run is added with `RelCT.wp`. The calls of `vg_aes_encrypt_blocks` and
`vg_aes_decrypt_blocks` have the same arguments in both runs
(`callBlocks_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm.X86_64 (word_byte add_ofNat_assoc runBlock_append)

/-- The taint: the registers `rs`, `r14`, `r15` and `rsp` public, `r15` the
base of the working space (the second writable region), the slots of the
public arguments `[208, 248)` and `[288, 304)` and the words at `ex` public. -/
def ocbT (rs : List Reg) (ex : List Nat) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.r14, .r15, .rsp]), flags := false, lens := [0, 2560], bases := [(.r15, 1, 0)],
    slots := [(1, 208, 40), (1, 288, 16)] ++ ex.map fun d => (1, d, 8) }

/-- Two runs with the same public arguments: both in the environment, with
the same slots and writable regions, agreeing on the registers `rs` and the
words of `W` at `ex`. -/
structure Both (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (rs : List Reg) (ex : List Nat)
    (s₁ s₂ : State) : Prop where
  e₁ : Env K W SP s₁
  e₂ : Env K W SP s₂
  sl₁ : Slots W R N A D nl n tl s₁.mem
  sl₂ : Slots W R N A D nl n tl s₂.mem
  wr₁ : s₁.wr = [⟨D, n⟩, ⟨W, 2560⟩]
  wr₂ : s₂.wr = [⟨D, n⟩, ⟨W, 2560⟩]
  agree : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r
  ex : ∀ d ∈ ex, d + 8 ≤ 2560 ∧ s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s₂.mem.readW (W + BitVec.ofNat 64 d) 64

theorem both_agree {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {rs : List Reg} {ex : List Nat}
    {s₁ s₂ : State} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (h : VG.Proof.AesOcb.X86_64.Both K W SP R N A D nl n tl rs ex s₁ s₂) : X86_64.Taint.Agree (VG.Proof.AesOcb.X86_64.ocbT rs ex) s₁ s₂ := by
  have wf : ∀ {s : State}, Env K W SP s → s.wr = [⟨D, n⟩, ⟨W, 2560⟩] → X86_64.Taint.Wf (VG.Proof.AesOcb.X86_64.ocbT rs ex) s :=
    fun E hw => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
    · rw [hw]; exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
    · rw [hw]; exact List.pairwise_pair.mpr hDW
    · rw [hw]; intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hn
      · show 2560 ≤ 2 ^ 64; decide
    · simp only [VG.Proof.AesOcb.X86_64.ocbT, List.mem_singleton] at hp; subst hp
      simp only [X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
      rw [E.r15, BitVec.add_zero]
  have hb : ∀ s : State, s.wr = [⟨D, n⟩, ⟨W, 2560⟩] → ∀ k, X86_64.Taint.byteAddr s 1 k = W + BitVec.ofNat 64 k :=
    fun s hw k => by
      simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
  have hw : ∀ {k : Nat} (d : Nat), d ≤ k → W + BitVec.ofNat 64 k = W + BitVec.ofNat 64 d + BitVec.ofNat 64 (k - d) :=
    fun {k} d e => by rw [add_ofNat_assoc, show d + (k - d) = k by omega]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [h.wr₁, h.wr₂], wf h.e₁ h.wr₁, wf h.e₂ h.wr₂,
    fun sl hsl => ?_, fun sl hsl k hk₁ hk₂ => ?_, X86_64.Taint.noLo⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with hr | hr
    · exact h.agree r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.e₁.r14, h.e₂.r14]
      · rw [h.e₁.r15, h.e₂.r15]
      · rw [h.e₁.rsp, h.e₂.rsp]
  · simp only [VG.Proof.AesOcb.X86_64.ocbT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hsl
    rcases hsl with (rfl | rfl) | ⟨d, hd, rfl⟩
    · simp [VG.Proof.AesOcb.X86_64.ocbT]
    · simp [VG.Proof.AesOcb.X86_64.ocbT]
    · simp only [VG.Proof.AesOcb.X86_64.ocbT, List.getD_cons_succ, List.getD_cons_zero]; exact (h.ex d hd).1
  · simp only [VG.Proof.AesOcb.X86_64.ocbT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hsl
    have S₁ := h.sl₁
    have S₂ := h.sl₂
    rcases hsl with (rfl | rfl) | ⟨d, hd, rfl⟩ <;> rw [hb s₁ h.wr₁, hb s₂ h.wr₂]
    · simp only at hk₁ hk₂
      have key : ∀ d, d ∈ [208, 216, 224, 232, 240] → d ≤ k → k < d + 8 →
          s₁.mem (W + BitVec.ofNat 64 k) = s₂.mem (W + BitVec.ofNat 64 k) := fun d hd h₁ h₂ => by
        rw [hw d h₁]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl
        · exact word_byte S₁.data S₂.data (by omega)
        · exact word_byte S₁.len S₂.len (by omega)
        · exact word_byte S₁.tl S₂.tl (by omega)
        · exact word_byte S₁.rounds S₂.rounds (by omega)
        · exact word_byte S₁.aad S₂.aad (by omega)
      have hq : (k - 208) / 8 = 0 ∨ (k - 208) / 8 = 1 ∨ (k - 208) / 8 = 2 ∨ (k - 208) / 8 = 3 ∨
          (k - 208) / 8 = 4 := by omega
      exact key (208 + 8 * ((k - 208) / 8)) (by
        rcases hq with h | h | h | h | h <;> rw [h] <;> decide) (by omega) (by omega)
    · simp only at hk₁ hk₂
      by_cases hk : k < 296
      · rw [hw 288 (by omega)]; exact word_byte S₁.nonce S₂.nonce (by omega)
      · rw [hw 296 (by omega)]; exact word_byte S₁.nlen S₂.nlen (by omega)
    · simp only at hk₁ hk₂
      rw [hw d hk₁]; exact word_byte (h.ex d hd).2 rfl (by omega)

/-- Code the taint analysis checks from `ocbT rs ex`. -/
theorem rel_taintC {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (ex : List Nat) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesOcb.X86_64.Both K W SP R N A D nl n tl rs ex s₁ s₂)
    (hc : ∃ hc, (taint.check (VG.Proof.AesOcb.X86_64.ocbT rs ex) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (VG.Proof.AesOcb.X86_64.ocbT rs ex) (fun s₁ s₂ h => VG.Proof.AesOcb.X86_64.both_agree hDW hn (hP _ _ h)) hc

/-- Code the taint analysis checks from `ocbT rs ex`, leaving the flags public. -/
theorem rel_flagsC {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (ex : List Nat) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesOcb.X86_64.Both K W SP R N A D nl n tl rs ex s₁ s₂)
    (hc : ∃ hc, ((taint.check (VG.Proof.AesOcb.X86_64.ocbT rs ex) c hc).map (·.flags)) = some true) :
    RelCT isa P c fun s₁ s₂ => s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf := by
  obtain ⟨_, h⟩ := hc
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (VG.Proof.AesOcb.X86_64.both_agree hDW hn (hP _ _ hp)) e₁ e₂
  obtain ⟨hcf, hzf, -, -⟩ := ha.rf.2 hs
  exact ⟨ht, hcf, hzf⟩

/-- Runs related from each pair of states. -/
theorem rel_of_pt {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, P σ₁ σ₂ → RelCT isa (fun t₁ t₂ => t₁ = σ₁ ∧ t₂ = σ₂) c Q) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

/-- One run with the public arguments. -/
structure One (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (s : State) : Prop where
  env : Env K W SP s
  sl : Slots W R N A D nl n tl s.mem
  wr : s.wr = [⟨D, n⟩, ⟨W, 2560⟩]

theorem Both.of {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {s₁ s₂ : State}
    (o₁ : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₁) (o₂ : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₂) :
    VG.Proof.AesOcb.X86_64.Both K W SP R N A D nl n tl [] [] s₁ s₂ :=
  ⟨o₁.env, o₂.env, o₁.sl, o₂.sl, o₁.wr, o₂.wr, fun _ h => (nomatch h), fun _ h => (nomatch h)⟩

/-- One run, after a frame within the parts the pieces write. -/
theorem One.step {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} (L : Lay K W SP)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {s s' : State} (o : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s)
    (E : Env K W SP s') (hw : s'.wr = s.wr) (f : Frame (mutR W SP D n) s.mem s'.mem) :
    VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s' :=
  ⟨E, Slots.of_mut L hDW f o.sl, hw.trans o.wr⟩

/-- The data, in a run with the public arguments. -/
theorem DBuf.of_one {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {s s' : State}
    (h : DBuf K W SP s D n) (o : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s') : DBuf K W SP s' D n where
  toBuf := { h.toBuf with rd := Covers.right (by rw [o.wr]; exact Covers.of_mem fun r hr => by simp_all) }
  wr := by rw [o.wr]; exact Covers.of_mem fun r hr => by simp_all
  k := h.k

/-- A call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on the same
`n` blocks at `D'` in both runs. -/
theorem callBlocks_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86_64 f).pre (Proof.Aes.blocksX86_64 f).pub b.code)
    {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D : Addr} {nl n tl : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64) {args : List Instr} (rs : List Reg)
    (ex : List Nat)
    (hc : ∃ hc, (taint.check (VG.Proof.AesOcb.X86_64.ocbT rs ex)
      (.block (args ++ [mvr .rdi .r14, VG.Impl.AesOcb.X86_64.ld .rsi .r15 rndO, mvr .r8 .r15, addi .r8 scrO])) hc).isSome = true)
    {D' : Addr} {k : Nat} {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesOcb.X86_64.Both K W SP R N A D nl n tl rs ex s₁ s₂ ∧ ArgsOk args s₁ D' k ∧ ArgsOk args s₂ D' k ∧
      Dst K W SP s₁ D' k ∧ Dst K W SP s₂ D' k) :
    RelCT isa P (callBlocks b args) fun _ _ => True := by
  unfold callBlocks
  have a := (VG.Proof.AesOcb.X86_64.rel_taintC rs ex hDW hn (fun s₁ s₂ h => (hP s₁ s₂ h).1) hc).wp
    (F₁ := fun (s : State) => BCall s K D' (W + BitVec.ofNat 64 512) R k ∧ s.gpr .rsp = SP)
    (F₂ := fun (s : State) => BCall s K D' (W + BitVec.ofNat 64 512) R k ∧ s.gpr .rsp = SP) fun s₁ s₂ h => by
      obtain ⟨B, a₁, a₂, d₁, d₂⟩ := hP s₁ s₂ h
      exact ⟨WP.mono (callArgs_ok L B.e₁ hR B.sl₁.rounds a₁ d₁) fun _ q => ⟨q.1, q.2.1⟩,
        WP.mono (callArgs_ok L B.e₂ hR B.sl₂.rounds a₂ d₂) fun _ q => ⟨q.1, q.2.1⟩⟩
  exact RelCT.seq a (blk_rel ok ct fun s₁ s₂ h => ⟨K, D', _, R, k, h.2.1.1, h.2.2.1, h.2.1.2.trans h.2.2.2.symm⟩)

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.WholeCT`. -/
section

/-!
# AES-OCB on x86-64: the whole blocks are constant time

Untrusted: everything here is checked by Lean. Each pass passes the taint
analysis from the public slots and the number of blocks in `r13`
(`rel_taintC`); the call of `vg_aes_encrypt_blocks` or
`vg_aes_decrypt_blocks` between them has the same arguments in both runs
(`callBlocks_rel`). A pass keeps the public arguments, whatever the offsets
and the checksum (`pass_one`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Ocb (Block blockAtMem lAt)
open VG.Proof.Ocb (offAt)
open VG.Proof.AesCcm.X86_64 (runBlock_append)

/-- The checksums of a pass, from `c₀`. -/
def ckRec (c₀ : Block) (f : Nat → Block → Block) : Nat → Block
  | 0 => c₀
  | i + 1 => f i (VG.Proof.AesOcb.X86_64.ckRec c₀ f i)

/-- A pass keeps the public arguments and the registers it does not use. -/
theorem pass_one {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl n tl m : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hmn : 16 * m ≤ n) {body : List Instr}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} (hB : VG.Proof.AesOcb.X86_64.BodyOk W body fB fC)
    {t : State} (o : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl t) (hD : DBuf K W SP t D (16 * m)) (hm0 : 0 < m) (hm : m < 2 ^ 60)
    {l : Block} (hl0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hbx : t.gpr .rbx = D) (hbp : t.gpr .rbp = BitVec.ofNat 64 1) (h12 : t.gpr .r12 = BitVec.ofNat 64 m) :
    WP isa (pass body) t fun t' => VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl t' ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 l0O) = lAt l 0 ∧
      ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r11 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 →
        t'.gpr r = t.gpr r := by
  let O0 := blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)
  let X := fun k => blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k))
  let ckF := VG.Proof.AesOcb.X86_64.ckRec (blockAtMem t.mem (W + BitVec.ofNat 64 ckO)) fun i c => fC c (X i) (offAt O0 l (i + 1))
  have P₀ : VG.Proof.AesOcb.X86_64.PassInv K W SP D m O0 l X fB ckF t t 0 :=
    { env := o.env, frame := Frame.refl _ _, rd := rfl, wr := rfl
      rbx := by rw [hbx]; simp
      rbp := hbp
      r12 := by rw [h12, Nat.sub_zero]
      ofs := rfl
      ck := rfl
      blk := fun k _ => by simp [X]
      l0 := hl0
      gpr := fun _ _ _ _ _ _ _ _ _ => rfl }
  refine WP.mono (VG.Proof.AesOcb.X86_64.pass_ok L hB (ckF := ckF) (fun i _ => rfl) hD hm0 hm P₀) fun t' P => ⟨?_, P.l0, P.gpr⟩
  refine o.step L hDW P.env P.wr (P.frame.sub fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩
  · exact ⟨_, by simp, Region.sub_prefix hmn⟩

/-- What the whole blocks need of a run, and what their first pass keeps:
the public arguments, the number of blocks in `r13`, `L_0` and the data. -/
def WRun (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl m : Nat) (s : State) : Prop :=
  VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s ∧ s.gpr .r13 = BitVec.ofNat 64 m ∧
    (∃ l, blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) ∧ DBuf K W SP s D n

/-- The first pass. -/
theorem wholeA_one {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl n tl m : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hmn : 16 * m ≤ n) (hm0 : 0 < m) (hm : m < 2 ^ 60)
    {body : List Instr} {fB : Block → Block → Block} {fC : Block → Block → Block → Block}
    (hB : VG.Proof.AesOcb.X86_64.BodyOk W body fB fC) {s : State} (h : VG.Proof.AesOcb.X86_64.WRun K W SP R N A D nl n tl m s) :
    WP isa (.seq (.block [VG.Impl.AesOcb.X86_64.ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)]) (pass body)) s
      (VG.Proof.AesOcb.X86_64.WRun K W SP R N A D nl n tl m) := by
  obtain ⟨o, h13, ⟨l, hl0⟩, hD⟩ := h
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 208) 8 := o.env.perm.wR (by decide)
  have hdata := o.sl.data
  obtain ⟨s₁, run₁, rbx₁, r12₁, rbp₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [VG.Impl.AesOcb.X86_64.ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)] s = some s₁ ∧
      s₁.gpr .rbx = D ∧ s₁.gpr .r12 = BitVec.ofNat 64 m ∧ s₁.gpr .rbp = BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .rbp → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by orun [o.env.r15, r₁, hdata], ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h13]
    · simp only [gpr_setReg, ite_true, sext1]
    · simp only [gpr_setReg, h1, h2, h3, ite_false]
    all_goals rfl
  have E₁ : Env K W SP s₁ := o.env.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₁ wr₁
  have o₁ : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₁ := ⟨E₁, by rw [m₁]; exact o.sl, by rw [wr₁]; exact o.wr⟩
  have hD₁ : DBuf K W SP s₁ D n := hD.of_eq rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (VG.Proof.AesOcb.X86_64.pass_one L hDW hmn hB o₁ (hD₁.take' hmn) hm0 hm (l := l) (by rw [m₁]; exact hl0) rbx₁ rbp₁ r12₁)
    fun t ⟨o', hl', g'⟩ => ⟨o', ?_, ⟨l, hl'⟩, hD₁.of_one o'⟩
  rw [g' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    g₁ _ (by decide) (by decide) (by decide), h13]

/-- Both runs with the number of blocks in `r13`. -/
theorem both_r13 {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl m : Nat} {s₁ s₂ : State}
    (o₁ : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₁) (o₂ : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₂)
    (h₁ : s₁.gpr .r13 = BitVec.ofNat 64 m) (h₂ : s₂.gpr .r13 = BitVec.ofNat 64 m) :
    VG.Proof.AesOcb.X86_64.Both K W SP R N A D nl n tl [.r13] [] s₁ s₂ :=
  ⟨o₁.env, o₂.env, o₁.sl, o₂.sl, o₁.wr, o₂.wr, fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂], fun _ h => (nomatch h)⟩

/-- `whole f pre post` in two runs. -/
theorem whole_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86_64 f).pre (Proof.Aes.blocksX86_64 f).pub b.code)
    (nosp : NoSp b.code) (depth : b.code.depth = 0)
    {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D : Addr} {nl n tl m : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64) (hmn : 16 * m ≤ n) (hm0 : 0 < m)
    (hm : m < 2 ^ 60) {pre post : List Instr} {fB : Block → Block → Block} {fC : Block → Block → Block → Block}
    (hB : VG.Proof.AesOcb.X86_64.BodyOk W pre fB fC)
    (hc₁ : ∃ hc, (taint.check (VG.Proof.AesOcb.X86_64.ocbT [.r13] [])
      (.seq (.block [VG.Impl.AesOcb.X86_64.ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)]) (pass pre)) hc).isSome = true)
    (hc₂ : ∃ hc, (taint.check (VG.Proof.AesOcb.X86_64.ocbT [.r13] [])
      (.seq (.block (copy16 o0O ofsO ++ [VG.Impl.AesOcb.X86_64.ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)])) (pass post)) hc).isSome
        = true)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesOcb.X86_64.WRun K W SP R N A D nl n tl m s₁ ∧ VG.Proof.AesOcb.X86_64.WRun K W SP R N A D nl n tl m s₂) :
    RelCT isa P (whole b pre post) fun _ _ => True := by
  unfold whole
  have a := (VG.Proof.AesOcb.X86_64.rel_taintC [.r13] [] hDW hn (fun s₁ s₂ h => VG.Proof.AesOcb.X86_64.both_r13 (hP s₁ s₂ h).1.1 (hP s₁ s₂ h).2.1
    (hP s₁ s₂ h).1.2.1 (hP s₁ s₂ h).2.2.1) hc₁).wp
    (F₁ := VG.Proof.AesOcb.X86_64.WRun K W SP R N A D nl n tl m) (F₂ := VG.Proof.AesOcb.X86_64.WRun K W SP R N A D nl n tl m)
    fun s₁ s₂ h => ⟨VG.Proof.AesOcb.X86_64.wholeA_one L hDW hmn hm0 hm hB (hP s₁ s₂ h).1, VG.Proof.AesOcb.X86_64.wholeA_one L hDW hmn hm0 hm hB (hP s₁ s₂ h).2⟩
  have args : ∀ {s : State}, VG.Proof.AesOcb.X86_64.WRun K W SP R N A D nl n tl m s → ArgsOk [VG.Impl.AesOcb.X86_64.ld .rdx .r15 dataO, mvr .rcx .r13] s D m :=
    fun h => VG.Proof.AesOcb.X86_64.dataArgs_ok h.1.env.r15 h.1.sl.data h.2.1 (h.1.env.perm.wR (by decide))
  have call : ∀ s, VG.Proof.AesOcb.X86_64.WRun K W SP R N A D nl n tl m s →
      WP isa (callBlocks b [VG.Impl.AesOcb.X86_64.ld .rdx .r15 dataO, mvr .rcx .r13]) s fun s' =>
        VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s' ∧ s'.gpr .r13 = BitVec.ofNat 64 m := fun s h =>
    WP.mono (callBlocks_ok ok nosp depth L h.1.env hR h.1.sl.rounds (args h) (dstD (h.2.2.2.take' hmn)))
      fun s' Q => by
      refine ⟨h.1.step L hDW (h.1.env.of_saved Q.saved Q.rd Q.wr) Q.wr (Q.frame.sub fun r hr => ?_),
        by rw [Q.saved _ (by decide), h.2.1]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, Region.sub_prefix hmn⟩
      · exact ⟨_, by simp, VG.Proof.AesOcb.X86_64.sub_wC (by decide) (by decide)⟩
      · rw [h.1.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩
  have bb := (VG.Proof.AesOcb.X86_64.callBlocks_rel ok ct L hR hDW hn [.r13] [] (args := [VG.Impl.AesOcb.X86_64.ld .rdx .r15 dataO, mvr .rcx .r13])
    ⟨_, by taint_decide⟩ (D' := D) (k := m)
    (P := fun s₁ s₂ => True ∧ VG.Proof.AesOcb.X86_64.WRun K W SP R N A D nl n tl m s₁ ∧ VG.Proof.AesOcb.X86_64.WRun K W SP R N A D nl n tl m s₂) fun s₁ s₂ h =>
      ⟨VG.Proof.AesOcb.X86_64.both_r13 h.2.1.1 h.2.2.1 h.2.1.2.1 h.2.2.2.1, args h.2.1, args h.2.2, dstD (h.2.1.2.2.2.take' hmn),
        dstD (h.2.2.2.2.2.take' hmn)⟩).wp
    (F₁ := fun (s : State) => VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s ∧ s.gpr .r13 = BitVec.ofNat 64 m)
    (F₂ := fun (s : State) => VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s ∧ s.gpr .r13 = BitVec.ofNat 64 m)
    fun s₁ s₂ h => ⟨call s₁ h.2.1, call s₂ h.2.2⟩
  have c := VG.Proof.AesOcb.X86_64.rel_taintC [.r13] [] hDW hn (fun s₁ s₂ (h : True ∧ (VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₁ ∧
      s₁.gpr .r13 = BitVec.ofNat 64 m) ∧ (VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₂ ∧ s₂.gpr .r13 = BitVec.ofNat 64 m)) =>
    VG.Proof.AesOcb.X86_64.both_r13 h.2.1.1 h.2.2.1 h.2.1.2 h.2.2.2) hc₂
  exact Proof.AesCcm.X86_64.rel_assoc (RelCT.seq a (RelCT.seq bb c))

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.TagCT`. -/
section

/-!
# AES-OCB on x86-64: the tag is constant time

Untrusted: everything here is checked by Lean. The blocks before and after
the call pass the taint analysis from the public slots (`rel_taintC`); the
call of `vg_aes_encrypt_blocks` has the same arguments in both runs
(`callBlocks_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append)

/-- A call of `vg_aes_encrypt_blocks` on the block at `W + tmpO` keeps the
public arguments. -/
theorem callTmp_one (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {s : State}
    (o : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s) :
    WP isa (callBlocks (VG.Proof.AesOcb.X86_64.callees v).enc (oneBlock tmpO)) s (VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl) :=
  WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encDepth L o.env hR o.sl.rounds
    (oneBlock_ok o.env.r15 tmpO (by decide)) (dstW L o.env.perm (d := tmpO) (n := 1) (by decide))) fun s' Q => by
    have E' := o.env.of_saved Q.saved Q.rd Q.wr
    refine o.step L hDW E' Q.wr (Q.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩
    · exact ⟨_, by simp, VG.Proof.AesOcb.X86_64.sub_wC (by decide) (by decide)⟩
    · rw [o.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩

/-- The call on the block at `W + tmpO`, in two runs. -/
theorem callTmp_rel (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₁ ∧ VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₂) :
    RelCT isa P (callBlocks (VG.Proof.AesOcb.X86_64.callees v).enc (oneBlock tmpO)) fun s₁ s₂ =>
      VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₁ ∧ VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₂ :=
  ((VG.Proof.AesOcb.X86_64.callBlocks_rel (b := (VG.Proof.AesOcb.X86_64.callees v).enc) v.encOk v.encCt L hR hDW hn [] [] (args := oneBlock tmpO)
    ⟨_, by taint_decide⟩ (D' := W + BitVec.ofNat 64 tmpO) (k := 1) fun s₁ s₂ h =>
      ⟨Both.of (hP s₁ s₂ h).1 (hP s₁ s₂ h).2, oneBlock_ok (hP s₁ s₂ h).1.env.r15 tmpO (by decide),
        oneBlock_ok (hP s₁ s₂ h).2.env.r15 tmpO (by decide), dstW L (hP s₁ s₂ h).1.env.perm (by decide),
        dstW L (hP s₁ s₂ h).2.env.perm (by decide)⟩).wp
    (F₁ := VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl) (F₂ := VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl)
    fun s₁ s₂ h => ⟨VG.Proof.AesOcb.X86_64.callTmp_one v L hR hDW (hP s₁ s₂ h).1, VG.Proof.AesOcb.X86_64.callTmp_one v L hR hDW (hP s₁ s₂ h).2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-- The checksum, the offset and `L_$` at `W + tmpO`. -/
theorem tagHead_one {K W SP : Addr} (L : Lay K W SP) {N A D : Addr} {R nl n tl : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {s : State} (o : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s) :
    WP isa (.block (copy16 ckO tmpO ++ xor16 .r15 ofsO tmpO ++ xor16 .r15 ldO tmpO)) s
      (VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl) := by
  have E := o.env
  obtain ⟨t₁, run₁, B₁⟩ := copy16_ok (s := s) (a := ckO) (d := tmpO) E.r15
    (E.perm.wR (by decide)) (E.perm.wR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have nE : ∀ r ∈ [Reg.r14, .r15, .rsp], r ∉ [Reg.rax, .rdx] := by decide
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => B₁.gpr r (nE r hr)) B₁.rd B₁.wr
  obtain ⟨t₂, run₂, B₂⟩ := xor16_ok (s := t₁) (b := .r15) (a := ofsO) (d := tmpO) E₁.r15 E₁.r15 (by decide) (by decide)
    (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide)) (E₁.perm.wW (by decide)) (E₁.perm.wW (by decide))
  have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => B₂.gpr r (nE r hr)) B₂.rd B₂.wr
  obtain ⟨t₃, run₃, B₃⟩ := xor16_ok (s := t₂) (b := .r15) (a := ldO) (d := tmpO) E₂.r15 E₂.r15 (by decide) (by decide)
    (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide)) (E₂.perm.wW (by decide)) (E₂.perm.wW (by decide))
  have E₃ : Env K W SP t₃ := E₂.keep (fun r hr => B₃.gpr r (nE r hr)) B₃.rd B₃.wr
  refine WP.of_runBlock ⟨t₃, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, VG.Proof.AesCcm.X86_64.runBlock_append, run₁, Option.bind_some, run₂,
    Option.bind_some, run₃], o.step L hDW E₃ (by rw [B₃.wr, B₂.wr, B₁.wr])
      (((B₁.frame.trans B₂.frame).trans B₃.frame).sub fun r hr => ?_)⟩
  simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩

/-- `tag d` in two runs. -/
theorem tag_rel (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    {d : Nat} (hd : d = tagO ∨ d = t2O) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₁ ∧ VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₂) :
    RelCT isa P (tag (VG.Proof.AesOcb.X86_64.callees v) d) fun _ _ => True := by
  have a := (VG.Proof.AesOcb.X86_64.rel_taintC [] [] hDW hn (fun s₁ s₂ h => Both.of (hP s₁ s₂ h).1 (hP s₁ s₂ h).2)
    (c := .block (copy16 ckO tmpO ++ xor16 .r15 ofsO tmpO ++ xor16 .r15 ldO tmpO)) ⟨_, by taint_decide⟩).wp
    (F₁ := VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl) (F₂ := VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl)
    fun s₁ s₂ h => ⟨VG.Proof.AesOcb.X86_64.tagHead_one L hDW (hP s₁ s₂ h).1, VG.Proof.AesOcb.X86_64.tagHead_one L hDW (hP s₁ s₂ h).2⟩
  have b := VG.Proof.AesOcb.X86_64.callTmp_rel v L hR hDW hn (P := fun s₁ s₂ => True ∧ VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₁ ∧
    VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₂) fun _ _ h => h.2
  have c := VG.Proof.AesOcb.X86_64.rel_taintC [] [] hDW hn (fun s₁ s₂ (h : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₁ ∧ VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₂) =>
    Both.of h.1 h.2) (c := .block (copy16 tmpO d ++ xor16 .r15 sumO d))
    (by rcases hd with rfl | rfl <;> exact ⟨_, by taint_decide⟩)
  exact RelCT.seq a (RelCT.seq b c)

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.RestCT`. -/
section

/-!
# AES-OCB on x86-64: the rest of the data is constant time

Untrusted: everything here is checked by Lean. The code around the call
passes the taint analysis from the public slots and the address and length
of the rest in `rbx` and `r12` (`rel_taintC`); the call of
`vg_aes_encrypt_blocks` has the same arguments in both runs (`callTmp_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append)

/-- A run before the rest: the public arguments, its address and length. -/
def RRun (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (P : Addr) (r : Nat) (s : State) : Prop :=
  VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s ∧ s.gpr .rbx = P ∧ s.gpr .r12 = BitVec.ofNat 64 r

theorem both_rr {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {P : Addr} {r : Nat} {s₁ s₂ : State}
    (h₁ : VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl P r s₁) (h₂ : VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl P r s₂) :
    VG.Proof.AesOcb.X86_64.Both K W SP R N A D nl n tl [.rbx, .r12] [] s₁ s₂ :=
  ⟨h₁.1.env, h₂.1.env, h₁.1.sl, h₂.1.sl, h₁.1.wr, h₂.1.wr, fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2], fun _ h => (nomatch h)⟩

/-- `Offset_*` and a copy of it at `W + tmpO`. -/
theorem restHead1_one {K W SP : Addr} (L : Lay K W SP) {N A D : Addr} {R nl n tl : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {P : Addr} {r : Nat} {s : State}
    (h : VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl P r s) :
    WP isa (.block (xor16 .r14 240 ofsO ++ copy16 ofsO tmpO)) s (VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl P r) := by
  have E := h.1.env
  obtain ⟨t₁, run₁, B₁⟩ := xor16_ok (s := s) (b := .r14) (a := 240) (d := ofsO) E.r15 E.r14 (by decide) (by decide)
    (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have nE : ∀ r ∈ [Reg.r14, .r15, .rsp], r ∉ [Reg.rax, .rdx] := by decide
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => B₁.gpr r (nE r hr)) B₁.rd B₁.wr
  obtain ⟨t₂, run₂, B₂⟩ := copy16_ok (s := t₁) (a := ofsO) (d := tmpO) E₁.r15
    (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide)) (E₁.perm.wW (by decide)) (E₁.perm.wW (by decide))
  have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => B₂.gpr r (nE r hr)) B₂.rd B₂.wr
  refine WP.of_runBlock ⟨t₂, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₁, Option.bind_some, run₂],
    h.1.step L hDW E₂ (by rw [B₂.wr, B₁.wr]) (((B₁.frame.sub fun r hr => ?_).trans (B₂.frame.sub fun r hr => ?_))),
    by rw [B₂.gpr _ (by decide), B₁.gpr _ (by decide), h.2.1], by rw [B₂.gpr _ (by decide), B₁.gpr _ (by decide), h.2.2]⟩
  all_goals simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩

/-- The call on the block at `W + tmpO` keeps the callee-saved registers. -/
theorem callTmp_rr (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {P : Addr} {r : Nat} {s : State}
    (h : VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl P r s) :
    WP isa (callBlocks (VG.Proof.AesOcb.X86_64.callees v).enc (oneBlock tmpO)) s (VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl P r) :=
  WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encDepth L h.1.env hR h.1.sl.rounds
    (oneBlock_ok h.1.env.r15 tmpO (by decide)) (dstW L h.1.env.perm (d := tmpO) (n := 1) (by decide))) fun s' Q => by
    have E' := h.1.env.of_saved Q.saved Q.rd Q.wr
    refine ⟨h.1.step L hDW E' Q.wr (Q.frame.sub fun r hr => ?_), by rw [Q.saved _ (by decide), h.2.1],
      by rw [Q.saved _ (by decide), h.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩
    · exact ⟨_, by simp, VG.Proof.AesOcb.X86_64.sub_wC (by decide) (by decide)⟩
    · rw [h.1.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩

/-- `rest enc` in two runs. -/
theorem rest_rel (v : BlocksImpl) (enc : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hn : n ≤ 2 ^ 64) {P : Addr} {r : Nat} {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl P r s₁ ∧ VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl P r s₂) :
    RelCT isa Q (VG.Impl.AesOcb.X86_64.rest (VG.Proof.AesOcb.X86_64.callees v) enc) fun _ _ => True := by
  unfold VG.Impl.AesOcb.X86_64.rest
  have a := (VG.Proof.AesOcb.X86_64.rel_taintC [.rbx, .r12] [] hDW hn (fun s₁ s₂ h => VG.Proof.AesOcb.X86_64.both_rr (hQ s₁ s₂ h).1 (hQ s₁ s₂ h).2)
    (c := .block (xor16 .r14 240 ofsO ++ copy16 ofsO tmpO)) ⟨_, by taint_decide⟩).wp
    (F₁ := VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl P r) (F₂ := VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl P r)
    fun s₁ s₂ h => ⟨VG.Proof.AesOcb.X86_64.restHead1_one L hDW (hQ s₁ s₂ h).1, VG.Proof.AesOcb.X86_64.restHead1_one L hDW (hQ s₁ s₂ h).2⟩
  have b := ((VG.Proof.AesOcb.X86_64.callTmp_rel v L hR hDW hn (P := fun s₁ s₂ => True ∧ VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl P r s₁ ∧
    VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl P r s₂) fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩).wp
    (F₁ := VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl P r) (F₂ := VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl P r)
    fun s₁ s₂ h => ⟨VG.Proof.AesOcb.X86_64.callTmp_rr v L hR hDW h.2.1, VG.Proof.AesOcb.X86_64.callTmp_rr v L hR hDW h.2.2⟩)
  have c := VG.Proof.AesOcb.X86_64.rel_taintC [.rbx, .r12] [] hDW hn (fun s₁ s₂ (h : (VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₁ ∧
      VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₂) ∧ VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl P r s₁ ∧ VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl P r s₂) =>
    VG.Proof.AesOcb.X86_64.both_rr h.2.1 h.2.2) (c := if enc then .seq padCk xorPad else .seq xorPad padCk)
    (by cases enc <;> exact ⟨_, by taint_decide⟩)
  exact RelCT.seq a (RelCT.seq b c)

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.BodyCT`. -/
section

/-!
# AES-OCB on x86-64: the data is constant time

Untrusted: everything here is checked by Lean. The number of whole blocks
and the length of the rest come from the public slots, so the branches agree
in both runs (`rel_flagsC`); the whole blocks and the rest are related by
`whole_rel` and `rest_rel`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (eval_e)

/-- What `body` needs of a run: the public arguments, the data, `L_0`, and
the offset equal to `Offset_0`. -/
def BRun (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (s : State) : Prop :=
  VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s ∧ DBuf K W SP s D n ∧ (∃ l, blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) ∧
    blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = blockAtMem s.mem (W + BitVec.ofNat 64 o0O)

/-- The whole blocks, if any, keep the public arguments. -/
theorem wholeIte_one {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp b.code) (depth : b.code.depth = 0) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block}
    (hB1 : ∀ {W}, VG.Proof.AesOcb.X86_64.BodyOk W pre (fun b o => b ^^^ o) fC1) (hB2 : ∀ {W}, VG.Proof.AesOcb.X86_64.BodyOk W post (fun b o => b ^^^ o) fC2)
    {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D : Addr} {nl n tl : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {s : State} (h : VG.Proof.AesOcb.X86_64.BRun K W SP R N A D nl n tl s) :
    WP isa (.seq (.block [VG.Impl.AesOcb.X86_64.ld .r13 .r15 lenO, .shift .shr .r13 4, .alu .test .r13 (.reg .r13)])
        (.ite .e (.block []) (whole b pre post))) s (VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl) := by
  obtain ⟨o, hD, ⟨l, hl0⟩, ho⟩ := h
  let O0 := blockAtMem s.mem (W + BitVec.ofNat 64 ofsO)
  let ckF1 := VG.Proof.AesOcb.X86_64.ckRec (blockAtMem s.mem (W + BitVec.ofNat 64 ckO))
    fun i c => fC1 c (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1))
  let ckF2 := VG.Proof.AesOcb.X86_64.ckRec (ckF1 (n / 16)) fun i c => fC2 c
    (G (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
    (offAt O0 l (i + 1))
  refine WP.mono (VG.Proof.AesOcb.X86_64.wholeIte_ok (O0 := O0) (l := l) (ckF1 := ckF1) (ckF2 := ckF2) ok nosp depth hcall hB1 hB2 L o.env hR
    hD o.sl.data o.sl.len o.sl.rounds rfl ho.symm rfl hl0 (fun _ => rfl) rfl (fun _ => rfl)) fun t P =>
    o.step L hDW P.env P.wr (VG.Proof.AesOcb.X86_64.bodyR_mut (P.frame.sub (VG.Proof.AesOcb.X86_64.wholeR_sub (Nat.mul_div_le n 16))))

/-- `body`, for its whole blocks `whole b pre post` and its rest `rest enc`, in two runs. -/
theorem body_rel' (v : BlocksImpl) (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86_64 f).pre (Proof.Aes.blocksX86_64 f).pub b.code)
    (nosp : NoSp b.code) (depth : b.code.depth = 0) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block}
    (hB1 : ∀ {W}, VG.Proof.AesOcb.X86_64.BodyOk W pre (fun b o => b ^^^ o) fC1) (hB2 : ∀ {W}, VG.Proof.AesOcb.X86_64.BodyOk W post (fun b o => b ^^^ o) fC2)
    (hc₁ : ∃ hc, (taint.check (VG.Proof.AesOcb.X86_64.ocbT [.r13] [])
      (.seq (.block [VG.Impl.AesOcb.X86_64.ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)]) (pass pre)) hc).isSome = true)
    (hc₂ : ∃ hc, (taint.check (VG.Proof.AesOcb.X86_64.ocbT [.r13] [])
      (.seq (.block (copy16 o0O ofsO ++ [VG.Impl.AesOcb.X86_64.ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)])) (pass post)) hc).isSome
        = true)
    {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D : Addr} {nl n tl : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n < 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesOcb.X86_64.BRun K W SP R N A D nl n tl s₁ ∧ VG.Proof.AesOcb.X86_64.BRun K W SP R N A D nl n tl s₂) :
    RelCT isa P (.seq (.block [VG.Impl.AesOcb.X86_64.ld .r13 .r15 lenO, .shift .shr .r13 4, .alu .test .r13 (.reg .r13)])
      (.seq (.ite .e (.block []) (whole b pre post))
        (.seq (.block [VG.Impl.AesOcb.X86_64.ld .rbx .r15 dataO, VG.Impl.AesOcb.X86_64.ld .rax .r15 lenO, mvr .r12 .rax, .alu .and .r12 (.imm 15),
            .alu .sub .rax (.reg .r12), .alu .add .rbx (.reg .rax), .alu .test .r12 (.reg .r12)])
          (.ite .e (.block []) (VG.Impl.AesOcb.X86_64.rest (VG.Proof.AesOcb.X86_64.callees v) enc))))) fun _ _ => True := by
  have hn' : n ≤ 2 ^ 64 := Nat.le_of_lt hn
  let m := n / 16
  -- The number of whole blocks.
  have head : ∀ s, VG.Proof.AesOcb.X86_64.BRun K W SP R N A D nl n tl s →
      WP isa (.block [VG.Impl.AesOcb.X86_64.ld .r13 .r15 lenO, .shift .shr .r13 4, .alu .test .r13 (.reg .r13)]) s fun s₁ =>
        VG.Proof.AesOcb.X86_64.WRun K W SP R N A D nl n tl m s₁ ∧ s₁.zf = some (decide (m = 0)) := fun s ⟨o, hD, ⟨l, hl0⟩, _⟩ => by
    obtain ⟨s₁, run₁, r13₁, zf₁, m₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86_64.bodyHead_ok o.env hn o.sl.len
    have E₁ : Env K W SP s₁ := o.env.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
      rd₁ wr₁
    have o₁ : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₁ := ⟨E₁, by rw [m₁]; exact o.sl, by rw [wr₁]; exact o.wr⟩
    exact WP.of_runBlock ⟨s₁, run₁, ⟨o₁, r13₁, ⟨l, by rw [m₁]; exact hl0⟩, hD.of_one o₁⟩, zf₁⟩
  have a := (VG.Proof.AesOcb.X86_64.rel_flagsC [] [] hDW hn' (fun s₁ s₂ h => Both.of (hP s₁ s₂ h).1.1 (hP s₁ s₂ h).2.1)
    (c := .block [VG.Impl.AesOcb.X86_64.ld .r13 .r15 lenO, .shift .shr .r13 4, .alu .test .r13 (.reg .r13)]) ⟨_, by taint_decide⟩).wp
    (F₁ := fun (s : State) => VG.Proof.AesOcb.X86_64.WRun K W SP R N A D nl n tl m s ∧ s.zf = some (decide (m = 0)))
    (F₂ := fun (s : State) => VG.Proof.AesOcb.X86_64.WRun K W SP R N A D nl n tl m s ∧ s.zf = some (decide (m = 0)))
    fun s₁ s₂ h => ⟨head s₁ (hP s₁ s₂ h).1, head s₂ (hP s₁ s₂ h).2⟩
  have i₁ := RelCT.ite (M := isa) (c := .e) (t := .block []) (e := whole b pre post) (Q := fun _ _ => True)
    (P := fun s₁ s₂ => (s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf) ∧
      (VG.Proof.AesOcb.X86_64.WRun K W SP R N A D nl n tl m s₁ ∧ s₁.zf = some (decide (m = 0))) ∧
      (VG.Proof.AesOcb.X86_64.WRun K W SP R N A D nl n tl m s₂ ∧ s₂.zf = some (decide (m = 0))))
    (fun s₁ s₂ h => Proof.AesCcm.X86_64.eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) (by
      by_cases hm : m = 0
      · refine RelCT.of_false fun s₁ s₂ h => ?_
        have := (eval_e h.1.2.1.2).symm.trans h.2
        simp [hm] at this
      · exact VG.Proof.AesOcb.X86_64.whole_rel ok ct nosp depth L hR hDW hn' (Nat.mul_div_le n 16) (Nat.pos_of_ne_zero hm) (by omega) hB1
          hc₁ hc₂ fun s₁ s₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩)
  have x := (RelCT.seq a i₁).wp (F₁ := VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl) (F₂ := VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl)
    fun s₁ s₂ h => ⟨VG.Proof.AesOcb.X86_64.wholeIte_one ok nosp depth hcall hB1 hB2 L hR hDW (hP s₁ s₂ h).1,
      VG.Proof.AesOcb.X86_64.wholeIte_one ok nosp depth hcall hB1 hB2 L hR hDW (hP s₁ s₂ h).2⟩
  -- The rest.
  let Pr := D + BitVec.ofNat 64 (16 * (n / 16))
  have tail : ∀ s, VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s →
      WP isa (.block [VG.Impl.AesOcb.X86_64.ld .rbx .r15 dataO, VG.Impl.AesOcb.X86_64.ld .rax .r15 lenO, mvr .r12 .rax, .alu .and .r12 (.imm 15),
          .alu .sub .rax (.reg .r12), .alu .add .rbx (.reg .rax), .alu .test .r12 (.reg .r12)]) s fun t =>
        VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl Pr (n % 16) t ∧ t.zf = some (decide (n % 16 = 0)) := fun s o => by
    obtain ⟨t₁, run₁, rbx₁, r12₁, zf₁, m₁, g₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86_64.bodyTail_ok o.env hn o.sl.data o.sl.len
    have E₁ : Env K W SP t₁ := o.env.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
      rd₁ wr₁
    exact WP.of_runBlock ⟨t₁, run₁, ⟨⟨E₁, by rw [m₁]; exact o.sl, by rw [wr₁]; exact o.wr⟩, rbx₁, r12₁⟩, zf₁⟩
  have y₁ := (VG.Proof.AesOcb.X86_64.rel_flagsC [] [] hDW hn' (fun s₁ s₂ (h : True ∧ VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₁ ∧
      VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₂) => Both.of h.2.1 h.2.2)
    (c := .block [VG.Impl.AesOcb.X86_64.ld .rbx .r15 dataO, VG.Impl.AesOcb.X86_64.ld .rax .r15 lenO, mvr .r12 .rax, .alu .and .r12 (.imm 15),
      .alu .sub .rax (.reg .r12), .alu .add .rbx (.reg .rax), .alu .test .r12 (.reg .r12)]) ⟨_, by taint_decide⟩).wp
    (F₁ := fun (t : State) => VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl Pr (n % 16) t ∧ t.zf = some (decide (n % 16 = 0)))
    (F₂ := fun (t : State) => VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl Pr (n % 16) t ∧ t.zf = some (decide (n % 16 = 0)))
    fun s₁ s₂ h => ⟨tail s₁ h.2.1, tail s₂ h.2.2⟩
  have i₂ := RelCT.ite (M := isa) (c := .e) (t := .block []) (e := VG.Impl.AesOcb.X86_64.rest (VG.Proof.AesOcb.X86_64.callees v) enc) (Q := fun _ _ => True)
    (P := fun s₁ s₂ => (s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf) ∧
      (VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl Pr (n % 16) s₁ ∧ s₁.zf = some (decide (n % 16 = 0))) ∧
      (VG.Proof.AesOcb.X86_64.RRun K W SP R N A D nl n tl Pr (n % 16) s₂ ∧ s₂.zf = some (decide (n % 16 = 0))))
    (fun s₁ s₂ h => Proof.AesCcm.X86_64.eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) (by
      by_cases hr : n % 16 = 0
      · refine RelCT.of_false fun s₁ s₂ h => ?_
        have := (eval_e h.1.2.1.2).symm.trans h.2
        simp [hr] at this
      · exact VG.Proof.AesOcb.X86_64.rest_rel v enc L hR hDW hn' fun s₁ s₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩)
  exact Proof.AesCcm.X86_64.rel_assoc (RelCT.seq x (RelCT.seq y₁ i₂))

/-- `body` for `seal`, in two runs. -/
theorem bodySeal_rel (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n < 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesOcb.X86_64.BRun K W SP R N A D nl n tl s₁ ∧ VG.Proof.AesOcb.X86_64.BRun K W SP R N A D nl n tl s₂) :
    RelCT isa P (VG.Impl.AesOcb.X86_64.body (VG.Proof.AesOcb.X86_64.callees v) true) fun _ _ => True := by
  simp only [VG.Impl.AesOcb.X86_64.body, ↓reduceIte]
  exact VG.Proof.AesOcb.X86_64.body_rel' v true v.encOk v.encCt v.encNosp v.encDepth VG.Proof.AesOcb.X86_64.hcall_enc VG.Proof.AesOcb.X86_64.sealPre_ok VG.Proof.AesOcb.X86_64.xorOfs_ok ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩ L hR hDW hn hP

/-- `body` for `open`, in two runs. -/
theorem bodyOpen_rel (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n < 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesOcb.X86_64.BRun K W SP R N A D nl n tl s₁ ∧ VG.Proof.AesOcb.X86_64.BRun K W SP R N A D nl n tl s₂) :
    RelCT isa P (VG.Impl.AesOcb.X86_64.body (VG.Proof.AesOcb.X86_64.callees v) false) fun _ _ => True := by
  simp only [VG.Impl.AesOcb.X86_64.body, Bool.false_eq_true, ↓reduceIte]
  exact VG.Proof.AesOcb.X86_64.body_rel' v false v.decOk v.decCt v.decNosp v.decDepth VG.Proof.AesOcb.X86_64.hcall_dec VG.Proof.AesOcb.X86_64.xorOfs_ok VG.Proof.AesOcb.X86_64.openPost_ok ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩ L hR hDW hn hP

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.CmpMask`. -/
section

/-!
# AES-OCB on x86-64: checking the tag and masking the data (`cmp`, `mask`)

Untrusted: everything here is checked by Lean. `cmp` ORs the XORs of the
first `tag_len` bytes of the received tag (at `W`) and the computed one (at
`W + t2O`) and leaves 1 at `W` if the OR is 0, else 0 (`cmp_ok`); `mask`
ANDs every byte of the data with `0 − ok`: the data stays if the tags were
equal, and is zeroed if not (`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (zeros)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt eval_e eval_ne length_bytesAt)
open VG.Proof.AesGcm.X86_64 (in_of_covers succ_ofNat bytesAt_succ)

/-! ## `cmp` -/

theorem setWidth_xor_eq_zero (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64 = 0#64) ↔ a = b := by
  rw [BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth] at this
    rwa [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega),
      Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)] at this
  · intro h; rw [h]

theorem toNat_setWidth_xor (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).toNat < 256 := by
  simp only [BitVec.toNat_xor, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega), Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact Nat.xor_lt_two_pow (n := 8) a.isLt b.isLt

/-- `(x − 1) >> 63` is 1 if `x` is 0 and 0 if `0 < x < 256`. -/
theorem okBit {x : BitVec 64} (h : x.toNat < 256) : (x - 1#64) >>> 63 = if x = 0#64 then 1#64 else 0#64 := by
  by_cases hx : x = 0#64
  · subst hx; decide
  · simp only [hx, ↓reduceIte]
    have hx' : 0 < x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hx
      · exact h0
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    rw [show 2 ^ 64 - 1 % 2 ^ 64 + x.toNat = (x.toNat - 1) + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]

/-- One step of `cmp`. -/
theorem cmpStep_ok (s : State) {W : Addr} {j T : Nat} (h15 : s.gpr .r15 = W)
    (h1 : s.gpr .rcx = BitVec.ofNat 64 j) (h12 : s.gpr .r12 = BitVec.ofNat 64 T)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 j) 1)
    (r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 128 + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa [.movzx8 .rax { base := .r15, index := some .rcx },
        .movzx8 .r8 { base := .r15, index := some .rcx, disp := t2O }, .alu .xor .rax (.reg .r8),
        .alu .or .rdx (.reg .rax), addi .rcx 1, .alu .cmp .rcx (.reg .r12)] s = some s' ∧
      s'.mem = s.mem ∧
      s'.gpr .rdx = s.gpr .rdx ||| ((s.mem (W + BitVec.ofNat 64 j)).setWidth 64 ^^^
        (s.mem (W + BitVec.ofNat 64 128 + BitVec.ofNat 64 j)).setWidth 64) ∧
      s'.gpr .rcx = BitVec.ofNat 64 (j + 1) ∧
      s'.zf = some (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 T == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea₁ := VG.Proof.AesOcb.X86_64.ea_index s h15 h1
  have ea₂ : s.gpr .r15 + s.gpr .rcx * BitVec.ofNat 64 1 + BitVec.ofNat 64 128 =
      W + BitVec.ofNat 64 128 + BitVec.ofNat 64 j := VG.Proof.AesOcb.X86_64.ea_index_disp s (d := 128) h15 h1
  refine ⟨_, by orun [ea₁, ea₂, r₀, r₁], ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_⟩
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h1, sext1, ← BitVec.ofNat_add]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h1, h12, sext1,
      ← BitVec.ofNat_add]
  · simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, h₄, ite_false]
  all_goals rfl

/-- `cmp`: 1 at `W` if the first `tl` bytes at `W` and `W + t2O` are equal, else 0. -/
theorem cmp_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {tl : Nat} (h1 : 1 ≤ tl) (h16 : tl ≤ 16)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) :
    WP isa cmp s fun t => t.mem = s.mem.writeW (W + BitVec.ofNat 64 tagO)
        (if bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl then 1#64 else 0#64) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r12 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  have r₀ := E.perm.wR (show 224 + 8 ≤ 2560 by decide)
  simp only [tlO] at htl
  obtain ⟨s₁, run₁, rdx₁, rcx₁, r12₁, m₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.alu .xor .rdx (.reg .rdx), .mov .rcx (.imm 0), VG.Impl.AesOcb.X86_64.ld .r12 .r15 tlO] s = some s₁ ∧
      s₁.gpr .rdx = 0#64 ∧ s₁.gpr .rcx = BitVec.ofNat 64 0 ∧ s₁.gpr .r12 = BitVec.ofNat 64 tl ∧ s₁.mem = s.mem ∧
      (∀ r, r ≠ .rdx → r ≠ .rcx → r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [E.r15, r₀, htl], ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, BitVec.xor_self, sext0]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, BitVec.xor_self, sext0]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, htl]
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, ite_false]
    all_goals rfl
  have h15₁ : s₁.gpr .r15 = W := by rw [g₁ _ (by decide) (by decide) (by decide), E.r15]
  unfold cmp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hR : ∀ {d j : Nat}, d + j < 2560 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d + BitVec.ofNat 64 j) 1 :=
    fun h => by rw [Offset.add_add]; exact E.perm.wR (by omega)
  -- The loop: the OR of the XORs of the first `j` bytes in `rdx`.
  refine WP.seq (WP.mono (WP.loop (M := isa) (c := .ne)
    (Q := fun u => (u.gpr .rdx).toNat < 256 ∧
      (u.gpr .rdx = 0#64 ↔ bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl) ∧
      u.mem = s.mem ∧ (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r12 → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr)
    (fun (k : Nat) (u : State) => ∃ j, k = tl - j ∧ j < tl ∧ u.gpr .rcx = BitVec.ofNat 64 j ∧
      u.gpr .r12 = BitVec.ofNat 64 tl ∧ (u.gpr .rdx).toNat < 256 ∧
      (u.gpr .rdx = 0#64 ↔ bytesAt s.mem W j = bytesAt s.mem (W + BitVec.ofNat 64 t2O) j) ∧
      u.mem = s.mem ∧ (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r12 → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr) ?_ (tl - 0) _
    ⟨0, rfl, by omega, rcx₁, r12₁, by rw [rdx₁]; decide, by rw [rdx₁]; simp [bytesAt], m₁,
      fun r _ h₂ h₃ _ h₅ => g₁ r h₂ h₃ h₅, rd₁, wr₁⟩) fun u hu => ?_)
  · rintro k u ⟨j, rfl, hj, rcx, r12, lt, iff, mem, g, rd, wr⟩
    have h15 : u.gpr .r15 = W := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), E.r15]
    obtain ⟨u', run', mem', rdx', rcx', zf', g', rd', wr'⟩ := VG.Proof.AesOcb.X86_64.cmpStep_ok u (W := W) (j := j) (T := tl) h15 rcx r12
      (by rw [rd, wr, show W + BitVec.ofNat 64 j = W + BitVec.ofNat 64 0 + BitVec.ofNat 64 j by simp]
          exact hR (by omega))
      (by rw [rd, wr]; exact hR (by omega))
    refine WP.of_runBlock ⟨u', run', ?_⟩
    rw [mem] at rdx'
    have lt' : (u'.gpr .rdx).toNat < 256 := by
      rw [rdx', BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 8) lt (VG.Proof.AesOcb.X86_64.toNat_setWidth_xor _ _)
    have iff' : u'.gpr .rdx = 0#64 ↔
        bytesAt s.mem W (j + 1) = bytesAt s.mem (W + BitVec.ofNat 64 t2O) (j + 1) := by
      rw [rdx', BitVec.or_eq_zero_iff, iff, VG.Proof.AesOcb.X86_64.setWidth_xor_eq_zero, VG.Proof.AesGcm.X86_64.bytesAt_succ, VG.Proof.AesGcm.X86_64.bytesAt_succ]
      constructor
      · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]; rfl
      · intro h
        obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt, VG.Proof.AesCcm.X86_64.length_bytesAt])
        exact ⟨h₁, List.head_eq_of_cons_eq h₂⟩
    have hz : u'.zf = some (decide (j + 1 = tl)) := by
      rw [zf', Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    have gg : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r12 → u'.gpr r = s.gpr r :=
      fun r h₁ h₂ h₃ h₄ h₅ => by rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄ h₅]
    by_cases he : j + 1 = tl
    · left
      exact ⟨(eval_ne hz).trans (by simp [he]), lt', by rw [iff', he], by rw [mem', mem], gg, by rw [rd', rd],
        by rw [wr', wr]⟩
    · right
      exact ⟨(eval_ne hz).trans (by simp [he]), tl - (j + 1), by omega, j + 1, rfl, by omega, rcx',
        by rw [g' _ (by decide) (by decide) (by decide) (by decide), r12], lt', iff', by rw [mem', mem], gg,
        by rw [rd', rd], by rw [wr', wr]⟩
  · obtain ⟨lt, iff, mem, g, rd, wr⟩ := hu
    have h15 : u.gpr .r15 = W := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), E.r15]
    have w₀ : InRegions u.wr (W + BitVec.ofNat 64 0) 8 := by rw [wr]; exact E.perm.wW (by decide)
    refine WP.of_runBlock ⟨_, by orun [h15, w₀], ?_, fun r h₁ h₂ h₃ h₄ h₅ => ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_setFlags, mem_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true,
        ite_false, reduceCtorEq, sext1, mem]
      rw [show BitVec.ofNat 64 1 = 1#64 from rfl, VG.Proof.AesOcb.X86_64.okBit lt]
      by_cases he : bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl
      · simp only [iff.mpr he, he, ↓reduceIte]; rfl
      · simp only [mt iff.mp he, he, ↓reduceIte]; rfl
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h₁, h₂, h₃, h₄, h₅, ite_false]
      exact g r h₁ h₂ h₃ h₄ h₅
    all_goals simp only [rd, wr]

/-! ## `mask` -/

theorem mask_byte (b : Byte) (c : Bool) :
    ((b.setWidth 64 &&& ((0 : BitVec 64) - (if c then 1#64 else 0#64))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then 1#64 else 0#64) = 1#64 from rfl,
      show (0 : BitVec 64) - 1#64 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    simp

theorem maskStep_ok (s : State) {P : Addr} {j L : Nat} {c : Bool} (h3 : s.gpr .rbx = P)
    (h1 : s.gpr .rcx = BitVec.ofNat 64 j) (hdx : s.gpr .rdx = 0 - (if c then 1#64 else 0#64))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 L)
    (rq : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 j) 1) (wq : InRegions s.wr (P + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa [.movzx8 .rax { base := .rbx, index := some .rcx }, .alu .and .rax (.reg .rdx),
        .store8 { base := .rbx, index := some .rcx } .rax, addi .rcx 1, .alu .cmp .rcx (.reg .r12)] s = some s' ∧
      s'.mem = s.mem.writeW (P + BitVec.ofNat 64 j) ((if c then s.mem (P + BitVec.ofNat 64 j) else 0 : Byte)) ∧
      s'.gpr .rcx = BitVec.ofNat 64 (j + 1) ∧
      s'.zf = some (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 L == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea := VG.Proof.AesOcb.X86_64.ea_index s h3 h1
  refine ⟨_, by orun [ea, rq, wq], ?_, ?_, ?_, fun r h₁ h₂ => ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hdx,
      VG.Proof.AesOcb.X86_64.mask_byte]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h1, sext1, ← BitVec.ofNat_add]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h1, h12, sext1,
      ← BitVec.ofNat_add]
  · simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, ite_false]
  all_goals rfl

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, VG.Proof.AesCcm.X86_64.length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, VG.Proof.AesGcm.X86_64.bytesAt_succ, List.replicate_succ']

/-- Every byte of the data ANDed with `0 − ok`. -/
theorem mask_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {D : Addr} {n : Nat}
    (hdata : s.mem.readW (W + BitVec.ofNat 64 208) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) (hD : DBuf K W SP s D n) {c : Bool}
    (hok : s.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64) :
    WP isa mask s fun t => Env K W SP t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mem = writeBytes s.mem D (if c then bytesAt s.mem D n else zeros n) := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 216 + 8 ≤ 2560 by decide)
  have r₃ := E.perm.wR (show 0 + 8 ≤ 2560 by decide)
  simp only [tagO] at hok
  have hn := hD.lt
  obtain ⟨s₁, run₁, m₁, h3₁, h12₁, hdx₁, h1₁, zf₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [VG.Impl.AesOcb.X86_64.ld .rbx .r15 dataO, VG.Impl.AesOcb.X86_64.ld .r12 .r15 lenO, .alu .xor .rdx (.reg .rdx),
        .alu .sub .rdx (.mem (at_ .r15 tagO)), .mov .rcx (.imm 0), .alu .test .r12 (.reg .r12)] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .rbx = D ∧ s₁.gpr .r12 = BitVec.ofNat 64 n ∧
      s₁.gpr .rdx = 0 - (if c then 1#64 else 0#64) ∧ s₁.gpr .rcx = BitVec.ofNat 64 0 ∧
      s₁.zf = some (decide (n = 0)) ∧
      (∀ r ∈ [Reg.r14, .r15, .rsp], s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [h15, r₁, r₂, r₃, hdata, hlen, hok], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, BitVec.xor_self, sext0, hok]; rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, BitVec.xor_self, sext0]
    · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
        Proof.AesCcm.X86_64.and_self_beq hn]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  have E₁ : Env K W SP s₁ := E.keep g₁ rd₁ wr₁
  unfold mask
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := of_decide_eq_true hb
    subst hn0
    refine ⟨E₁, rd₁, wr₁, ?_⟩
    rw [m₁]
    cases c <;> simp [bytesAt, zeros, writeBytes_nil]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .rcx = BitVec.ofNat 64 j ∧
      t.mem = writeBytes s.mem D (if c then bytesAt s.mem D j else zeros j) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → t.gpr r = s₁.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn0, h1₁, by rw [m₁]; cases c <;> simp [bytesAt, zeros, writeBytes_nil],
      fun r _ _ => rfl, rd₁, wr₁⟩
  rintro k t ⟨j, rfl, hj, h1, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', h1', zf', g', rd', wr'⟩ := VG.Proof.AesOcb.X86_64.maskStep_ok t (P := D) (j := j) (L := n) (c := c)
    (by rw [g _ (by decide) (by decide), h3₁]) h1 (by rw [g _ (by decide) (by decide), hdx₁])
    (by rw [g _ (by decide) (by decide), h12₁]) (by rw [rd, wr]; exact in_of_covers hD.rd hj hn)
    (by rw [wr]; exact in_of_covers hD.wr hj hn)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [VG.Proof.AesOcb.X86_64.length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (D + BitVec.ofNat 64 j) = s.mem (D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat D (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = writeBytes s.mem D (if c then bytesAt s.mem D (j + 1) else zeros (j + 1)) := by
    rw [mem', hq, mem, VG.Proof.AesOcb.X86_64.mask_succ, writeBytes_snoc _ _ _ _ (by rw [VG.Proof.AesOcb.X86_64.length_mask]; omega), VG.Proof.AesOcb.X86_64.length_mask]
  have hz : t'.zf = some (decide (j + 1 = n)) := by
    rw [zf', Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .rcx → t'.gpr r = s₁.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  have E' : Env K W SP t' := E₁.keep (fun r hr => gg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    (by rw [rd', rd, rd₁]) (by rw [wr', wr, wr₁])
  by_cases he : j + 1 = n
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), E', by rw [rd', rd], by rw [wr', wr], by rw [hmem, he]⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), n - (j + 1), by omega, j + 1, rfl, by omega, h1', hmem, gg,
      by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.Seal`. -/
section

/-!
# AES-OCB on x86-64: `vg_aes_ocb_seal`

Untrusted: everything here is checked by Lean. The preconditions `sealPreX`
and `openPreX` give the facts the proofs use about the arguments (`Args`,
`sealArgs_of`, `openArgs_of`). `seal` is `front`: `entry`, `Offset_0`
(`nonce`), `HASH` (`hash`), the data (`body`) and the tag at `W` (`tag`)
(`sealFront_wp`); then the copy of the tag to `tag` (`tagOut`) and
`restore` (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append length_bytesAt bytesAt_frame covers_left covers_of_mem)

/-- What `seal` and `open` are given: the key context at `K` for `R`
rounds, the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), the tag (`tl` bytes at `T`), the working
space at `W` and the stack pointer `SP`. -/
structure Args (s : State) (K W SP N A D : Addr) (R nl al n tl : Nat) (T : Addr) : Prop where
  lay : Lay K W SP
  perm : Perm K W s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : Buf W SP s N nl
  aad : Buf W SP s A al
  data : DBuf K W SP s D n
  tag : Buf W SP s T tl
  nd : (⟨N, nl⟩ : Region).Disjoint ⟨D, n⟩
  td : (⟨T, tl⟩ : Region).Disjoint ⟨D, n⟩
  ad : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩
  n1 : 1 ≤ nl
  n15 : nl ≤ 15
  t1 : 1 ≤ tl
  t16 : tl ≤ 16
  retW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩
  retD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  retT : (⟨SP, 8⟩ : Region).Disjoint ⟨T, tl⟩
  args : Covers [⟨SP + BitVec.ofNat 64 8, 40⟩] (s.rd ++ s.wr)
  argsW : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨W, 2560⟩

/-- `Args` from the facts both preconditions give, for a state that may
read the key context, the nonce, the associated data, the tag and the
arguments on the stack, and write the data and `W`. -/
theorem args_of {s : State} (h : oneFacts s)
    (mrd : ∀ r ∈ [aCtx s, aNonce s, aAad s, args s 5, aTag s], Covers [r] (s.rd ++ s.wr))
    (mwr : ∀ r ∈ [aData s, aWork s], Covers [r] s.wr) :
    VG.Proof.AesOcb.X86_64.Args s (s.gpr .rdi) (arg s 4) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (arg s 0) (s.gpr .rsi).toNat
      (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat (arg s 2) := by
  obtain ⟨d3, d4, d5, d6, d7, d8, t1, t2, d9, _, d11, d12, d13, t3, d14, d15, d16, d17, d18, t4, b19, b20, b21, b22,
    bt, b23, b24, _, hR, hv⟩ := h
  simp only [Spec.Ocb.lengthsOk, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨ht1, ht16⟩, hn1⟩, hn15⟩ := hv
  exact {
    lay := ⟨b19, b23, d4, d14, d18, b24⟩
    perm := ⟨mrd _ (by simp), mwr _ (by simp)⟩
    rounds := hR
    nonce := ⟨mrd _ (by simp), BitVec.isLt _, b20, d6, d15⟩
    aad := ⟨mrd _ (by simp), BitVec.isLt _, b21, d8, d16⟩
    data := ⟨⟨covers_left (mwr _ (by simp)), BitVec.isLt _, b22, d9, d17⟩, mwr _ (by simp), d3⟩
    tag := ⟨mrd _ (by simp), BitVec.isLt _, bt, t2, t4⟩
    nd := d5
    ad := d7
    td := t1
    n1 := hn1
    n15 := hn15
    t1 := ht1
    t16 := ht16
    retW := d13
    retD := d12
    retT := t3
    args := mrd (args s 5) (by simp)
    argsW := d11.symm }

theorem sealArgs_of {s : State} (h : sealPreX s) :
    VG.Proof.AesOcb.X86_64.Args s (s.gpr .rdi) (arg s 4) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (arg s 0) (s.gpr .rsi).toNat
      (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat (arg s 2) := by
  obtain ⟨hrd, hwr, -, -, -, -, hf⟩ := h
  refine VG.Proof.AesOcb.X86_64.args_of hf (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (rw [hrd, hwr]; exact covers_of_mem (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hwr]; exact covers_of_mem (by simp))

theorem openArgs_of {s : State} (h : openPreX s) :
    VG.Proof.AesOcb.X86_64.Args s (s.gpr .rdi) (arg s 4) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (arg s 0) (s.gpr .rsi).toNat
      (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat (arg s 2) := by
  obtain ⟨hrd, hwr, hf⟩ := h
  refine VG.Proof.AesOcb.X86_64.args_of hf (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (rw [hrd, hwr]; exact covers_of_mem (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hwr]; exact covers_of_mem (by simp))

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

section
variable {K W SP D : Addr} {n : Nat} {m m' : Mem}

theorem saved_mut (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hf : Frame (mutR W SP D n) m m') {g : Reg → BitVec 64} (S : VG.Proof.AesOcb.X86_64.Saved m W g) : VG.Proof.AesOcb.X86_64.Saved m' W g := by
  intro p hp
  rw [← S p hp]
  have hd : 160 ≤ p.2 ∧ p.2 + 8 ≤ 248 := by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact hf.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (w := 64) (Region.contains_self _ _) (kept_mut L hD (.inl hd))
    (by decide)

theorem buf_mut {s : State} {P : Addr} {len : Nat} (hP : Buf W SP s P len)
    (hPD : (⟨P, len⟩ : Region).Disjoint ⟨D, n⟩) (hf : Frame (mutR W SP D n) m m') :
    bytesAt m' P len = bytesAt m P len :=
  VG.Proof.AesCcm.X86_64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm
    · exact hPD) (by have := hP.lt; omega)

theorem lstar_mut (L : Lay K W SP) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩) (hf : Frame (mutR W SP D n) m m') :
    ctxLstar m' K = ctxLstar m K :=
  VG.Proof.AesOcb.X86_64.blockAtMem_frame hf fun r hr => (k_mut L hD r hr).sub_left (Lay.kSub (by decide))

end

/-- What `tag d` writes, within the parts the pieces write. -/
theorem tagR_mut {W SP D : Addr} {n d : Nat} (hd : d + 16 ≤ 160) {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 d, 16⟩, wC W, below SP 8] m m') :
    Frame (mutR W SP D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA hd⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The return address is outside what the functions write. -/
theorem ret_disj {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩) : ∀ r ∈ VG.Proof.AesOcb.X86_64.entryR W :: mutR W SP D n, (⟨SP, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Region.sub_prefix (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below SP (by have := L.sp; omega)
  · exact hD

/-- The first `t ≤ 16` bytes of a block. -/
theorem bytesAt_take_block (m : Mem) (p : Addr) {t : Nat} (h : t ≤ 16) :
    bytesAt m p t = (Spec.Ocb.toBytes (blockAtMem m p)).take t := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (VG.Proof.AesCcm.X86_64.length_bytesAt _ _ _), show (16 : Nat) = t + (16 - t) by omega,
    Proof.Ocb.bytesAt_append, List.take_left' (VG.Proof.AesCcm.X86_64.length_bytesAt _ _ _)]

/-- What the pieces before the data leave: the offset, the checksum, `L_$`,
`L_0` and `HASH`. -/
structure Pre (K W SP N A D : Addr) (R nl al n tl : Nat) (T : Addr) (s s' : State) : Prop where
  env : Env K W SP s'
  frame : Frame (VG.Proof.AesOcb.X86_64.entryR W :: mutR W SP D n) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  slots : Slots W R N A D nl n tl s'.mem
  tg : s'.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T
  saved : VG.Proof.AesOcb.X86_64.Saved s'.mem W s.gpr
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) =
    Spec.Ocb.offset0 (ctxCiph s.mem K R) tl (bytesAt s.mem N nl)
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) =
    Spec.Ocb.offset0 (ctxCiph s.mem K R) tl (bytesAt s.mem N nl)
  ck : blockAtMem s'.mem (W + BitVec.ofNat 64 ckO) = 0
  ld : blockAtMem s'.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K)
  l0 : blockAtMem s'.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0
  sum : blockAtMem s'.mem (W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al)
  ciph : ctxCiph s'.mem K R = ctxCiph s.mem K R
  lstar : ctxLstar s'.mem K = ctxLstar s.mem K
  data : bytesAt s'.mem D n = bytesAt s.mem D n

/-- `entry`, `nonce` and `hash`. -/
theorem pre_wp' (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : VG.Proof.AesOcb.X86_64.Args s K W SP N A D R nl al n tl T) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa (.seq (.block VG.Impl.AesOcb.X86_64.entry) (.seq (nonce (VG.Proof.AesOcb.X86_64.callees v)) (hash (VG.Proof.AesOcb.X86_64.callees v)))) s
      (VG.Proof.AesOcb.X86_64.Pre K W SP N A D R nl al n tl T s) := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 256 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  obtain ⟨s₁, run₁, P₁⟩ := VG.Proof.AesOcb.X86_64.entry_ok L Ar.perm hsp Ar.args Ar.argsW hD hn hT htl hW hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have eK : ctxCiph s₁.mem K R = ctxCiph s.mem K R := by
    unfold ctxCiph
    rw [VG.Proof.AesCcm.X86_64.bytesAt_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))) (by omega)]
  have eL : ctxLstar s₁.mem K = ctxLstar s.mem K := VG.Proof.AesOcb.X86_64.blockAtMem_frame P₁.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (L.k_w.sub_left (Lay.kSub (by decide))).sub_right (Lay.wSub (by decide)))
  have eB : ∀ {P : Addr} {k : Nat}, Buf W SP s P k → bytesAt s₁.mem P k = bytesAt s.mem P k := fun hP =>
    VG.Proof.AesCcm.X86_64.bytesAt_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)
  -- `Offset_0`.
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.nonce_ok v L P₁.env Ar.rounds P₁.slots.rounds P₁.slots.nonce P₁.slots.nlen P₁.slots.tl
    Ar.n1 Ar.n15 (by have := Ar.t16; omega) (Ar.nonce.of_eq P₁.rd P₁.wr) Ar.data.k Ar.data.w) fun s₂ P₂ => ?_)
  have F₂ : Frame (mutR W SP D n) s₁.mem s₂.mem := VG.Proof.AesOcb.X86_64.nonceR_mut P₂.frame
  have S₂ := Slots.of_mut L Ar.data.w F₂ P₁.slots
  have c₂ : ctxCiph s₂.mem K R = ctxCiph s.mem K R := (VG.Proof.AesOcb.X86_64.ctxCiph_mut L Ar.data.k F₂ Ar.rounds).trans eK
  have l₂ : ctxLstar s₂.mem K = ctxLstar s.mem K := (VG.Proof.AesOcb.X86_64.lstar_mut L Ar.data.k F₂).trans eL
  have a₂ : bytesAt s₂.mem A al = bytesAt s.mem A al := (VG.Proof.AesOcb.X86_64.buf_mut Ar.aad Ar.ad F₂).trans (eB Ar.aad)
  -- `HASH`.
  have C : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R (ctxCiph s.mem K R) (ctxLstar s.mem K) A (bytesAt s.mem A al) s₂ :=
    { lay := L, rounds := Ar.rounds, ciph := c₂, lstar := l₂
      buf := by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact Ar.aad.of_eq (P₂.rd.trans P₁.rd) (P₂.wr.trans P₁.wr)
      aad := by rw [VG.Proof.AesCcm.X86_64.length_bytesAt, a₂]
      ad := by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact Ar.ad
      kd := Ar.data.k, dw := Ar.data.w, rnd := S₂.rounds
      short := by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact Ar.aad.lt }
  refine WP.mono (VG.Proof.AesOcb.X86_64.hash_ok v C P₂.env S₂.aad (by rw [P₂.alen, P₁.alen, VG.Proof.AesCcm.X86_64.length_bytesAt])
    (by rw [P₂.keep (by decide) (by decide), P₁.l0])) fun s₃ ⟨E₃, F₃, sum₃, rd₃, wr₃⟩ => ?_
  have F₃' : Frame (mutR W SP D n) s₂.mem s₃.mem := VG.Proof.AesOcb.X86_64.hashR_mut F₃
  have k₃ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ (64 ≤ d ∧ d + 16 ≤ 96) ∨ (256 ≤ d ∧ d + 16 ≤ 384)) →
      blockAtMem s₃.mem (W + BitVec.ofNat 64 d) = blockAtMem s₂.mem (W + BitVec.ofNat 64 d) := fun {d} hd =>
    VG.Proof.AesOcb.X86_64.blockAtMem_frame F₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact (L.stk_w' (by omega)).symm
  refine ⟨E₃, ?_, by rw [rd₃, P₂.rd, P₁.rd], by rw [wr₃, P₂.wr, P₁.wr], Slots.of_mut L Ar.data.w F₃' S₂,
    by rw [VG.Proof.AesOcb.X86_64.kept_read L Ar.data.w (F₂.trans F₃') (d := tgO) (by decide), P₁.tg],
    VG.Proof.AesOcb.X86_64.saved_mut L Ar.data.w (F₂.trans F₃') P₁.saved, ?_, ?_, ?_, ?_, ?_, by rw [sum₃],
    (VG.Proof.AesOcb.X86_64.ctxCiph_mut L Ar.data.k F₃' Ar.rounds).trans c₂, (VG.Proof.AesOcb.X86_64.lstar_mut L Ar.data.k F₃').trans l₂, ?_⟩
  · exact (P₁.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩).trans
      ((F₂.trans F₃').sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  · rw [k₃ (d := ofsO) (by decide), P₂.ofs, eK, eB Ar.nonce]
  · rw [k₃ (d := o0O) (by decide), P₂.o0, eK, eB Ar.nonce]
  · rw [k₃ (d := ckO) (by decide), P₂.keep (by decide) (by decide), P₁.ck]
  · rw [k₃ (d := ldO) (by decide), P₂.keep (by decide) (by decide), P₁.ld]
  · rw [k₃ (d := l0O) (by decide), P₂.keep (by decide) (by decide), P₁.l0]
  · have hd := Ar.data
    rw [VG.Proof.AesCcm.X86_64.bytesAt_frame F₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.stk.symm) (by have := hd.lt; omega),
      VG.Proof.AesCcm.X86_64.bytesAt_frame P₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.w.sub_right (Lay.wSub (by decide))
        · exact hd.stk.symm) (by have := hd.lt; omega), eB hd.toBuf]

/-- `entry`, `nonce` and `hash`, then `k`. -/
theorem pre_wp (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : VG.Proof.AesOcb.X86_64.Args s K W SP N A D R nl al n tl T) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al)
    {k : Prog isa} {Q : State → Prop} (hk : ∀ s', VG.Proof.AesOcb.X86_64.Pre K W SP N A D R nl al n tl T s s' → WP isa k s' Q) :
    WP isa (.seq (.block VG.Impl.AesOcb.X86_64.entry) (.seq (nonce (VG.Proof.AesOcb.X86_64.callees v)) (.seq (hash (VG.Proof.AesOcb.X86_64.callees v)) k))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (VG.Proof.AesOcb.X86_64.pre_wp' v Ar hsp hD hn hT htl hW hdi hsi hdx hcx hr8 hr9)) fun _ h₁ =>
    wp_seq_assoc (WP.seq (WP.mono h₁ hk)))

/-- `body`'s frame misses a block of `W` outside the offset, the checksum and
`[96, 144)`. -/
theorem body_keep {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {m m' : Mem}
    (h : Frame (VG.Proof.AesOcb.X86_64.bodyR W SP D n) m m') {d : Nat} (hd : d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (144 ≤ d ∧ d + 16 ≤ 384)) :
    blockAtMem m' (W + BitVec.ofNat 64 d) = blockAtMem m (W + BitVec.ofNat 64 d) :=
  VG.Proof.AesOcb.X86_64.blockAtMem_frame h fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.w_w (by omega) (by omega) (by decide)
    · exact L.w_w (by omega) (by omega) (by decide)
    · exact L.w_w (by omega) (by omega) (by decide)
    · exact (L.stk_w' (by omega)).symm
    · exact (hD.sub_right (Lay.wSub (by omega))).symm

/-- What `front` leaves for `seal`: the environment, the slots and the
address of the tag, our caller's registers, the encrypted data and the tag
at `W`. -/
structure SFront (K W SP N A D : Addr) (R nl al n tl : Nat) (T : Addr) (s s' : State) : Prop where
  env : Env K W SP s'
  frame : Frame (VG.Proof.AesOcb.X86_64.entryR W :: mutR W SP D n) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  slots : Slots W R N A D nl n tl s'.mem
  tg : s'.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T
  saved : VG.Proof.AesOcb.X86_64.Saved s'.mem W s.gpr
  out : Spec.Ocb.encryptWith (ctxCiph s.mem K R) (ctxLstar s.mem K) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
    (bytesAt s.mem D n) = (bytesAt s'.mem D n, bytesAt s'.mem W tl)

/-- `seal`'s `front`, for its arguments. -/
theorem sealFront_wp' (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : VG.Proof.AesOcb.X86_64.Args s K W SP N A D R nl al n tl T) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa (front (VG.Proof.AesOcb.X86_64.callees v) true tagO) s (VG.Proof.AesOcb.X86_64.SFront K W SP N A D R nl al n tl T s) := by
  have L := Ar.lay
  unfold front
  refine VG.Proof.AesOcb.X86_64.pre_wp v Ar hsp hD hn hT htl hW hdi hsi hdx hcx hr8 hr9 fun s₃ P₃ => ?_
  have hD₃ : DBuf K W SP s₃ D n := Ar.data.of_eq P₃.rd P₃.wr
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.bodySeal_ok v L P₃.env Ar.rounds P₃.slots.rounds hD₃ P₃.slots.data P₃.slots.len P₃.ofs
    P₃.o0 P₃.ck (by rw [P₃.l0, P₃.lstar])) fun s₄ B => ?_)
  have F₄ : Frame (mutR W SP D n) s₃.mem s₄.mem := VG.Proof.AesOcb.X86_64.bodyR_mut B.frame
  have cK₄ : ctxCiph s₄.mem K R = ctxCiph s.mem K R := (VG.Proof.AesOcb.X86_64.ctxCiph_mut L Ar.data.k F₄ Ar.rounds).trans P₃.ciph
  have ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K) := by
    rw [VG.Proof.AesOcb.X86_64.body_keep L Ar.data.w B.frame (d := ldO) (by decide), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al) := by
    rw [VG.Proof.AesOcb.X86_64.body_keep L Ar.data.w B.frame (d := sumO) (by decide), P₃.sum]
  -- The tag.
  refine WP.mono (VG.Proof.AesOcb.X86_64.tag_ok v L B.env Ar.rounds ((VG.Proof.AesOcb.X86_64.kept_read L Ar.data.w F₄ (d := 232) (by decide)).trans
    P₃.slots.rounds) (.inl rfl)) fun s₅ T₅ => ?_
  have F₅ : Frame (mutR W SP D n) s₄.mem s₅.mem := VG.Proof.AesOcb.X86_64.tagR_mut (by decide) T₅.frame
  refine ⟨T₅.env, P₃.frame.trans ((F₄.trans F₅).sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩),
    by rw [T₅.rd, B.rd, P₃.rd], by rw [T₅.wr, B.wr, P₃.wr], Slots.of_mut L Ar.data.w (F₄.trans F₅) P₃.slots,
    by rw [VG.Proof.AesOcb.X86_64.kept_read L Ar.data.w (F₄.trans F₅) (d := tgO) (by decide), P₃.tg],
    VG.Proof.AesOcb.X86_64.saved_mut L Ar.data.w (F₄.trans F₅) P₃.saved, ?_⟩
  -- The ciphertext and the tag.
  have hout := B.out
  rw [P₃.ciph, P₃.lstar, P₃.data] at hout
  have hofs := B.ofs
  rw [P₃.lstar] at hofs
  have hck := B.ck
  rw [P₃.data] at hck
  have d₅ : bytesAt s₅.mem D n = bytesAt s₄.mem D n :=
    VG.Proof.AesCcm.X86_64.bytesAt_frame T₅.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.stk.symm) (by have := Ar.data.lt; omega)
  have tv := T₅.val
  rw [show W + BitVec.ofNat 64 tagO = W from BitVec.add_zero W] at tv
  have t₅ : bytesAt s₅.mem W tl = (Spec.Ocb.toBytes (blockAtMem s₅.mem W)).take tl :=
    VG.Proof.AesOcb.X86_64.bytesAt_take_block _ _ Ar.t16
  rw [Proof.Ocb.encryptWith_eq, d₅, hout, t₅, tv, hck, hofs, ld₄, sum₄, cK₄]
  simp only [VG.Proof.AesCcm.X86_64.length_bytesAt, List.length_drop]
  by_cases hr : 0 < n % 16
  · have h' : n - 16 * (n / 16) > 0 := by omega
    simp only [h', hr, ↓reduceIte]
  · have h' : ¬ (n - 16 * (n / 16) > 0) := by omega
    simp only [h', hr, ↓reduceIte]

/-- The arguments of `copyLoop` for the copy of the tag: from `W` to the
tag, whose address is at `W + tgO`. -/
theorem tagOutArgs_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {T : Addr} {tl : Nat}
    (htg : s.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) :
    ∃ s', runBlock isa [mvr .rbx .r15, VG.Impl.AesOcb.X86_64.ld .rsi .r15 tgO, VG.Impl.AesOcb.X86_64.ld .r12 .r15 tlO, .mov .rcx (.imm 0)] s = some s' ∧
      s'.gpr .rbx = W ∧ s'.gpr .rsi = T ∧ s'.gpr .r12 = BitVec.ofNat 64 tl ∧ s'.gpr .rcx = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → r ≠ .r12 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [tgO, tlO] at htg htl
  have r₁ := E.perm.wR (show 304 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 224 + 8 ≤ 2560 by decide)
  refine ⟨_, by orun [E.r15, r₁, r₂, htg, htl], ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, E.r15]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, E.r15, htg]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, E.r15, htl]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sext0]
  · simp only [gpr_setReg, h₁, h₂, h₃, h₄, ite_false]
  all_goals rfl

/-- The received tag's arguments of `copyLoop`: from the tag, whose address
is at `W + tgO`, to `W`. -/
theorem recvArgs_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {T : Addr} {tl : Nat}
    (htg : s.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) :
    ∃ s', runBlock isa [VG.Impl.AesOcb.X86_64.ld .rbx .r15 tgO, mvr .rsi .r15, VG.Impl.AesOcb.X86_64.ld .r12 .r15 tlO, .mov .rcx (.imm 0)] s = some s' ∧
      s'.gpr .rbx = T ∧ s'.gpr .rsi = W ∧ s'.gpr .r12 = BitVec.ofNat 64 tl ∧ s'.gpr .rcx = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → r ≠ .r12 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [tgO, tlO] at htg htl
  have r₁ := E.perm.wR (show 304 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 224 + 8 ≤ 2560 by decide)
  refine ⟨_, by orun [E.r15, r₁, r₂, htg, htl], ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, E.r15, htg]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, E.r15]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, E.r15, htl]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sext0]
  · simp only [gpr_setReg, h₁, h₂, h₃, h₄, ite_false]
  all_goals rfl

/-- `tagOut`: the first `tl` bytes at `W` copied to the tag at `T`, which the
state may write. -/
theorem tagOut_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {T : Addr} {tl : Nat} (h1 : 1 ≤ tl) (h16 : tl ≤ 16)
    (htg : s.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (hT : Covers [⟨T, tl⟩] s.wr) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa tagOut s fun t => t.mem = writeBytes s.mem T (bytesAt s.mem W tl) ∧
      (∀ r ∈ [Reg.r14, .r15, .rsp], t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨s₁, run₁, rbx₁, rsi₁, r12₁, rcx₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86_64.tagOutArgs_ok E htg htl
  unfold tagOut
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (VG.Proof.AesOcb.X86_64.copyLoop_ok s₁ (S := W) (Dd := T) (n := tl) (by omega) (by omega) rbx₁ rsi₁ rcx₁ r12₁
    (by rw [rd₁, wr₁]; exact covers_left (covers_prefix E.perm.w (by omega))) (by rw [wr₁]; exact hT)
    (hTW.sub_right (Region.sub_prefix (by omega))).symm) fun t ⟨m, _, g, rd, wr⟩ => ⟨by rw [m, m₁], ?_,
      by rw [rd, rd₁], by rw [wr, wr₁]⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> rw [g _ (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide)]

/-- `vg_aes_ocb_seal`, for its arguments. -/
theorem seal_wp' (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : VG.Proof.AesOcb.X86_64.Args s K W SP N A D R nl al n tl T) (hTw : Covers [⟨T, tl⟩] s.wr) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa («seal» (VG.Proof.AesOcb.X86_64.callees v)) s fun s' => gprPreserved s s' ∧
      Spec.Ocb.encryptWith (ctxCiph s.mem K R) (ctxLstar s.mem K) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
        (bytesAt s.mem D n) = (bytesAt s'.mem D n, bytesAt s'.mem T tl) := by
  have L := Ar.lay
  unfold «seal»
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.sealFront_wp' v Ar hsp hD hn hT htl hW hdi hsi hdx hcx hr8 hr9) fun s₅ F => ?_)
  -- The copy of the tag.
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.tagOut_ok F.env Ar.t1 Ar.t16 F.tg F.slots.tl (by rw [F.wr]; exact hTw) Ar.tag.w)
    fun s₆ ⟨m₆, g₆, rd₆, wr₆⟩ => ?_)
  have E₆ : Env K W SP s₆ := F.env.keep g₆ rd₆ wr₆
  have F₆ : Frame [⟨T, tl⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact writeBytes_frame _ _ _ (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact Region.contains_self _ _)
  have S₆ : VG.Proof.AesOcb.X86_64.Saved s₆.mem W s.gpr := fun p hp => by
    rw [← F.saved p hp]
    exact F₆.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have hd : p.2 + 8 ≤ 2560 := by
        simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (Ar.tag.w.sub_right (Lay.wSub hd)).symm) (by decide)
  -- `restore`.
  obtain ⟨s₇, run₇, hg₇, hm₇, hsp₇, _⟩ := VG.Proof.AesOcb.X86_64.restore_ok E₆ S₆
  refine WP.of_runBlock ⟨s₇, run₇, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₇ (.rbx, savO) (by decide)
    · exact hg₇ (.rbp, savO + 8) (by decide)
    · rw [hsp₇, E₆.rsp, hsp]
    · exact hg₇ (.r12, savO + 16) (by decide)
    · exact hg₇ (.r13, savO + 24) (by decide)
    · exact hg₇ (.r14, savO + 32) (by decide)
    · exact hg₇ (.r15, savO + 40) (by decide)
  · rw [hm₇, hsp, F₆.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.retT) (by decide)]
    exact F.frame.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (VG.Proof.AesOcb.X86_64.ret_disj L Ar.retW Ar.retD) (by decide)
  · -- The ciphertext and the tag.
    have hn := Ar.data.lt
    have ht := Ar.tag.lt
    rw [F.out, hm₇, VG.Proof.AesCcm.X86_64.bytesAt_frame F₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.td.symm) (by omega), m₆,
      Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]) ht, VG.Proof.AesCcm.X86_64.length_bytesAt,
      List.drop_of_length_le (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]), List.append_nil]

/-- `vg_aes_ocb_seal`. -/
theorem seal_wp (v : BlocksImpl) {s : State} (h : sealPreX s) :
    WP isa («seal» (VG.Proof.AesOcb.X86_64.callees v)) s fun s' => gprPreserved s s' ∧ sealX86_64.post s s' :=
  VG.Proof.AesOcb.X86_64.seal_wp' v (VG.Proof.AesOcb.X86_64.sealArgs_of h) (covers_of_mem (by rw [h.2.1]; simp)) rfl rfl (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm rfl
    (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm rfl rfl (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm rfl (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm rfl (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.NonceCT`. -/
section

/-!
# AES-OCB on x86-64: `Offset_0` is constant time

Untrusted: everything here is checked by Lean. The nonce block and the
stretch pass the taint analysis from the public slots (`rel_taintC`); the
call of `vg_aes_encrypt_blocks` has the same arguments in both runs
(`callBlocks_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem nonce_rel (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (h1 : 1 ≤ nl) (h15 : nl ≤ 15) (ht : tl < 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₁ ∧ VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₂ ∧
      Buf W SP s₁ N nl ∧ Buf W SP s₂ N nl) :
    RelCT isa P (nonce (VG.Proof.AesOcb.X86_64.callees v)) fun _ _ => True := by
  have step : ∀ s, VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s → Buf W SP s N nl →
      WP isa nonceBlock s (VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl) := fun s o hB =>
    WP.mono (VG.Proof.AesOcb.X86_64.nonceBlock_ok L o.env o.sl.nonce o.sl.nlen o.sl.tl h1 h15 ht hB) fun s' Q =>
      o.step L hDW (o.env.keep (fun r hr => Q.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
        (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
        (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
        Q.rd Q.wr) Q.wr (Q.frame.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩
          · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), VG.Proof.AesOcb.X86_64.sub_wB (by decide) (by decide)⟩)
  have a := (VG.Proof.AesOcb.X86_64.rel_taintC [] [] hDW hn (fun s₁ s₂ h => Both.of (hP s₁ s₂ h).1 (hP s₁ s₂ h).2.1)
    (c := nonceBlock) ⟨_, by taint_decide⟩).wp (F₁ := VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl) (F₂ := VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl)
    fun s₁ s₂ h => ⟨step s₁ (hP s₁ s₂ h).1 (hP s₁ s₂ h).2.2.1, step s₂ (hP s₁ s₂ h).2.1 (hP s₁ s₂ h).2.2.2⟩
  have call : ∀ s, VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s →
      WP isa (callBlocks (VG.Proof.AesOcb.X86_64.callees v).enc (oneBlock tmpO)) s (VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl) := fun s o =>
    WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encDepth L o.env hR o.sl.rounds
      (oneBlock_ok o.env.r15 tmpO (by decide)) (dstW L o.env.perm (d := tmpO) (n := 1) (by decide))) fun s' Q => by
      have E' := o.env.of_saved Q.saved Q.rd Q.wr
      refine o.step L hDW E' Q.wr (Q.frame.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩
      · exact ⟨_, by simp, VG.Proof.AesOcb.X86_64.sub_wC (by decide) (by decide)⟩
      · rw [o.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩
  have b := (VG.Proof.AesOcb.X86_64.callBlocks_rel (b := (VG.Proof.AesOcb.X86_64.callees v).enc) v.encOk v.encCt L hR hDW hn [] [] (args := oneBlock tmpO) ⟨_, by taint_decide⟩
    (D' := W + BitVec.ofNat 64 tmpO) (k := 1)
    (P := fun s₁ s₂ => True ∧ VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₁ ∧ VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₂) fun s₁ s₂ h =>
      ⟨Both.of h.2.1 h.2.2, oneBlock_ok h.2.1.env.r15 tmpO (by decide), oneBlock_ok h.2.2.env.r15 tmpO (by decide),
        dstW L h.2.1.env.perm (by decide), dstW L h.2.2.env.perm (by decide)⟩).wp
    (F₁ := VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl) (F₂ := VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl)
    fun s₁ s₂ h => ⟨call s₁ h.2.1, call s₂ h.2.2⟩
  have c := VG.Proof.AesOcb.X86_64.rel_taintC [] [] hDW hn (fun s₁ s₂ (h : True ∧ VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₁ ∧ VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₂) =>
    Both.of h.2.1 h.2.2) (c := .block offset0) ⟨_, by taint_decide⟩
  exact RelCT.seq a (RelCT.seq b c)

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.HashCT`. -/
section

/-!
# AES-OCB on x86-64: `HASH` is constant time

Untrusted: everything here is checked by Lean. Each chunk fills its buffer
and adds it to the sum by code that passes the taint analysis from the
public slots, the number of blocks left (at `W + alenO`) and the position
in the associated data (`rbx`, `rbp`); the call between has the same
arguments in both runs (`callBlocks_rel`), and so does the rest's. Both runs
are at the same chunk at each iteration (`chunk_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append eval_e eval_ne)

section
variable {K W SP D : Addr} {n R : Nat} {ciph : Cipher} {l : Block} {A : Addr} {a : List Byte} {s₀ : State}

/-- A run of `HASH` keeps the public arguments. -/
theorem HInv.one {N : Addr} {nl tl : Nat} (C : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph l A a s₀)
    (o : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₀) {t : State} {j : Nat} (H : VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ t j) :
    VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl t :=
  ⟨H.env, Slots.of_mut C.lay C.dw (VG.Proof.AesOcb.X86_64.hashR_mut H.frame) o.sl, H.wr.trans o.wr⟩

theorem FillInv.one {N : Addr} {nl tl : Nat} (C : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph l A a s₀)
    (o : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₀) {t : State} {j c i : Nat} (F : VG.Proof.AesOcb.X86_64.FillInv K W SP D n ciph l A a s₀ j c t i) :
    VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl t :=
  ⟨F.env, Slots.of_mut C.lay C.dw (VG.Proof.AesOcb.X86_64.hashR_mut F.frame) o.sl, F.wr.trans o.wr⟩

/-- The first block and the chunks, if any. -/
theorem hashHI_ok (v : BlocksImpl) (C : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph l A a s₀) (E : Env K W SP s₀)
    (haad : s₀.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A)
    (halen : s₀.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a.length)
    (hl0 : blockAtMem s₀.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (.seq (.block (zero16 sumO ++ zero16 ohO ++
      [VG.Impl.AesOcb.X86_64.ld .rbx .r15 aadO, VG.Impl.AesOcb.X86_64.ld .rax .r15 alenO, mvr .rcx .rax, .alu .and .rcx (.imm 15),
       st .r15 tmpO .rcx, .shift .shr .rax 4, st .r15 alenO .rax, .mov .rbp (.imm 1),
       .alu .test .rax (.reg .rax)])) (.ite .e (.block []) (.loop (hashChunk (VG.Proof.AesOcb.X86_64.callees v)) .ne))) s₀
      fun t => VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ t (a.length / 16) := by
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.hashHead_ok C E haad halen hl0) fun s₃ ⟨H₀, zf₃⟩ => ?_)
  refine WP.ite (decide (a.length / 16 = 0)) (eval_e zf₃) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · exact (of_decide_eq_true hb) ▸ H₀
  · exact VG.Proof.AesOcb.X86_64.hashLoop_ok v C H₀ (Nat.pos_of_ne_zero (of_decide_eq_false hb))

/-- The length of the rest. -/
theorem tailHead_ok {t : State} (H : VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ t (a.length / 16)) :
    WP isa (.block [VG.Impl.AesOcb.X86_64.ld .r12 .r15 tmpO, .alu .test .r12 (.reg .r12)]) t fun t₁ =>
      VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ t₁ (a.length / 16) ∧ t₁.gpr .r12 = BitVec.ofNat 64 (a.length % 16) ∧
        t₁.zf = some (decide (a.length % 16 = 0)) := by
  have r₁ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 112) 8 := H.env.perm.wR (by decide)
  have rest := H.rest
  simp only [tmpO] at rest
  obtain ⟨t₁, run₁, r12₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [VG.Impl.AesOcb.X86_64.ld .r12 .r15 tmpO, .alu .test .r12 (.reg .r12)] t =
      some t₁ ∧ t₁.gpr .r12 = BitVec.ofNat 64 (a.length % 16) ∧ t₁.zf = some (decide (a.length % 16 = 0)) ∧
      (∀ r, r ≠ .r12 → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by orun [H.env.r15, r₁, rest], ?_, ?_, fun r h => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true]
    · simp only [zf_arithFlags, gpr_setReg, ite_true,
        Proof.AesCcm.X86_64.and_self_beq (show a.length % 16 < 2 ^ 64 by omega)]
    · simp only [gpr_setReg, gpr_arithFlags, h, ite_false]
    all_goals rfl
  exact WP.of_runBlock ⟨t₁, run₁,
    { H with
      env := H.env.keep (fun r hr => g₁ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₁ wr₁
      frame := by rw [m₁]; exact H.frame
      rd := by rw [rd₁, H.rd]
      wr := by rw [wr₁, H.wr]
      sum := by rw [m₁, H.sum]
      oh := by rw [m₁, H.oh]
      rbx := by rw [g₁ _ (by decide), H.rbx]
      rbp := by rw [g₁ _ (by decide), H.rbp]
      alen := by rw [m₁, H.alen]
      rest := by rw [m₁, H.rest]
      l0 := by rw [m₁, H.l0] }, r12₁, zf₁⟩

/-- The rest of the associated data, before its call, keeps the public arguments. -/
theorem hashRestPre_one {N : Addr} {nl tl : Nat} (C : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph l A a s₀)
    (o : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₀) {t : State} (H : VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ t (a.length / 16))
    (hr : 0 < a.length % 16) (h12 : t.gpr .r12 = BitVec.ofNat 64 (a.length % 16)) :
    WP isa (.seq (.block (xor16 .r14 240 ohO)) (.seq (padTo bufO) (.block (xor16 .r15 ohO bufO)))) t
      (VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl) := by
  have L := C.lay
  have E := H.env
  have hs := C.short
  have o₀ := H.one C o
  generalize hm : a.length / 16 = m at H
  obtain ⟨t₁, run₁, B₁⟩ := xor16_ok (s := t) (b := .r14) (a := 240) (d := ohO) E.r15 E.r14 (by decide) (by decide)
    (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => B₁.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    B₁.rd B₁.wr
  have hB := C.buf.slice (a := 16 * m) (k := a.length % 16) (by omega)
  have hS : Covers [⟨A + BitVec.ofNat 64 (16 * m), a.length % 16⟩] (t₁.rd ++ t₁.wr) := by
    rw [B₁.rd, B₁.wr, H.rd, H.wr]; exact hB.rd
  have hSD : (⟨A + BitVec.ofNat 64 (16 * m), a.length % 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 bufO, 16⟩ :=
    hB.w.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.padTo_ok E₁ hr (by omega) (by decide) (by rw [B₁.gpr _ (by decide), H.rbx])
    (by rw [B₁.gpr _ (by decide), h12]) hS hSD) fun t₂ ⟨fr₂, _, g₂, rd₂, wr₂⟩ => ?_)
  have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => g₂ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₂ wr₂
  obtain ⟨t₃, run₃, B₃⟩ := xor16_ok (s := t₂) (b := .r15) (a := ohO) (d := bufO) E₂.r15 E₂.r15 (by decide) (by decide)
    (E₂.perm.wR (by decide)) (E₂.perm.wR (by decide)) (E₂.perm.wW (by decide)) (E₂.perm.wW (by decide))
  have E₃ : Env K W SP t₃ := E₂.keep (fun r hr => B₃.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    B₃.rd B₃.wr
  refine WP.of_runBlock ⟨t₃, run₃, o₀.step L C.dw E₃ (by rw [B₃.wr, wr₂, B₁.wr])
    (((B₁.frame.sub fun r hr => ?_).trans (fr₂.sub fun r hr => ?_)).trans (B₃.frame.sub fun r hr => ?_))⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩
  all_goals simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, VG.Proof.AesOcb.X86_64.sub_wC (by decide) (by decide)⟩

end

/-- One chunk, at the same position in both runs. -/
theorem chunk_rel (v : BlocksImpl) {K W SP D : Addr} {n R : Nat} {ciph₁ ciph₂ : Cipher} {l₁ l₂ : Block} {A : Addr}
    {a₁ a₂ : List Byte} {s₀₁ s₀₂ : State} {N : Addr} {nl tl : Nat}
    (C₁ : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph₁ l₁ A a₁ s₀₁) (C₂ : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph₂ l₂ A a₂ s₀₂)
    (o₁ : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₀₁) (o₂ : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₀₂) (hal : a₂.length = a₁.length)
    (hn : n ≤ 2 ^ 64) (k j : Nat) :
    RelCT isa (fun s₁ s₂ => k = a₁.length / 16 - j ∧ j < a₁.length / 16 ∧
        VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ j ∧ VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ j)
      (hashChunk (VG.Proof.AesOcb.X86_64.callees v)) fun s₁ s₂ => isa.eval .ne s₁ = isa.eval .ne s₂ ∧
        (isa.eval .ne s₁ = some false → VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ (a₁.length / 16) ∧
          VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ (a₂.length / 16)) ∧
        (isa.eval .ne s₁ = some true → ∃ m < k, ∃ j', m = a₁.length / 16 - j' ∧ j' < a₁.length / 16 ∧
          VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ j' ∧ VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ j') := by
  have L := C₁.lay
  have hDW := C₁.dw
  have hM : a₂.length / 16 = a₁.length / 16 := by rw [hal]
  obtain ⟨M, hMd⟩ : ∃ M, M = a₁.length / 16 := ⟨_, rfl⟩
  obtain ⟨c, hcd⟩ : ∃ c, c = min 8 (M - j) := ⟨_, rfl⟩
  rw [← hMd]
  rw [← hMd] at hM
  by_cases hkj : k = M - j ∧ j < M
  swap
  · exact RelCT.of_false fun s₁ s₂ h => hkj ⟨h.1, h.2.1⟩
  obtain ⟨hk, hjM⟩ := hkj
  have pre : ∀ {ciph : Cipher} {l : Block} {a : List Byte} {s₀ s : State}, VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph l A a s₀ →
      a.length / 16 = M → j < M → VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph l A a s₀ s j →
      WP isa (.seq (.block [VG.Impl.AesOcb.X86_64.ld .r12 .r15 alenO, .alu .cmp .r12 (.imm 8)])
        (.seq (.ite .b (.block []) (.block [.mov .r12 (.imm 8)])) (.seq (.block bufStart) (.loop hashFill .ne)))) s
        (VG.Proof.AesOcb.X86_64.FillInv K W SP D n ciph l A a s₀ j c · c) := fun {ciph l a s₀ s} C hm hj H => by
    have hc : min 8 (a.length / 16 - j) = c := by rw [hm, hcd]
    refine wp_seq_assoc (WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.chunkHead_ok C H (by omega)) fun t ⟨H', h12⟩ => ?_))
    rw [hc] at h12
    exact VG.Proof.AesOcb.X86_64.chunkFill_ok C H' (by omega) (by omega) (by omega) h12
  have bX : ∀ s₁ s₂, (k = M - j ∧ j < M ∧ VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ j ∧
      VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ j) → VG.Proof.AesOcb.X86_64.Both K W SP R N A D nl n tl [.rbx, .rbp] [248] s₁ s₂ :=
    fun s₁ s₂ ⟨_, _, H₁, H₂⟩ => by
      have O₁ := H₁.one C₁ o₁
      have O₂ := H₂.one C₂ o₂
      refine ⟨O₁.env, O₂.env, O₁.sl, O₂.sl, O₁.wr, O₂.wr, fun x hx => ?_, fun d hd => ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · rw [H₁.rbx, H₂.rbx]
        · rw [H₁.rbp, H₂.rbp]
      · simp only [List.mem_singleton] at hd; subst hd
        exact ⟨by decide, by rw [show (248 : Nat) = alenO from rfl, H₁.alen, H₂.alen, hM, hMd]⟩
  have X := (VG.Proof.AesOcb.X86_64.rel_taintC [.rbx, .rbp] [248] hDW hn bX
    (c := .seq (.block [VG.Impl.AesOcb.X86_64.ld .r12 .r15 alenO, .alu .cmp .r12 (.imm 8)])
      (.seq (.ite .b (.block []) (.block [.mov .r12 (.imm 8)])) (.seq (.block bufStart) (.loop hashFill .ne))))
    ⟨_, by taint_decide⟩).wp
    (F₁ := (VG.Proof.AesOcb.X86_64.FillInv K W SP D n ciph₁ l₁ A a₁ s₀₁ j c · c)) (F₂ := (VG.Proof.AesOcb.X86_64.FillInv K W SP D n ciph₂ l₂ A a₂ s₀₂ j c · c))
    fun s₁ s₂ ⟨_, hj, H₁, H₂⟩ => ⟨pre C₁ hMd.symm hj H₁, pre C₂ hM hj H₂⟩
  have hc8 : c ≤ 8 := by omega
  have call : ∀ {ciph : Cipher} {l : Block} {a : List Byte} {s₀ s : State}, VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph l A a s₀ →
      VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₀ → VG.Proof.AesOcb.X86_64.FillInv K W SP D n ciph l A a s₀ j c s c →
      WP isa (callBlocks (VG.Proof.AesOcb.X86_64.callees v).enc [mvr .rdx .r15, addi .rdx bufO, mvr .rcx .r12]) s fun s' =>
        VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s' ∧ s'.gpr .r12 = BitVec.ofNat 64 c := fun {ciph l a s₀ s} C o F => by
    have O := F.one C o
    exact WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encDepth L O.env C.rounds O.sl.rounds
      (VG.Proof.AesOcb.X86_64.bufArgs_ok F.env.r15 F.r12) (dstW L F.env.perm (d := 384) (n := c) (by omega))) fun s' Q => by
      refine ⟨O.step L hDW (O.env.of_saved Q.saved Q.rd Q.wr) Q.wr (Q.frame.sub fun r hr => ?_),
        by rw [Q.saved _ (by decide), F.r12]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, VG.Proof.AesOcb.X86_64.sub_wC (by decide) (by omega)⟩
      · exact ⟨_, by simp, VG.Proof.AesOcb.X86_64.sub_wC (by decide) (by decide)⟩
      · rw [O.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩
  have B := (VG.Proof.AesOcb.X86_64.callBlocks_rel (b := (VG.Proof.AesOcb.X86_64.callees v).enc) v.encOk v.encCt L C₁.rounds hDW hn [] []
    (args := [mvr .rdx .r15, addi .rdx bufO, mvr .rcx .r12]) ⟨_, by taint_decide⟩
    (D' := W + BitVec.ofNat 64 384) (k := c)
    (P := fun s₁ s₂ => True ∧ VG.Proof.AesOcb.X86_64.FillInv K W SP D n ciph₁ l₁ A a₁ s₀₁ j c s₁ c ∧
      VG.Proof.AesOcb.X86_64.FillInv K W SP D n ciph₂ l₂ A a₂ s₀₂ j c s₂ c) fun s₁ s₂ h =>
      ⟨Both.of (h.2.1.one C₁ o₁) (h.2.2.one C₂ o₂), VG.Proof.AesOcb.X86_64.bufArgs_ok h.2.1.env.r15 h.2.1.r12,
        VG.Proof.AesOcb.X86_64.bufArgs_ok h.2.2.env.r15 h.2.2.r12, dstW L h.2.1.env.perm (d := 384) (n := c) (by omega),
        dstW L h.2.2.env.perm (d := 384) (n := c) (by omega)⟩).wp
    (F₁ := fun (s : State) => VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s ∧ s.gpr .r12 = BitVec.ofNat 64 c)
    (F₂ := fun (s : State) => VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s ∧ s.gpr .r12 = BitVec.ofNat 64 c)
    fun s₁ s₂ h => ⟨call C₁ o₁ h.2.1, call C₂ o₂ h.2.2⟩
  have Y := VG.Proof.AesOcb.X86_64.rel_taintC [.r12] [] hDW hn (fun s₁ s₂ (h : True ∧ (VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₁ ∧
      s₁.gpr .r12 = BitVec.ofNat 64 c) ∧ (VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₂ ∧ s₂.gpr .r12 = BitVec.ofNat 64 c)) =>
    (⟨h.2.1.1.env, h.2.2.1.env, h.2.1.1.sl, h.2.2.1.sl, h.2.1.1.wr, h.2.2.1.wr, fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; rw [h.2.1.2, h.2.2.2], fun _ h => (nomatch h)⟩ :
      VG.Proof.AesOcb.X86_64.Both K W SP R N A D nl n tl [.r12] [] s₁ s₂))
    (c := .seq hashSum (.block [VG.Impl.AesOcb.X86_64.ld .rax .r15 alenO, .alu .sub .rax (.reg .r12), st .r15 alenO .rax]))
    ⟨_, by taint_decide⟩
  have T : RelCT isa (fun s₁ s₂ => k = M - j ∧ j < M ∧ VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ j ∧
      VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ j) (hashChunk (VG.Proof.AesOcb.X86_64.callees v)) fun _ _ => True := by
    unfold hashChunk; exact Proof.AesCcm.X86_64.rel_assoc4 (RelCT.seq X (RelCT.seq B Y))
  refine (T.wp (F₁ := fun (t : State) => VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ t (j + c) ∧
      t.zf = some (decide (M - (j + c) = 0)))
    (F₂ := fun (t : State) => VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ t (j + c) ∧ t.zf = some (decide (M - (j + c) = 0)))
    fun s₁ s₂ ⟨_, hj, H₁, H₂⟩ => ⟨?_, ?_⟩).mono (fun _ _ h => h) fun s₁ s₂ ⟨_, ⟨H₁, z₁⟩, ⟨H₂, z₂⟩⟩ => ?_
  · have := VG.Proof.AesOcb.X86_64.hashChunk_ok v C₁ H₁ (by omega)
    rw [← hMd, ← hcd] at this
    exact this
  · have := VG.Proof.AesOcb.X86_64.hashChunk_ok v C₂ H₂ (by omega)
    rw [hM, ← hcd] at this
    exact this
  · rw [eval_ne z₁, eval_ne z₂]
    refine ⟨rfl, fun h => ?_, fun h => ?_⟩
    · have he : j + c = M := by simp at h; omega
      rw [hM, ← he]; exact ⟨H₁, H₂⟩
    · have he : ¬ M - (j + c) = 0 := by simpa using h
      exact ⟨M - (j + c), by omega, j + c, rfl, by omega, H₁, H₂⟩

/-- The call on the block at `W + bufO` keeps the public arguments. -/
theorem callBuf_one (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {s : State}
    (o : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s) :
    WP isa (callBlocks (VG.Proof.AesOcb.X86_64.callees v).enc (oneBlock bufO)) s (VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl) :=
  WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encDepth L o.env hR o.sl.rounds
    (oneBlock_ok o.env.r15 bufO (by decide)) (dstW L o.env.perm (d := bufO) (n := 1) (by decide))) fun s' Q => by
    refine o.step L hDW (o.env.of_saved Q.saved Q.rd Q.wr) Q.wr (Q.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, VG.Proof.AesOcb.X86_64.sub_wC (by decide) (by decide)⟩
    · exact ⟨_, by simp, VG.Proof.AesOcb.X86_64.sub_wC (by decide) (by decide)⟩
    · rw [o.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩

/-- `HASH` in two runs, from the starts `s₀₁` and `s₀₂` of the same length of associated data. -/
theorem hash_rel (v : BlocksImpl) {K W SP D : Addr} {n R : Nat} {ciph₁ ciph₂ : Cipher} {l₁ l₂ : Block} {A : Addr}
    {a₁ a₂ : List Byte} {s₀₁ s₀₂ : State} {N : Addr} {nl tl : Nat}
    (C₁ : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph₁ l₁ A a₁ s₀₁) (C₂ : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R ciph₂ l₂ A a₂ s₀₂)
    (o₁ : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₀₁) (o₂ : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₀₂) (hal : a₂.length = a₁.length)
    (hn : n ≤ 2 ^ 64)
    (halen₁ : s₀₁.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a₁.length)
    (halen₂ : s₀₂.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 a₂.length)
    (hl0₁ : blockAtMem s₀₁.mem (W + BitVec.ofNat 64 l0O) = lAt l₁ 0)
    (hl0₂ : blockAtMem s₀₂.mem (W + BitVec.ofNat 64 l0O) = lAt l₂ 0) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀₁ ∧ s₂ = s₀₂) (Impl.AesOcb.X86_64.hash (VG.Proof.AesOcb.X86_64.callees v)) fun _ _ => True := by
  have L := C₁.lay
  have hDW := C₁.dw
  have hM : a₂.length / 16 = a₁.length / 16 := by rw [hal]
  have hr : a₂.length % 16 = a₁.length % 16 := by rw [hal]
  have haad₁ := o₁.sl.aad
  have haad₂ := o₂.sl.aad
  -- The first block.
  have a := (VG.Proof.AesOcb.X86_64.rel_flagsC [] [248] hDW hn (fun s₁ s₂ (h : s₁ = s₀₁ ∧ s₂ = s₀₂) => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨o₁.env, o₂.env, o₁.sl, o₂.sl, o₁.wr, o₂.wr, fun _ h => (nomatch h), fun d hd => by
        simp only [List.mem_singleton] at hd; subst hd
        exact ⟨by decide, by rw [show (248 : Nat) = alenO from rfl, halen₁, halen₂, hal]⟩⟩)
    (c := .block (zero16 sumO ++ zero16 ohO ++
      [VG.Impl.AesOcb.X86_64.ld .rbx .r15 aadO, VG.Impl.AesOcb.X86_64.ld .rax .r15 alenO, mvr .rcx .rax, .alu .and .rcx (.imm 15),
       st .r15 tmpO .rcx, .shift .shr .rax 4, st .r15 alenO .rax, .mov .rbp (.imm 1),
       .alu .test .rax (.reg .rax)])) ⟨_, by taint_decide⟩).wp
    (F₁ := fun (s : State) => VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s 0 ∧ s.zf = some (decide (a₁.length / 16 = 0)))
    (F₂ := fun (s : State) => VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s 0 ∧ s.zf = some (decide (a₂.length / 16 = 0)))
    fun s₁ s₂ h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨VG.Proof.AesOcb.X86_64.hashHead_ok C₁ o₁.env haad₁ halen₁ hl0₁, VG.Proof.AesOcb.X86_64.hashHead_ok C₂ o₂.env haad₂ halen₂ hl0₂⟩
  -- The chunks.
  have lp : RelCT isa (fun s₁ s₂ => ∃ j, a₁.length / 16 - 0 = a₁.length / 16 - j ∧ j < a₁.length / 16 ∧
      VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ j ∧ VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ j)
      (.loop (hashChunk (VG.Proof.AesOcb.X86_64.callees v)) .ne) fun _ _ => True :=
    (RelCT.loop (Q := fun s₁ s₂ => VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ (a₁.length / 16) ∧
        VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ (a₂.length / 16))
      (fun k s₁ s₂ => ∃ j, k = a₁.length / 16 - j ∧ j < a₁.length / 16 ∧
        VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ j ∧ VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ j)
      (fun k => RelCT.exists_ fun j => VG.Proof.AesOcb.X86_64.chunk_rel v C₁ C₂ o₁ o₂ hal hn k j) _).mono (fun _ _ h => h)
      fun _ _ _ => trivial
  have i₁ := RelCT.ite (M := isa) (c := .e) (t := .block []) (e := .loop (hashChunk (VG.Proof.AesOcb.X86_64.callees v)) .ne)
    (Q := fun _ _ => True)
    (P := fun s₁ s₂ => (s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf) ∧
      (VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ 0 ∧ s₁.zf = some (decide (a₁.length / 16 = 0))) ∧
      (VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ 0 ∧ s₂.zf = some (decide (a₂.length / 16 = 0))))
    (fun s₁ s₂ h => Proof.AesCcm.X86_64.eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) (by
      by_cases h0 : a₁.length / 16 = 0
      · refine RelCT.of_false fun s₁ s₂ h => ?_
        have := (eval_e h.1.2.1.2).symm.trans h.2
        simp [h0] at this
      · exact lp.mono (fun s₁ s₂ h => ⟨0, rfl, Nat.pos_of_ne_zero h0, h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h)
  have X := (RelCT.seq a i₁).wp
    (F₁ := fun s => VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s (a₁.length / 16))
    (F₂ := fun s => VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s (a₂.length / 16)) fun s₁ s₂ h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨VG.Proof.AesOcb.X86_64.hashHI_ok v C₁ o₁.env haad₁ halen₁ hl0₁, VG.Proof.AesOcb.X86_64.hashHI_ok v C₂ o₂.env haad₂ halen₂ hl0₂⟩
  -- The rest.
  have t₁ := (VG.Proof.AesOcb.X86_64.rel_flagsC [] [112] hDW hn (fun s₁ s₂ (h : True ∧ VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ (a₁.length / 16) ∧
      VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ (a₂.length / 16)) => by
      have O₁ := h.2.1.one C₁ o₁
      have O₂ := h.2.2.one C₂ o₂
      exact ⟨O₁.env, O₂.env, O₁.sl, O₂.sl, O₁.wr, O₂.wr, fun _ h => (nomatch h), fun d hd => by
        simp only [List.mem_singleton] at hd; subst hd
        exact ⟨by decide, by rw [show (112 : Nat) = tmpO from rfl, h.2.1.rest, h.2.2.rest, hr]⟩⟩)
    (c := .block [VG.Impl.AesOcb.X86_64.ld .r12 .r15 tmpO, .alu .test .r12 (.reg .r12)]) ⟨_, by taint_decide⟩).wp
    (F₁ := fun (t : State) => VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ t (a₁.length / 16) ∧
      t.gpr .r12 = BitVec.ofNat 64 (a₁.length % 16) ∧ t.zf = some (decide (a₁.length % 16 = 0)))
    (F₂ := fun (t : State) => VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ t (a₂.length / 16) ∧
      t.gpr .r12 = BitVec.ofNat 64 (a₂.length % 16) ∧ t.zf = some (decide (a₂.length % 16 = 0)))
    fun s₁ s₂ h => ⟨VG.Proof.AesOcb.X86_64.tailHead_ok h.2.1, VG.Proof.AesOcb.X86_64.tailHead_ok h.2.2⟩
  have rr : (0 < a₁.length % 16) → RelCT isa (fun s₁ s₂ =>
      (VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ (a₁.length / 16) ∧ s₁.gpr .r12 = BitVec.ofNat 64 (a₁.length % 16)) ∧
      (VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ (a₂.length / 16) ∧ s₂.gpr .r12 = BitVec.ofNat 64 (a₂.length % 16)))
      (hashRest (VG.Proof.AesOcb.X86_64.callees v)) fun _ _ => True := fun hr0 => by
    have p := (VG.Proof.AesOcb.X86_64.rel_taintC [.rbx, .r12] [] hDW hn (fun s₁ s₂ (h :
        (VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ (a₁.length / 16) ∧ s₁.gpr .r12 = BitVec.ofNat 64 (a₁.length % 16)) ∧
        (VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ (a₂.length / 16) ∧ s₂.gpr .r12 = BitVec.ofNat 64 (a₂.length % 16))) =>
      (⟨(h.1.1.one C₁ o₁).env, (h.2.1.one C₂ o₂).env,
        (h.1.1.one C₁ o₁).sl, (h.2.1.one C₂ o₂).sl, (h.1.1.one C₁ o₁).wr, (h.2.1.one C₂ o₂).wr, fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · rw [h.1.1.rbx, h.2.1.rbx, hM]
          · rw [h.1.2, h.2.2, hr], fun _ h => (nomatch h)⟩ : VG.Proof.AesOcb.X86_64.Both K W SP R N A D nl n tl [.rbx, .r12] [] s₁ s₂))
      (c := .seq (.block (xor16 .r14 240 ohO)) (.seq (padTo bufO) (.block (xor16 .r15 ohO bufO))))
      ⟨_, by taint_decide⟩).wp (F₁ := VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl) (F₂ := VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl)
      fun s₁ s₂ h => ⟨VG.Proof.AesOcb.X86_64.hashRestPre_one C₁ o₁ h.1.1 hr0 h.1.2, VG.Proof.AesOcb.X86_64.hashRestPre_one C₂ o₂ h.2.1 (by omega) h.2.2⟩
    have c := (VG.Proof.AesOcb.X86_64.callBlocks_rel (b := (VG.Proof.AesOcb.X86_64.callees v).enc) v.encOk v.encCt L C₁.rounds hDW hn [] [] (args := oneBlock bufO)
      ⟨_, by taint_decide⟩ (D' := W + BitVec.ofNat 64 bufO) (k := 1)
      (P := fun s₁ s₂ => True ∧ VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₁ ∧ VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₂) fun s₁ s₂ h =>
        ⟨Both.of h.2.1 h.2.2, oneBlock_ok h.2.1.env.r15 bufO (by decide), oneBlock_ok h.2.2.env.r15 bufO (by decide),
          dstW L h.2.1.env.perm (by decide), dstW L h.2.2.env.perm (by decide)⟩).wp
      (F₁ := VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl) (F₂ := VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl)
      fun s₁ s₂ h => ⟨VG.Proof.AesOcb.X86_64.callBuf_one v L C₁.rounds hDW h.2.1, VG.Proof.AesOcb.X86_64.callBuf_one v L C₁.rounds hDW h.2.2⟩
    have e := VG.Proof.AesOcb.X86_64.rel_taintC [] [] hDW hn (fun s₁ s₂ (h : True ∧ VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₁ ∧
      VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s₂) => Both.of h.2.1 h.2.2) (c := .block (xor16 .r15 bufO sumO)) ⟨_, by taint_decide⟩
    unfold hashRest
    exact Proof.AesCcm.X86_64.rel_assoc3 (RelCT.seq p (RelCT.seq c e))
  have i₂ := RelCT.ite (M := isa) (c := .e) (t := .block []) (e := hashRest (VG.Proof.AesOcb.X86_64.callees v)) (Q := fun _ _ => True)
    (P := fun s₁ s₂ => (s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf) ∧
      (VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₁ l₁ A a₁ s₀₁ s₁ (a₁.length / 16) ∧ s₁.gpr .r12 = BitVec.ofNat 64 (a₁.length % 16) ∧
        s₁.zf = some (decide (a₁.length % 16 = 0))) ∧
      (VG.Proof.AesOcb.X86_64.HInv K W SP D n ciph₂ l₂ A a₂ s₀₂ s₂ (a₂.length / 16) ∧ s₂.gpr .r12 = BitVec.ofNat 64 (a₂.length % 16) ∧
        s₂.zf = some (decide (a₂.length % 16 = 0))))
    (fun s₁ s₂ h => Proof.AesCcm.X86_64.eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) (by
      by_cases h0 : a₁.length % 16 = 0
      · refine RelCT.of_false fun s₁ s₂ h => ?_
        have := (eval_e h.1.2.1.2.2).symm.trans h.2
        simp [h0] at this
      · exact (rr (Nat.pos_of_ne_zero h0)).mono (fun s₁ s₂ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.1⟩, ⟨h.1.2.2.1, h.1.2.2.2.1⟩⟩)
          fun _ _ h => h)
  unfold Impl.AesOcb.X86_64.hash
  exact Proof.AesCcm.X86_64.rel_assoc (RelCT.seq X (RelCT.seq t₁ i₂))

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.SealCT`. -/
section

/-!
# AES-OCB on x86-64: `vg_aes_ocb_seal` is constant time

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments are related piece by piece: the entry by the taint analysis from
the public registers, once the first instruction has loaded `W` (`entry_rel`),
then `Offset_0`, `HASH`, the data and the tag (`nonce_rel`, `hash_rel`,
`bodySeal_rel`, `tag_rel`; `front_rel`), each run satisfying what correctness
says between them (`RelCT.wp`).

The taint analysis knows `W` as the second writable region, as it is for
`open`; `seal` may write `tag` too, before `W`, but its `front` does not, and
runs the same from its states with `tag` only readable (`rel_narrow`). The
copy of the tag and `restore` are related by the taint analysis from the
registers that correctness says agree (`sealTail_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append length_bytesAt bytesAt_frame in_off add_ofNat_assoc)

/-- A run after `Offset_0`: what `HASH` needs. -/
structure NRun (K W SP N A D : Addr) (R nl al n tl : Nat) (s₀ s : State) : Prop where
  C : VG.Proof.AesOcb.X86_64.HCtx K W SP D n R (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) A (bytesAt s₀.mem A al) s
  one : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s
  alen : s.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 (bytesAt s₀.mem A al).length
  l0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s₀.mem K) 0

/-- `Offset_0`, after `entry`. -/
theorem nonce_nrun (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Ar : VG.Proof.AesOcb.X86_64.Args s K W SP N A D R nl al n tl T) (hw : s.wr = [⟨D, n⟩, ⟨W, 2560⟩]) {s₁ : State}
    (P₁ : EntryPost K W SP R N A D nl al n tl T s s₁) :
    WP isa (nonce (VG.Proof.AesOcb.X86_64.callees v)) s₁ (VG.Proof.AesOcb.X86_64.NRun K W SP N A D R nl al n tl s) := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 256 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  have eK : ctxCiph s₁.mem K R = ctxCiph s.mem K R := by
    unfold ctxCiph
    rw [VG.Proof.AesCcm.X86_64.bytesAt_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))) (by omega)]
  have eL : ctxLstar s₁.mem K = ctxLstar s.mem K := VG.Proof.AesOcb.X86_64.blockAtMem_frame P₁.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (L.k_w.sub_left (Lay.kSub (by decide))).sub_right (Lay.wSub (by decide)))
  have eB : ∀ {P : Addr} {k : Nat}, Buf W SP s P k → bytesAt s₁.mem P k = bytesAt s.mem P k := fun hP =>
    VG.Proof.AesCcm.X86_64.bytesAt_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)
  refine WP.mono (VG.Proof.AesOcb.X86_64.nonce_ok v L P₁.env Ar.rounds P₁.slots.rounds P₁.slots.nonce P₁.slots.nlen P₁.slots.tl
    Ar.n1 Ar.n15 (by have := Ar.t16; omega) (Ar.nonce.of_eq P₁.rd P₁.wr) Ar.data.k Ar.data.w) fun s₂ P₂ => ?_
  have F₂ : Frame (mutR W SP D n) s₁.mem s₂.mem := VG.Proof.AesOcb.X86_64.nonceR_mut P₂.frame
  have S₂ := Slots.of_mut L Ar.data.w F₂ P₁.slots
  have c₂ : ctxCiph s₂.mem K R = ctxCiph s.mem K R := (VG.Proof.AesOcb.X86_64.ctxCiph_mut L Ar.data.k F₂ Ar.rounds).trans eK
  have l₂ : ctxLstar s₂.mem K = ctxLstar s.mem K := (VG.Proof.AesOcb.X86_64.lstar_mut L Ar.data.k F₂).trans eL
  have a₂ : bytesAt s₂.mem A al = bytesAt s.mem A al := (VG.Proof.AesOcb.X86_64.buf_mut Ar.aad Ar.ad F₂).trans (eB Ar.aad)
  exact
    { C := { lay := L, rounds := Ar.rounds, ciph := c₂, lstar := l₂
             buf := by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact Ar.aad.of_eq (P₂.rd.trans P₁.rd) (P₂.wr.trans P₁.wr)
             aad := by rw [VG.Proof.AesCcm.X86_64.length_bytesAt, a₂]
             ad := by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact Ar.ad
             kd := Ar.data.k, dw := Ar.data.w, rnd := S₂.rounds
             short := by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact Ar.aad.lt }
      one := ⟨P₂.env, S₂, P₂.wr.trans (P₁.wr.trans hw)⟩
      alen := by rw [P₂.alen, P₁.alen, VG.Proof.AesCcm.X86_64.length_bytesAt]
      l0 := by rw [P₂.keep (by decide) (by decide), P₁.l0] }

/-- Two runs of the same public arguments: `seal`'s and `open`'s inputs. -/
structure Two (s₀ s₀' : State) (K W SP N A D : Addr) (R nl al n tl : Nat) (T : Addr) : Prop where
  ar : VG.Proof.AesOcb.X86_64.Args s₀ K W SP N A D R nl al n tl T
  ar' : VG.Proof.AesOcb.X86_64.Args s₀' K W SP N A D R nl al n tl T
  sp : s₀.gpr .rsp = SP
  sp' : s₀'.gpr .rsp = SP
  dd : s₀.mem.readW (SP + BitVec.ofNat 64 8) 64 = D
  dd' : s₀'.mem.readW (SP + BitVec.ofNat 64 8) 64 = D
  nn : s₀.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n
  nn' : s₀'.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n
  tg : s₀.mem.readW (SP + BitVec.ofNat 64 24) 64 = T
  tg' : s₀'.mem.readW (SP + BitVec.ofNat 64 24) 64 = T
  tt : s₀.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl
  tt' : s₀'.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl
  ww : s₀.mem.readW (SP + BitVec.ofNat 64 40) 64 = W
  ww' : s₀'.mem.readW (SP + BitVec.ofNat 64 40) 64 = W
  di : s₀.gpr .rdi = K
  di' : s₀'.gpr .rdi = K
  si : s₀.gpr .rsi = BitVec.ofNat 64 R
  si' : s₀'.gpr .rsi = BitVec.ofNat 64 R
  dx : s₀.gpr .rdx = N
  dx' : s₀'.gpr .rdx = N
  cx : s₀.gpr .rcx = BitVec.ofNat 64 nl
  cx' : s₀'.gpr .rcx = BitVec.ofNat 64 nl
  r8 : s₀.gpr .r8 = A
  r8' : s₀'.gpr .r8 = A
  r9 : s₀.gpr .r9 = BitVec.ofNat 64 al
  r9' : s₀'.gpr .r9 = BitVec.ofNat 64 al

section
variable {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
  (Tw : VG.Proof.AesOcb.X86_64.Two s₀ s₀' K W SP N A D R nl al n tl T)
include Tw

/-- What `entry` leaves, in each run. -/
theorem Two.entry₁ : WP isa (.block VG.Impl.AesOcb.X86_64.entry) s₀ (EntryPost K W SP R N A D nl al n tl T s₀) := by
  obtain ⟨s₁, run₁, P₁⟩ := VG.Proof.AesOcb.X86_64.entry_ok Tw.ar.lay Tw.ar.perm Tw.sp Tw.ar.args Tw.ar.argsW Tw.dd Tw.nn Tw.tg Tw.tt Tw.ww
    Tw.di Tw.si Tw.dx Tw.cx Tw.r8 Tw.r9
  exact WP.of_runBlock ⟨s₁, run₁, P₁⟩

theorem Two.entry₂ : WP isa (.block VG.Impl.AesOcb.X86_64.entry) s₀' (EntryPost K W SP R N A D nl al n tl T s₀') := by
  obtain ⟨s₁, run₁, P₁⟩ := VG.Proof.AesOcb.X86_64.entry_ok Tw.ar'.lay Tw.ar'.perm Tw.sp' Tw.ar'.args Tw.ar'.argsW Tw.dd' Tw.nn' Tw.tg'
    Tw.tt' Tw.ww' Tw.di' Tw.si' Tw.dx' Tw.cx' Tw.r8' Tw.r9'
  exact WP.of_runBlock ⟨s₁, run₁, P₁⟩

/-- `entry` in two runs: the first instruction loads `W` from the stack, the
rest passes the taint analysis from the public registers. -/
theorem entry_rel : RelCT isa (fun a b => a = s₀ ∧ b = s₀') (.block VG.Impl.AesOcb.X86_64.entry) fun _ _ => True := by
  have a₄₀ := in_off (d := 32) (n := 8) Tw.ar.args (by decide) (by decide)
  have a₄₀' := in_off (d := 32) (n := 8) Tw.ar'.args (by decide) (by decide)
  rw [add_ofNat_assoc] at a₄₀ a₄₀'
  have first : ∀ {s : State}, s.gpr .rsp = SP → s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W →
      InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 (8 + 32)) 8 →
      WP isa (.block [.mov .rax (.mem (at_ .rsp 40))]) s fun t =>
        t.gpr .rax = W ∧ ∀ r, r ≠ .rax → t.gpr r = s.gpr r := fun hsp hW ha =>
    WP.of_runBlock ⟨_, by orun [hsp, hW, ha], by simp only [gpr_setReg, ite_true],
      fun r h => by simp only [gpr_setReg, h, ite_false]⟩
  have e : VG.Impl.AesOcb.X86_64.entry = [.mov .rax (.mem (at_ .rsp 40))] ++ (save .rax ++
      [mvr .r15 .rax, mvr .r14 .rdi, st .r15 rndO .rsi, st .r15 nO .rdx, st .r15 nlO .rcx,
       st .r15 aadO .r8, st .r15 alenO .r9,
       VG.Impl.AesOcb.X86_64.ld .rax .rsp 8, st .r15 dataO .rax, VG.Impl.AesOcb.X86_64.ld .rax .rsp 16, st .r15 lenO .rax, VG.Impl.AesOcb.X86_64.ld .rax .rsp 32,
       st .r15 tlO .rax, VG.Impl.AesOcb.X86_64.ld .rax .rsp 24, st .r15 tgO .rax] ++ lsetup ++ zero16 ckO) := by
    simp only [VG.Impl.AesOcb.X86_64.entry, List.append_assoc]
  rw [e]
  refine RelCT.block_append ?_
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (at_ .rsp 40))]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; rw [Tw.sp, Tw.sp']) hA).wp
    (F₁ := fun (t : State) => t.gpr .rax = W ∧ ∀ r, r ≠ .rax → t.gpr r = s₀.gpr r)
    (F₂ := fun (t : State) => t.gpr .rax = W ∧ ∀ r, r ≠ .rax → t.gpr r = s₀'.gpr r) fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab; exact ⟨first Tw.sp Tw.ww a₄₀, first Tw.sp' Tw.ww' a₄₀'⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block (save .rax ++ [mvr .r15 .rax, mvr .r14 .rdi, st .r15 rndO .rsi, st .r15 nO .rdx, st .r15 nlO .rcx,
       st .r15 aadO .r8, st .r15 alenO .r9,
       VG.Impl.AesOcb.X86_64.ld .rax .rsp 8, st .r15 dataO .rax, VG.Impl.AesOcb.X86_64.ld .rax .rsp 16, st .r15 lenO .rax, VG.Impl.AesOcb.X86_64.ld .rax .rsp 32,
       st .r15 tlO .rax, VG.Impl.AesOcb.X86_64.ld .rax .rsp 24, st .r15 tgO .rax] ++ lsetup ++ zero16 ckO)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have b := RelCT.taint (A := taint) (P := fun (a b : State) => True ∧
      (a.gpr .rax = W ∧ ∀ r, r ≠ .rax → a.gpr r = s₀.gpr r) ∧ (b.gpr .rax = W ∧ ∀ r, r ≠ .rax → b.gpr r = s₀'.gpr r))
    _ (fun a b ⟨_, ha, hb⟩ => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [ha.1, hb.1]
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.di, Tw.di']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.si, Tw.si']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.dx, Tw.dx']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.cx, Tw.cx']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.r8, Tw.r8']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.r9, Tw.r9']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.sp, Tw.sp']) hB
  exact RelCT.seq a b

variable (hw : s₀.wr = [⟨D, n⟩, ⟨W, 2560⟩]) (hw' : s₀'.wr = [⟨D, n⟩, ⟨W, 2560⟩])
include hw hw'

/-- `entry`, `Offset_0` and `HASH` in two runs. -/
theorem pre_rel (v : BlocksImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (.seq (.block VG.Impl.AesOcb.X86_64.entry) (.seq (nonce (VG.Proof.AesOcb.X86_64.callees v)) (hash (VG.Proof.AesOcb.X86_64.callees v))))
      fun _ _ => True := by
  have L := Tw.ar.lay
  have hDW := Tw.ar.data.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt Tw.ar.data.lt
  have e := (VG.Proof.AesOcb.X86_64.entry_rel Tw).wp (F₁ := EntryPost K W SP R N A D nl al n tl T s₀)
    (F₂ := EntryPost K W SP R N A D nl al n tl T s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨Tw.entry₁, Tw.entry₂⟩
  have nn := (VG.Proof.AesOcb.X86_64.nonce_rel v L Tw.ar.rounds hDW hn Tw.ar.n1 Tw.ar.n15 (by have := Tw.ar.t16; omega)
    (P := fun a b => True ∧ EntryPost K W SP R N A D nl al n tl T s₀ a ∧ EntryPost K W SP R N A D nl al n tl T s₀' b)
    fun a b h => ⟨⟨h.2.1.env, h.2.1.slots, h.2.1.wr.trans hw⟩, ⟨h.2.2.env, h.2.2.slots, h.2.2.wr.trans hw'⟩,
      Tw.ar.nonce.of_eq h.2.1.rd h.2.1.wr, Tw.ar'.nonce.of_eq h.2.2.rd h.2.2.wr⟩).wp
    (F₁ := VG.Proof.AesOcb.X86_64.NRun K W SP N A D R nl al n tl s₀) (F₂ := VG.Proof.AesOcb.X86_64.NRun K W SP N A D R nl al n tl s₀')
    fun a b h => ⟨VG.Proof.AesOcb.X86_64.nonce_nrun v Tw.ar hw h.2.1, VG.Proof.AesOcb.X86_64.nonce_nrun v Tw.ar' hw' h.2.2⟩
  have hh := VG.Proof.AesOcb.X86_64.rel_of_pt (P := fun a b => True ∧ VG.Proof.AesOcb.X86_64.NRun K W SP N A D R nl al n tl s₀ a ∧
      VG.Proof.AesOcb.X86_64.NRun K W SP N A D R nl al n tl s₀' b) (Q := fun _ _ => True) (c := hash (VG.Proof.AesOcb.X86_64.callees v)) fun a b h =>
    VG.Proof.AesOcb.X86_64.hash_rel v h.2.1.C h.2.2.C h.2.1.one h.2.2.one (by simp only [VG.Proof.AesCcm.X86_64.length_bytesAt]) hn h.2.1.alen h.2.2.alen
      h.2.1.l0 h.2.2.l0
  exact RelCT.seq e (RelCT.seq nn hh)

end

/-- A run with the public arguments and the address of the tag at `W + tgO`,
which it may read. -/
def OneT (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (T : Addr) (s : State) : Prop :=
  VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s ∧ s.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T ∧
    Covers [⟨T, tl⟩] (s.rd ++ s.wr)

/-- What `pre_wp'` leaves is what `body` needs. -/
theorem brun_of {s : State} {s' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Ar : VG.Proof.AesOcb.X86_64.Args s K W SP N A D R nl al n tl T) (hw : s.wr = [⟨D, n⟩, ⟨W, 2560⟩])
    (P : VG.Proof.AesOcb.X86_64.Pre K W SP N A D R nl al n tl T s s') : VG.Proof.AesOcb.X86_64.BRun K W SP R N A D nl n tl s' :=
  ⟨⟨P.env, P.slots, P.wr.trans hw⟩, Ar.data.of_eq P.rd P.wr, ⟨_, P.l0⟩, P.ofs.trans P.o0.symm⟩

/-- `body` keeps the public arguments and the address of the tag. -/
theorem body_oneT (v : BlocksImpl) (enc : Bool) {σ s : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Ar : VG.Proof.AesOcb.X86_64.Args σ K W SP N A D R nl al n tl T) (hw : σ.wr = [⟨D, n⟩, ⟨W, 2560⟩])
    (P : VG.Proof.AesOcb.X86_64.Pre K W SP N A D R nl al n tl T σ s) :
    WP isa (VG.Impl.AesOcb.X86_64.body (VG.Proof.AesOcb.X86_64.callees v) enc) s (VG.Proof.AesOcb.X86_64.OneT K W SP R N A D nl n tl T) := by
  have L := Ar.lay
  have k : ∀ {t : State}, Env K W SP t → t.rd = s.rd → t.wr = s.wr → Frame (VG.Proof.AesOcb.X86_64.bodyR W SP D n) s.mem t.mem →
      VG.Proof.AesOcb.X86_64.OneT K W SP R N A D nl n tl T t := fun E hr' hw' f =>
    ⟨(VG.Proof.AesOcb.X86_64.brun_of Ar hw P).1.step L Ar.data.w E hw' (VG.Proof.AesOcb.X86_64.bodyR_mut f),
      by rw [VG.Proof.AesOcb.X86_64.kept_read L Ar.data.w (VG.Proof.AesOcb.X86_64.bodyR_mut f) (d := tgO) (by decide), P.tg],
      by rw [hr', hw', P.rd, P.wr]; exact Ar.tag.rd⟩
  cases enc
  · exact WP.mono (VG.Proof.AesOcb.X86_64.bodyOpen_ok v L P.env Ar.rounds P.slots.rounds (Ar.data.of_eq P.rd P.wr) P.slots.data
      P.slots.len P.ofs P.o0 P.ck (by rw [P.l0, P.lstar])) fun t B => k B.env B.rd B.wr B.frame
  · exact WP.mono (VG.Proof.AesOcb.X86_64.bodySeal_ok v L P.env Ar.rounds P.slots.rounds (Ar.data.of_eq P.rd P.wr) P.slots.data
      P.slots.len P.ofs P.o0 P.ck (by rw [P.l0, P.lstar])) fun t B => k B.env B.rd B.wr B.frame

/-- The tag keeps the public arguments and the address of the tag. -/
theorem tag_oneT (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} {T : Addr} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {d : Nat} (hd : d = tagO ∨ d = t2O) {s : State}
    (o : VG.Proof.AesOcb.X86_64.OneT K W SP R N A D nl n tl T s) : WP isa (tag (VG.Proof.AesOcb.X86_64.callees v) d) s (VG.Proof.AesOcb.X86_64.OneT K W SP R N A D nl n tl T) :=
  WP.mono (VG.Proof.AesOcb.X86_64.tag_ok v L o.1.env hR o.1.sl.rounds hd) fun t P =>
    have f := VG.Proof.AesOcb.X86_64.tagR_mut (D := D) (n := n) (by rcases hd with rfl | rfl <;> decide) P.frame
    ⟨o.1.step L hDW P.env P.wr f, by rw [VG.Proof.AesOcb.X86_64.kept_read L hDW f (d := tgO) (by decide), o.2.1],
      by rw [P.rd, P.wr]; exact o.2.2⟩

/-- `front` in two runs from states whose writable regions are the data and
`W`. -/
theorem front_rel {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Tw : VG.Proof.AesOcb.X86_64.Two s₀ s₀' K W SP N A D R nl al n tl T) (hw : s₀.wr = [⟨D, n⟩, ⟨W, 2560⟩])
    (hw' : s₀'.wr = [⟨D, n⟩, ⟨W, 2560⟩]) (v : BlocksImpl) (enc : Bool) {d : Nat} (hd : d = tagO ∨ d = t2O) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (front (VG.Proof.AesOcb.X86_64.callees v) enc d) fun a b =>
      True ∧ VG.Proof.AesOcb.X86_64.OneT K W SP R N A D nl n tl T a ∧ VG.Proof.AesOcb.X86_64.OneT K W SP R N A D nl n tl T b := by
  have L := Tw.ar.lay
  have hDW := Tw.ar.data.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt Tw.ar.data.lt
  have pre := (VG.Proof.AesOcb.X86_64.pre_rel Tw hw hw' v).wp (F₁ := VG.Proof.AesOcb.X86_64.Pre K W SP N A D R nl al n tl T s₀)
    (F₂ := VG.Proof.AesOcb.X86_64.Pre K W SP N A D R nl al n tl T s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨VG.Proof.AesOcb.X86_64.pre_wp' v Tw.ar Tw.sp Tw.dd Tw.nn Tw.tg Tw.tt Tw.ww Tw.di Tw.si Tw.dx Tw.cx Tw.r8 Tw.r9,
        VG.Proof.AesOcb.X86_64.pre_wp' v Tw.ar' Tw.sp' Tw.dd' Tw.nn' Tw.tg' Tw.tt' Tw.ww' Tw.di' Tw.si' Tw.dx' Tw.cx' Tw.r8' Tw.r9'⟩
  have bb : RelCT isa (fun a b => True ∧ VG.Proof.AesOcb.X86_64.Pre K W SP N A D R nl al n tl T s₀ a ∧ VG.Proof.AesOcb.X86_64.Pre K W SP N A D R nl al n tl T s₀' b)
      (VG.Impl.AesOcb.X86_64.body (VG.Proof.AesOcb.X86_64.callees v) enc) fun _ _ => True := by
    cases enc
    · exact VG.Proof.AesOcb.X86_64.bodyOpen_rel v L Tw.ar.rounds hDW Tw.ar.data.lt fun a b h => ⟨VG.Proof.AesOcb.X86_64.brun_of Tw.ar hw h.2.1, VG.Proof.AesOcb.X86_64.brun_of Tw.ar' hw' h.2.2⟩
    · exact VG.Proof.AesOcb.X86_64.bodySeal_rel v L Tw.ar.rounds hDW Tw.ar.data.lt fun a b h => ⟨VG.Proof.AesOcb.X86_64.brun_of Tw.ar hw h.2.1, VG.Proof.AesOcb.X86_64.brun_of Tw.ar' hw' h.2.2⟩
  have bb' := bb.wp (F₁ := VG.Proof.AesOcb.X86_64.OneT K W SP R N A D nl n tl T) (F₂ := VG.Proof.AesOcb.X86_64.OneT K W SP R N A D nl n tl T)
    fun a b h => ⟨VG.Proof.AesOcb.X86_64.body_oneT v enc Tw.ar hw h.2.1, VG.Proof.AesOcb.X86_64.body_oneT v enc Tw.ar' hw' h.2.2⟩
  have tt := (VG.Proof.AesOcb.X86_64.tag_rel v L Tw.ar.rounds hDW hn (d := d) hd
    (P := fun a b => True ∧ VG.Proof.AesOcb.X86_64.OneT K W SP R N A D nl n tl T a ∧ VG.Proof.AesOcb.X86_64.OneT K W SP R N A D nl n tl T b)
    fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩).wp
    (F₁ := VG.Proof.AesOcb.X86_64.OneT K W SP R N A D nl n tl T) (F₂ := VG.Proof.AesOcb.X86_64.OneT K W SP R N A D nl n tl T)
    fun a b h => ⟨VG.Proof.AesOcb.X86_64.tag_oneT v L Tw.ar.rounds hDW hd h.2.1, VG.Proof.AesOcb.X86_64.tag_oneT v L Tw.ar.rounds hDW hd h.2.2⟩
  unfold front
  exact Proof.AesCcm.X86_64.rel_assoc3 (RelCT.seq pre (RelCT.seq bb' tt))

/-! ## Moving the tag to the regions read only -/

/-- Two runs, as the runs from their states with the writable regions `ex`
moved to those they read only, and only the writable regions `w` left: the
code runs the same from both (`Exec.widen`, `Exec.det`). -/
theorem rel_narrow {P Q : State → State → Prop} {c : Prog isa} (ex w : List Region)
    (h : RelCT isa (fun σ₁ σ₂ => ∃ s₁ s₂, P s₁ s₂ ∧ σ₁ = s₁.withRegions (s₁.rd ++ ex) w ∧
      σ₂ = s₂.withRegions (s₂.rd ++ ex) w) c Q)
    (hP : ∀ s₁ s₂, P s₁ s₂ → (Covers (ex ++ w) s₁.wr ∧ Covers w s₁.wr ∧
        ∃ t s', Exec isa c (s₁.withRegions (s₁.rd ++ ex) w) t s') ∧
      (Covers (ex ++ w) s₂.wr ∧ Covers w s₂.wr ∧ ∃ t s', Exec isa c (s₂.withRegions (s₂.rd ++ ex) w) t s')) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨⟨c₁, w₁, u₁, σ₁', n₁⟩, ⟨c₂, w₂, u₂, σ₂', n₂⟩⟩ := hP _ _ hp
  have widen : ∀ {s σ' : State} {u : List Leak}, Covers (ex ++ w) s.wr → Covers w s.wr →
      Exec isa c (s.withRegions (s.rd ++ ex) w) u σ' → Exec isa c s u (σ'.withRegions s.rd s.wr) :=
    fun {s σ' u} hc hw n => by
    have m := Exec.widen n (rd := s.rd) (wr := s.wr)
      (by simp only [State.withRegions_rd, State.withRegions_wr, List.append_assoc]
          exact Covers.append (Covers.refl _) hc)
      (by simpa only [State.withRegions_wr] using hw)
    rwa [State.withRegions_withRegions, State.withRegions_self] at m
  obtain ⟨rfl, -⟩ := Exec.det e₁ (widen c₁ w₁ n₁)
  obtain ⟨rfl, -⟩ := Exec.det e₂ (widen c₂ w₂ n₂)
  exact ⟨(h _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ n₁ n₂).1, trivial⟩

/-- `s` with the tag `⟨T, tl⟩` read only, and the data and `W` its writable
regions. -/
abbrev narrowT (D : Addr) (n : Nat) (T : Addr) (tl : Nat) (W : Addr) (s : State) : State :=
  s.withRegions (s.rd ++ [⟨T, tl⟩]) [⟨D, n⟩, ⟨W, 2560⟩]

theorem covers_narrowT (rd : List Region) (d t w : Region) :
    Covers (rd ++ [d, t, w]) ((rd ++ [t]) ++ [d, w]) :=
  Covers.of_mem fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp [h]

/-- The arguments, in the state with the tag read only. -/
theorem Args.narrow {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Ar : VG.Proof.AesOcb.X86_64.Args s K W SP N A D R nl al n tl T) (hw : s.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 2560⟩]) :
    VG.Proof.AesOcb.X86_64.Args (VG.Proof.AesOcb.X86_64.narrowT D n T tl W s) K W SP N A D R nl al n tl T := by
  have c : Covers (s.rd ++ s.wr) ((VG.Proof.AesOcb.X86_64.narrowT D n T tl W s).rd ++ (VG.Proof.AesOcb.X86_64.narrowT D n T tl W s).wr) := by
    rw [hw]; exact VG.Proof.AesOcb.X86_64.covers_narrowT _ _ _ _
  have b : ∀ {P : Addr} {k : Nat}, Buf W SP s P k → Buf W SP (VG.Proof.AesOcb.X86_64.narrowT D n T tl W s) P k := fun h =>
    ⟨h.rd.trans c, h.lt, h.wrap, h.w, h.stk⟩
  have w : Covers [⟨W, 2560⟩] (VG.Proof.AesOcb.X86_64.narrowT D n T tl W s).wr := Covers.of_mem fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp
  have d : Covers [⟨D, n⟩] (VG.Proof.AesOcb.X86_64.narrowT D n T tl W s).wr := Covers.of_mem fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp
  exact {
    lay := Ar.lay, perm := ⟨Ar.perm.k.trans c, w⟩
    rounds := Ar.rounds, nonce := b Ar.nonce, aad := b Ar.aad
    data := ⟨b Ar.data.toBuf, d, Ar.data.k⟩, tag := b Ar.tag
    nd := Ar.nd, ad := Ar.ad, td := Ar.td, n1 := Ar.n1, n15 := Ar.n15, t1 := Ar.t1, t16 := Ar.t16
    retW := Ar.retW, retD := Ar.retD, retT := Ar.retT, args := Ar.args.trans c, argsW := Ar.argsW }

/-- Two runs, from the states with the tag read only. -/
theorem Two.narrow {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Tw : VG.Proof.AesOcb.X86_64.Two s₀ s₀' K W SP N A D R nl al n tl T) (hw : s₀.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 2560⟩])
    (hw' : s₀'.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 2560⟩]) :
    VG.Proof.AesOcb.X86_64.Two (VG.Proof.AesOcb.X86_64.narrowT D n T tl W s₀) (VG.Proof.AesOcb.X86_64.narrowT D n T tl W s₀') K W SP N A D R nl al n tl T :=
  { Tw with ar := Tw.ar.narrow hw, ar' := Tw.ar'.narrow hw' }

/-! ## The copy of the tag and the exit -/

/-- What the copy of the tag needs of a run: the environment, the tag
length in its slot and the address of the tag at `W + tgO`. -/
def SealOut (K W SP T : Addr) (tl : Nat) (s : State) : Prop :=
  Env K W SP s ∧ s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl ∧
    s.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T

/-- The copy of the tag and the exit, in two runs with the same `W`, tag
length and tag. -/
theorem sealTail_rel {K W SP T : Addr} {tl : Nat} {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.AesOcb.X86_64.SealOut K W SP T tl s₁ ∧ VG.Proof.AesOcb.X86_64.SealOut K W SP T tl s₂) :
    RelCT isa P (.seq tagOut (.block VG.Impl.AesOcb.X86_64.restore)) fun _ _ => True := by
  let F : State → Prop := fun s => s.gpr .rbx = W ∧ s.gpr .rsi = T ∧ s.gpr .r12 = BitVec.ofNat 64 tl ∧
    s.gpr .rcx = BitVec.ofNat 64 0 ∧ s.gpr .r15 = W
  have args : ∀ {s : State}, VG.Proof.AesOcb.X86_64.SealOut K W SP T tl s →
      WP isa (.block [mvr .rbx .r15, VG.Impl.AesOcb.X86_64.ld .rsi .r15 tgO, VG.Impl.AesOcb.X86_64.ld .r12 .r15 tlO, .mov .rcx (.imm 0)]) s F :=
    fun ⟨E, htl, htg⟩ => by
      obtain ⟨s', run, h1, h2, h3, h4, g, -⟩ := VG.Proof.AesOcb.X86_64.tagOutArgs_ok E htg htl
      exact WP.of_runBlock ⟨s', run, h1, h2, h3, h4, by rw [g _ (by decide) (by decide) (by decide) (by decide), E.r15]⟩
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r15])
      (.block [mvr .rbx .r15, VG.Impl.AesOcb.X86_64.ld .rsi .r15 tgO, VG.Impl.AesOcb.X86_64.ld .r12 .r15 tlO, .mov .rcx (.imm 0)]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := P) _ (fun a b h => by
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; rw [(hP a b h).1.1.r15, (hP a b h).2.1.r15]) hA).wp
    (F₁ := F) (F₂ := F) fun a b h => ⟨args (hP a b h).1, args (hP a b h).2⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rsi, .r12, .rcx, .r15])
      (.seq copyLoop (.block VG.Impl.AesOcb.X86_64.restore)) hc).isSome = true := ⟨_, by taint_decide⟩
  have b := RelCT.taint (A := taint) (P := fun a b => True ∧ F a ∧ F b) _ (fun a b ⟨_, ha, hb⟩ => by
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [ha.1, hb.1]
    · rw [ha.2.1, hb.2.1]
    · rw [ha.2.2.1, hb.2.2.1]
    · rw [ha.2.2.2.1, hb.2.2.2.1]
    · rw [ha.2.2.2.2, hb.2.2.2.2]) hB
  unfold tagOut
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq e₁ c₁ => cases e₁ with | seq a₁ b₁ =>
  cases e₂ with | seq e₂ c₂ => cases e₂ with | seq a₂ b₂ =>
  obtain ⟨ht, hq⟩ := RelCT.seq a b _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- `vg_aes_ocb_seal` in two runs. -/
theorem seal_rel {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Tw : VG.Proof.AesOcb.X86_64.Two s₀ s₀' K W SP N A D R nl al n tl T) (hw : s₀.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 2560⟩])
    (hw' : s₀'.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 2560⟩]) (v : BlocksImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') («seal» (VG.Proof.AesOcb.X86_64.callees v)) fun _ _ => True := by
  have Tn := Tw.narrow hw hw'
  have inner := (VG.Proof.AesOcb.X86_64.front_rel Tn rfl rfl v true (.inl rfl)).mono (P' := fun σ₁ σ₂ => ∃ s₁ s₂,
      (s₁ = s₀ ∧ s₂ = s₀') ∧ σ₁ = s₁.withRegions (s₁.rd ++ [⟨T, tl⟩]) [⟨D, n⟩, ⟨W, 2560⟩] ∧
        σ₂ = s₂.withRegions (s₂.rd ++ [⟨T, tl⟩]) [⟨D, n⟩, ⟨W, 2560⟩])
    (fun _ _ ⟨_, _, ⟨rfl, rfl⟩, e₁, e₂⟩ => ⟨e₁, e₂⟩) fun _ _ h => h
  have cw : ∀ {s : State}, s.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 2560⟩] →
      Covers ([⟨T, tl⟩] ++ [⟨D, n⟩, ⟨W, 2560⟩]) s.wr ∧ Covers [⟨D, n⟩, ⟨W, 2560⟩] s.wr := fun h => by
    rw [h]
    refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  have fr := (VG.Proof.AesOcb.X86_64.rel_narrow [⟨T, tl⟩] [⟨D, n⟩, ⟨W, 2560⟩] inner fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨_, _, e₁, -⟩ := VG.Proof.AesOcb.X86_64.sealFront_wp' v Tn.ar Tn.sp Tn.dd Tn.nn Tn.tg Tn.tt Tn.ww Tn.di Tn.si Tn.dx Tn.cx
        Tn.r8 Tn.r9
      obtain ⟨_, _, e₂, -⟩ := VG.Proof.AesOcb.X86_64.sealFront_wp' v Tn.ar' Tn.sp' Tn.dd' Tn.nn' Tn.tg' Tn.tt' Tn.ww' Tn.di' Tn.si' Tn.dx'
        Tn.cx' Tn.r8' Tn.r9'
      exact ⟨⟨(cw hw).1, (cw hw).2, _, _, e₁⟩, ⟨(cw hw').1, (cw hw').2, _, _, e₂⟩⟩).wp
    (F₁ := VG.Proof.AesOcb.X86_64.SFront K W SP N A D R nl al n tl T s₀) (F₂ := VG.Proof.AesOcb.X86_64.SFront K W SP N A D R nl al n tl T s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨VG.Proof.AesOcb.X86_64.sealFront_wp' v Tw.ar Tw.sp Tw.dd Tw.nn Tw.tg Tw.tt Tw.ww Tw.di Tw.si Tw.dx Tw.cx Tw.r8 Tw.r9,
        VG.Proof.AesOcb.X86_64.sealFront_wp' v Tw.ar' Tw.sp' Tw.dd' Tw.nn' Tw.tg' Tw.tt' Tw.ww' Tw.di' Tw.si' Tw.dx' Tw.cx' Tw.r8' Tw.r9'⟩
  exact RelCT.seq fr (VG.Proof.AesOcb.X86_64.sealTail_rel fun a b h => ⟨⟨h.2.1.env, h.2.1.slots.tl, h.2.1.tg⟩,
    ⟨h.2.2.env, h.2.2.slots.tl, h.2.2.tg⟩⟩)

/-- Two runs of `seal` or `open` with the same public arguments. -/
theorem Two.of {s₁ s₂ : State} (hq : onePub s₁ s₂)
    (ar₁ : VG.Proof.AesOcb.X86_64.Args s₁ (s₁.gpr .rdi) (arg s₁ 4) (s₁.gpr .rsp) (s₁.gpr .rdx) (s₁.gpr .r8) (arg s₁ 0) (s₁.gpr .rsi).toNat
      (s₁.gpr .rcx).toNat (s₁.gpr .r9).toNat (arg s₁ 1).toNat (arg s₁ 3).toNat (arg s₁ 2))
    (ar₂ : VG.Proof.AesOcb.X86_64.Args s₂ (s₂.gpr .rdi) (arg s₂ 4) (s₂.gpr .rsp) (s₂.gpr .rdx) (s₂.gpr .r8) (arg s₂ 0) (s₂.gpr .rsi).toNat
      (s₂.gpr .rcx).toNat (s₂.gpr .r9).toNat (arg s₂ 1).toNat (arg s₂ 3).toNat (arg s₂ 2)) :
    VG.Proof.AesOcb.X86_64.Two s₁ s₂ (s₁.gpr .rdi) (arg s₁ 4) (s₁.gpr .rsp) (s₁.gpr .rdx) (s₁.gpr .r8) (arg s₁ 0) (s₁.gpr .rsi).toNat
      (s₁.gpr .rcx).toNat (s₁.gpr .r9).toNat (arg s₁ 1).toNat (arg s₁ 3).toNat (arg s₁ 2) := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hq
  have a0 := q8 0 (by decide)
  have a1 := q8 1 (by decide)
  have a2 := q8 2 (by decide)
  have a3 := q8 3 (by decide)
  have a4 := q8 4 (by decide)
  have ar' := ar₂
  rw [← a0, ← a1, ← a2, ← a3, ← a4, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7] at ar'
  exact
  { ar := ar₁, ar' := ar', sp := rfl, sp' := q7.symm
    dd := rfl, dd' := by rw [q7]; exact a0.symm
    nn := (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm, nn' := by rw [q7, a1]; exact (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm
    tg := rfl, tg' := by rw [q7]; exact a2.symm
    tt := (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm, tt' := by rw [q7, a3]; exact (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm
    ww := rfl, ww' := by rw [q7]; exact a4.symm
    di := rfl, di' := q1.symm
    si := (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm, si' := by rw [← q2]; exact (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm
    dx := rfl, dx' := q3.symm
    cx := (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm, cx' := by rw [← q4]; exact (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm
    r8 := rfl, r8' := q5.symm
    r9 := (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm, r9' := by rw [← q6]; exact (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm }

/-- `vg_aes_ocb_seal` is constant time. -/
theorem seal_ct (v : BlocksImpl) : ConstantTime isa sealX86_64.pre sealX86_64.pub («seal» (VG.Proof.AesOcb.X86_64.callees v)) :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hq e₁ e₂ => by
    have T := Two.of hq (VG.Proof.AesOcb.X86_64.sealArgs_of h₁) (VG.Proof.AesOcb.X86_64.sealArgs_of h₂)
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hq
    have hw₂ : s₂.wr = [⟨arg s₁ 0, (arg s₁ 1).toNat⟩, ⟨arg s₁ 2, (arg s₁ 3).toNat⟩, ⟨arg s₁ 4, 2560⟩] := by
      rw [h₂.2.1, q8 0 (by decide), q8 1 (by decide), q8 2 (by decide), q8 3 (by decide), q8 4 (by decide)]
    exact (VG.Proof.AesOcb.X86_64.seal_rel T h₁.2.1 hw₂ v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.Open`. -/
section

/-!
# AES-OCB on x86-64: `vg_aes_ocb_open`

Untrusted: everything here is checked by Lean. `open` is `front`: `entry`,
`Offset_0` (`nonce`), `HASH` (`hash`), the data (`body`) and the tag at
`W + t2O` (`tag`); then the copy of the received tag from `tag` to `W`
(`recv`), its comparison with the computed tag (`cmp`), the mask of the
data (`mask`), the result and `restore` (`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar pad zeros)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append length_bytesAt bytesAt_frame)

/-- `recv`: the `tl` bytes of the tag at `T` copied to `W`. -/
theorem recv_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {T : Addr} {tl : Nat} (h1 : 1 ≤ tl) (h16 : tl ≤ 16)
    (htg : s.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (hT : Covers [⟨T, tl⟩] (s.rd ++ s.wr)) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa recv s fun t => t.mem = writeBytes s.mem W (bytesAt s.mem T tl) ∧
      (∀ r ∈ [Reg.r14, .r15, .rsp], t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨s₁, run₁, rbx₁, rsi₁, r12₁, rcx₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesOcb.X86_64.recvArgs_ok E htg htl
  unfold recv
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (VG.Proof.AesOcb.X86_64.copyLoop_ok s₁ (S := T) (Dd := W) (n := tl) (by omega) (by omega) rbx₁ rsi₁ rcx₁ r12₁
    (by rw [rd₁, wr₁]; exact hT) (by rw [wr₁]; exact covers_prefix E.perm.w (by omega))
    (hTW.sub_right (Region.sub_prefix (by omega)))) fun t ⟨m, _, g, rd, wr⟩ => ⟨by rw [m, m₁], ?_,
      by rw [rd, rd₁], by rw [wr, wr₁]⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> rw [g _ (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide)]

/-- `vg_aes_ocb_open`, for its arguments. -/
theorem open_wp' (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : VG.Proof.AesOcb.X86_64.Args s K W SP N A D R nl al n tl T) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa («open» (VG.Proof.AesOcb.X86_64.callees v)) s fun s' => gprPreserved s s' ∧
      match Spec.Ocb.decryptWith (ctxCiph s.mem K R) (Spec.Ocb.ctxInv s.mem K R) (ctxLstar s.mem K) tl
          (bytesAt s.mem N nl) (bytesAt s.mem A al) (bytesAt s.mem D n) (bytesAt s.mem T tl) with
      | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
      | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem D n = zeros n := by
  have L := Ar.lay
  unfold «open» front
  refine WP.seq (VG.Proof.AesOcb.X86_64.pre_wp v Ar hsp hD hn hT htl hW hdi hsi hdx hcx hr8 hr9 fun s₃ P₃ => ?_)
  have hD₃ : DBuf K W SP s₃ D n := Ar.data.of_eq P₃.rd P₃.wr
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.bodyOpen_ok v L P₃.env Ar.rounds P₃.slots.rounds hD₃ P₃.slots.data P₃.slots.len P₃.ofs
    P₃.o0 P₃.ck (by rw [P₃.l0, P₃.lstar])) fun s₄ B => ?_)
  have F₄ : Frame (mutR W SP D n) s₃.mem s₄.mem := VG.Proof.AesOcb.X86_64.bodyR_mut B.frame
  have cK₄ : ctxCiph s₄.mem K R = ctxCiph s.mem K R := (VG.Proof.AesOcb.X86_64.ctxCiph_mut L Ar.data.k F₄ Ar.rounds).trans P₃.ciph
  have ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K) := by
    rw [VG.Proof.AesOcb.X86_64.body_keep L Ar.data.w B.frame (d := ldO) (by decide), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al) := by
    rw [VG.Proof.AesOcb.X86_64.body_keep L Ar.data.w B.frame (d := sumO) (by decide), P₃.sum]
  -- The tag, at `W + t2O`.
  refine WP.mono (VG.Proof.AesOcb.X86_64.tag_ok v L B.env Ar.rounds ((VG.Proof.AesOcb.X86_64.kept_read L Ar.data.w F₄ (d := 232) (by decide)).trans
    P₃.slots.rounds) (.inr rfl)) fun s₅ T₅ => ?_
  have F₅ : Frame (mutR W SP D n) s₄.mem s₅.mem := VG.Proof.AesOcb.X86_64.tagR_mut (by decide) T₅.frame
  have S₅ := Slots.of_mut L Ar.data.w (F₄.trans F₅) P₃.slots
  -- The received tag, to `W`.
  have tg₅ : s₅.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T := by
    rw [VG.Proof.AesOcb.X86_64.kept_read L Ar.data.w (F₄.trans F₅) (d := tgO) (by decide), P₃.tg]
  have hTs : Buf W SP s₅ T tl := Ar.tag.of_eq (T₅.rd.trans (B.rd.trans P₃.rd)) (T₅.wr.trans (B.wr.trans P₃.wr))
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.recv_ok T₅.env Ar.t1 Ar.t16 tg₅ S₅.tl hTs.rd Ar.tag.w) fun s₅' ⟨mr, gr, rdr, wrr⟩ => ?_)
  have E₅' : Env K W SP s₅' := T₅.env.keep gr rdr wrr
  have Fr : Frame [⟨W, tl⟩] s₅.mem s₅'.mem := by
    rw [mr]; exact writeBytes_frame _ _ _ (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]; exact Region.contains_self _ _)
  have Fr' : Frame (mutR W SP D n) s₅.mem s₅'.mem := Fr.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by have := Ar.t16; omega)⟩
  have S₅' := Slots.of_mut L Ar.data.w Fr' S₅
  -- The comparison.
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.cmp_ok E₅' Ar.t1 Ar.t16 S₅'.tl) fun s₆ ⟨m₆, g₆, rd₆, wr₆⟩ => ?_)
  have E₆ : Env K W SP s₆ := E₅'.keep (fun r hr => g₆ r
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₆ wr₆
  have F₆ : Frame [⟨W + BitVec.ofNat 64 tagO, 8⟩] s₅'.mem s₆.mem := by
    rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have k₆ : ∀ {d : Nat}, 8 ≤ d → d + 8 ≤ 2560 →
      s₆.mem.readW (W + BitVec.ofNat 64 d) 64 = s₅'.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ => by
    rw [m₆, VG.Proof.AesOcb.X86_64.readW_writeW_off _ (by simp only [tagO]; omega) (by omega) (by decide)]
  have hD₅ : DBuf K W SP s₅' D n := hD₃.of_eq (rdr.trans (T₅.rd.trans B.rd)) (wrr.trans (T₅.wr.trans B.wr))
  let c : Bool := decide (bytesAt s₅'.mem W tl = bytesAt s₅'.mem (W + BitVec.ofNat 64 t2O) tl)
  -- The mask.
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.mask_ok E₆ (c := c) (by rw [k₆ (by decide) (by decide)]; exact S₅'.data)
    (by rw [k₆ (by decide) (by decide)]; exact S₅'.len) (hD₅.of_eq rd₆ wr₆)
    (by rw [m₆, Mem.readW_writeW_self64]; simp only [c, decide_eq_true_eq])) fun s₇ ⟨E₇, rd₇, wr₇, m₇⟩ => ?_)
  have F₇ : Frame [⟨D, n⟩] s₆.mem s₇.mem := by
    rw [m₇]; exact writeBytes_frame _ _ _ (by rw [VG.Proof.AesOcb.X86_64.length_mask]; exact Region.contains_self _ _)
  have F₃₇ : Frame (mutR W SP D n) s₃.mem s₇.mem :=
    (((F₄.trans F₅).trans Fr').trans (F₆.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩)).trans
    (F₇.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  -- The result, and `restore`.
  have ok₇ : s₇.mem.readW (W + BitVec.ofNat 64 0) 64 = if c then 1#64 else 0#64 := by
    rw [F₇.readW (r := ⟨W + BitVec.ofNat 64 0, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (Ar.data.w.sub_right (Lay.wSub (by decide))).symm)
      (by decide), m₆]
    exact (Mem.readW_writeW_self64 _ _ _).trans (by simp only [c, decide_eq_true_eq])
  have r₀ : InRegions (s₇.rd ++ s₇.wr) (W + BitVec.ofNat 64 0) 8 := E₇.perm.wR (by decide)
  obtain ⟨s₈, run₈, rax₈, m₈, g₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa [VG.Impl.AesOcb.X86_64.ld .rax .r15 tagO] s₇ = some s₈ ∧
      s₈.gpr .rax = (if c then 1#64 else 0#64) ∧ s₈.mem = s₇.mem ∧ (∀ r, r ≠ .rax → s₈.gpr r = s₇.gpr r) ∧
      s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by orun [E₇.r15, r₀, ok₇], ?_, ?_, fun r h => ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true]
    · rfl
    · simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  have E₈ : Env K W SP s₈ := E₇.keep (fun r hr => g₈ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₈ wr₈
  obtain ⟨s₉, run₉, hg₉, hm₉, hsp₉, hax₉⟩ := VG.Proof.AesOcb.X86_64.restore_ok E₈ (by rw [m₈]; exact VG.Proof.AesOcb.X86_64.saved_mut L Ar.data.w F₃₇ P₃.saved)
  refine WP.of_runBlock ⟨s₉, by rw [VG.Proof.AesCcm.X86_64.runBlock_append, run₈, Option.bind_some, run₉], ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₉ (.rbx, savO) (by decide)
    · exact hg₉ (.rbp, savO + 8) (by decide)
    · rw [hsp₉, E₈.rsp, hsp]
    · exact hg₉ (.r12, savO + 16) (by decide)
    · exact hg₉ (.r13, savO + 24) (by decide)
    · exact hg₉ (.r14, savO + 32) (by decide)
    · exact hg₉ (.r15, savO + 40) (by decide)
  · have fall : Frame (VG.Proof.AesOcb.X86_64.entryR W :: mutR W SP D n) s.mem s₇.mem :=
      P₃.frame.trans (F₃₇.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
    rw [hm₉, m₈, hsp]
    exact fall.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (VG.Proof.AesOcb.X86_64.ret_disj L Ar.retW Ar.retD) (by decide)
  · -- The plaintext and the comparison.
    have hRb : 16 * (R + 1) ≤ 256 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
    have i₃ : Spec.Ocb.ctxInv s₃.mem K R = Spec.Ocb.ctxInv s.mem K R := by
      unfold Spec.Ocb.ctxInv
      rw [VG.Proof.AesCcm.X86_64.bytesAt_frame P₃.frame (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
        · exact (k_mut L Ar.data.k r hr).sub_left (Region.sub_prefix hRb)) (by omega)]
    have hout := B.out
    rw [P₃.ciph, P₃.lstar, P₃.data, i₃] at hout
    have hofs := B.ofs
    rw [P₃.lstar] at hofs
    have hck := B.ck
    rw [P₃.ciph, P₃.lstar, P₃.data, i₃] at hck
    have hTn := Ar.tag.lt
    have recv : bytesAt s₅'.mem W tl = bytesAt s.mem T tl := by
      rw [mr, Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]) (by omega), VG.Proof.AesCcm.X86_64.length_bytesAt,
        List.drop_of_length_le (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]), List.append_nil,
        VG.Proof.AesOcb.X86_64.buf_mut Ar.tag Ar.td (F₄.trans F₅)]
      exact VG.Proof.AesCcm.X86_64.bytesAt_frame P₃.frame (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact Ar.tag.w.sub_right (Lay.wSub (by decide))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · exact Ar.tag.w.sub_right (Region.sub_prefix (by decide))
          · exact Ar.tag.w.sub_right (Lay.wSub (by decide))
          · exact Ar.tag.w.sub_right (Lay.wSub (by decide))
          · exact Ar.tag.stk.symm
          · exact Ar.td) (by omega)
    have t2₅ : bytesAt s₅'.mem (W + BitVec.ofNat 64 t2O) tl = bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl :=
      VG.Proof.AesCcm.X86_64.bytesAt_frame Fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.base_disjoint W (e := t2O) (n := tl) (k := tl) (by have := Ar.t16; unfold t2O; omega)
          (by have := Ar.t16; unfold t2O; omega)).symm) (by omega)
    have tagv := T₅.val
    rw [hck, hofs, ld₄, sum₄, cK₄] at tagv
    have d₉ : bytesAt s₉.mem D n = if c then bytesAt s₄.mem D n else zeros n := by
      have hn := Ar.data.lt
      have d₆ : bytesAt s₆.mem D n = bytesAt s₄.mem D n := by
        rw [VG.Proof.AesCcm.X86_64.bytesAt_frame F₆ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
            (by omega),
          VG.Proof.AesCcm.X86_64.bytesAt_frame Fr (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Ar.data.w.sub_right (Region.sub_prefix (by have := Ar.t16; omega))) (by omega),
          VG.Proof.AesCcm.X86_64.bytesAt_frame T₅.frame (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl
            · exact Ar.data.w.sub_right (Lay.wSub (by decide))
            · exact Ar.data.w.sub_right (Lay.wSub (by decide))
            · exact Ar.data.w.sub_right (Lay.wSub (by decide))
            · exact Ar.data.stk.symm) (by omega)]
      rw [hm₉, m₈, m₇, Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by rw [VG.Proof.AesOcb.X86_64.length_mask]) hn, VG.Proof.AesOcb.X86_64.length_mask,
        List.drop_of_length_le (by rw [VG.Proof.AesCcm.X86_64.length_bytesAt]), List.append_nil, d₆]
    rw [hax₉, rax₈, d₉, hout]
    rw [Proof.Ocb.decryptWith_eq]
    simp only [VG.Proof.AesCcm.X86_64.length_bytesAt, List.length_drop]
    have hc : ∀ x : Block, bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl = (Spec.Ocb.toBytes x).take tl →
        (c = true ↔ (Spec.Ocb.toBytes x).take tl = bytesAt s.mem T tl) := fun x hx => by
      show decide (_ = _) = true ↔ _
      rw [recv, t2₅, hx, decide_eq_true_iff, eq_comm]
    by_cases hr : 0 < n % 16
    · have h' : n - 16 * (n / 16) > 0 := by omega
      simp only [h', hr, ↓reduceIte] at tagv ⊢
      rw [VG.Proof.AesOcb.X86_64.bytesAt_take_block _ _ Ar.t16, tagv] at hc
      have hc := hc _ rfl
      by_cases hk : c = true
      · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
      · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, trivial⟩
    · have h' : ¬ (n - 16 * (n / 16) > 0) := by omega
      simp only [h', hr, ↓reduceIte] at tagv ⊢
      rw [VG.Proof.AesOcb.X86_64.bytesAt_take_block _ _ Ar.t16, tagv] at hc
      have hc := hc _ rfl
      by_cases hk : c = true
      · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
      · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, trivial⟩

/-- `vg_aes_ocb_open`. -/
theorem open_wp (v : BlocksImpl) {s : State} (h : openPreX s) :
    WP isa («open» (VG.Proof.AesOcb.X86_64.callees v)) s fun s' => gprPreserved s s' ∧ openX86_64.post s s' :=
  VG.Proof.AesOcb.X86_64.open_wp' v (VG.Proof.AesOcb.X86_64.openArgs_of h) rfl rfl (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm rfl (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm rfl rfl (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm
    rfl (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm rfl (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.OpenCT`. -/
section

/-!
# AES-OCB on x86-64: `vg_aes_ocb_open` is constant time

Untrusted: everything here is checked by Lean. As `seal` (`front_rel`), then
the copy of the received tag to `W`, the comparison, the mask and `restore`,
which pass the taint analysis from the public slots and the address of the
tag at `W + tgO`: the comparison's result is a value, not a branch.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)

section
variable {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {Tg : Addr}
  (T : VG.Proof.AesOcb.X86_64.Two s₀ s₀' K W SP N A D R nl al n tl Tg)
include T

/-- `recv` keeps the public arguments. -/
theorem recv_one {s : State} (o : VG.Proof.AesOcb.X86_64.OneT K W SP R N A D nl n tl Tg s) :
    WP isa recv s (VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl) := by
  refine WP.mono (VG.Proof.AesOcb.X86_64.recv_ok o.1.env T.ar.t1 T.ar.t16 o.2.1 o.1.sl.tl o.2.2 T.ar.tag.w) fun t ⟨m, g, rd, wr⟩ => ?_
  have fr : Frame (mutR W SP D n) s.mem t.mem := by
    rw [m]
    refine (writeBytes_frame _ _ _ (by rw [Proof.AesCcm.X86_64.length_bytesAt]; exact Region.contains_self _ _)).sub
      fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by have := T.ar.t16; omega)⟩
  exact o.1.step T.ar.lay T.ar.data.w (o.1.env.keep g rd wr) wr fr

/-- The comparison keeps the public arguments, and leaves 1 or 0 at `W`. -/
theorem cmpRes {s : State} (o : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s) :
    WP isa cmp s fun t => VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl t ∧
      ∃ c : Bool, t.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64 := by
  refine WP.mono (VG.Proof.AesOcb.X86_64.cmp_ok o.env T.ar.t1 T.ar.t16 o.sl.tl) fun t ⟨m, g, rd, wr⟩ => ?_
  have E : Env K W SP t := o.env.keep (fun r hr => g r
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd wr
  have fr : Frame (mutR W SP D n) s.mem t.mem := by
    rw [m]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)).sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., VG.Proof.AesOcb.X86_64.sub_wA (by decide)⟩
  refine ⟨o.step T.ar.lay T.ar.data.w E wr fr, decide (bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl),
    ?_⟩
  rw [m, Mem.readW_writeW_self64]; simp only [decide_eq_true_eq]

/-- The mask keeps the public arguments. -/
theorem mask_one {s : State} (o : VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s) {c : Bool}
    (hok : s.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64) :
    WP isa mask s (VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl) := by
  refine WP.mono (VG.Proof.AesOcb.X86_64.mask_ok o.env o.sl.data o.sl.len (T.ar.data.of_one o) hok) fun t ⟨E, _, wr, m⟩ => ?_
  have fr : Frame (mutR W SP D n) s.mem t.mem := by
    rw [m]
    refine (writeBytes_frame _ _ _ (by rw [VG.Proof.AesOcb.X86_64.length_mask]; exact Region.contains_self _ _)).sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  exact o.step T.ar.lay T.ar.data.w E wr fr

variable (hw : s₀.wr = [⟨D, n⟩, ⟨W, 2560⟩]) (hw' : s₀'.wr = [⟨D, n⟩, ⟨W, 2560⟩])
include hw hw'

/-- `vg_aes_ocb_open` in two runs. -/
theorem open_rel (v : BlocksImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') («open» (VG.Proof.AesOcb.X86_64.callees v)) fun _ _ => True := by
  have hDW := T.ar.data.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt T.ar.data.lt
  have fr := VG.Proof.AesOcb.X86_64.front_rel T hw hw' v false (.inr rfl)
  have rr := (VG.Proof.AesOcb.X86_64.rel_taintC [] [tgO] hDW hn (fun a b (h : True ∧ VG.Proof.AesOcb.X86_64.OneT K W SP R N A D nl n tl Tg a ∧
    VG.Proof.AesOcb.X86_64.OneT K W SP R N A D nl n tl Tg b) => ⟨h.2.1.1.env, h.2.2.1.env, h.2.1.1.sl, h.2.2.1.sl, h.2.1.1.wr, h.2.2.1.wr,
      fun _ h => (nomatch h), fun d hd => by
        simp only [List.mem_singleton] at hd; subst hd; exact ⟨by decide, by rw [h.2.1.2.1, h.2.2.2.1]⟩⟩)
    (c := recv) ⟨_, by taint_decide⟩).wp
    (F₁ := VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl) (F₂ := VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl)
    fun a b h => ⟨VG.Proof.AesOcb.X86_64.recv_one T h.2.1, VG.Proof.AesOcb.X86_64.recv_one T h.2.2⟩
  have cc := (VG.Proof.AesOcb.X86_64.rel_taintC [] [] hDW hn (fun a b (h : True ∧ VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl a ∧
    VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl b) => Both.of h.2.1 h.2.2) (c := cmp) ⟨_, by taint_decide⟩).wp
    (F₁ := fun (s : State) => VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s ∧ ∃ c : Bool, s.mem.readW (W + BitVec.ofNat 64 tagO) 64 =
      if c then 1#64 else 0#64)
    (F₂ := fun (s : State) => VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl s ∧ ∃ c : Bool, s.mem.readW (W + BitVec.ofNat 64 tagO) 64 =
      if c then 1#64 else 0#64)
    fun a b h => ⟨VG.Proof.AesOcb.X86_64.cmpRes T h.2.1, VG.Proof.AesOcb.X86_64.cmpRes T h.2.2⟩
  have mm := (VG.Proof.AesOcb.X86_64.rel_taintC [] [] hDW hn (fun a b (h : True ∧ (VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl a ∧
      ∃ c : Bool, a.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64) ∧
    (VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl b ∧
      ∃ c : Bool, b.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64)) => Both.of h.2.1.1 h.2.2.1)
    (c := mask) ⟨_, by taint_decide⟩).wp
    (F₁ := VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl) (F₂ := VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl)
    fun a b h => ⟨VG.Proof.AesOcb.X86_64.mask_one T h.2.1.1 h.2.1.2.choose_spec, VG.Proof.AesOcb.X86_64.mask_one T h.2.2.1 h.2.2.2.choose_spec⟩
  have rs := VG.Proof.AesOcb.X86_64.rel_taintC [] [] hDW hn (fun a b (h : True ∧ VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl a ∧
    VG.Proof.AesOcb.X86_64.One K W SP R N A D nl n tl b) => Both.of h.2.1 h.2.2) (c := .block ([VG.Impl.AesOcb.X86_64.ld .rax .r15 tagO] ++ VG.Impl.AesOcb.X86_64.restore))
    ⟨_, by taint_decide⟩
  unfold «open»
  exact RelCT.seq fr (RelCT.seq rr (RelCT.seq cc (RelCT.seq mm rs)))

end

/-- `vg_aes_ocb_open` is constant time. -/
theorem open_ct (v : BlocksImpl) : ConstantTime isa openX86_64.pre openX86_64.pub («open» (VG.Proof.AesOcb.X86_64.callees v)) :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hq e₁ e₂ => by
    have T := Two.of hq.1 (VG.Proof.AesOcb.X86_64.openArgs_of h₁) (VG.Proof.AesOcb.X86_64.openArgs_of h₂)
    obtain ⟨⟨q1, q2, q3, q4, q5, q6, q7, q8⟩, -⟩ := hq
    have hw₂ : s₂.wr = [⟨arg s₁ 0, (arg s₁ 1).toNat⟩, ⟨arg s₁ 4, 2560⟩] := by
      rw [h₂.2.1, q8 0 (by decide), q8 1 (by decide), q8 4 (by decide)]
    exact (VG.Proof.AesOcb.X86_64.open_rel T h₁.2.1 hw₂ v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.Init`. -/
section

/-!
# AES-OCB on x86-64: `vg_aes_ocb_init`

Untrusted: everything here is checked by Lean. `init` saves `rbx`, `rbp` and
`r12` in the scratch buffer, expands the key into the key context, enciphers
a zero block at byte 240 of it in place, for `L_*`, and restores the
registers (`init_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append length_bytesAt bytesAt_frame toNat_ofNat_of_lt)

/-- What `vg_aes_ocb_init` is given: the key (`KL` bytes at `Kp`), the key
context at `C` and the scratch buffer at `S`. -/
structure IArgs (s : State) (Kp C S : Addr) (KL : Nat) : Prop where
  rd : s.rd = [⟨Kp, KL⟩]
  wr : s.wr = [⟨C, 256⟩, ⟨S, 2560⟩]
  kc : (⟨Kp, KL⟩ : Region).Disjoint ⟨C, 256⟩
  ks : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 2560⟩
  cs : (⟨C, 256⟩ : Region).Disjoint ⟨S, 2560⟩
  retC : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨C, 256⟩
  retS : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 2560⟩
  stkK : (below (s.gpr .rsp) 8).Disjoint ⟨Kp, KL⟩
  stkC : (below (s.gpr .rsp) 8).Disjoint ⟨C, 256⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 2560⟩
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wC : C.toNat + 256 ≤ 2 ^ 64
  wS : S.toNat + 2560 ≤ 2 ^ 64
  sp : 8 ≤ (s.gpr .rsp).toNat
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32

theorem IArgs.of {s : State} (h : initX86_64.pre s) :
    VG.Proof.AesOcb.X86_64.IArgs s (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .rsi).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩

/-- The rounds, as `shr 2; add 6` computes them from the key length. -/
theorem rounds_bv {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) :
    BitVec.ofNat 64 KL >>> 2 + BitVec.ofNat 64 6 = BitVec.ofNat 64 (KL / 4 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem rounds_of {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) :
    KL / 4 + 6 = 10 ∨ KL / 4 + 6 = 12 ∨ KL / 4 + 6 = 14 := by
  rcases h with rfl | rfl | rfl <;> decide

/-- A read of a word in a region, through a write in a region apart from it. -/
theorem readW_writeW_off' {m : Mem} {a b : Addr} {r r' : Region} {v : BitVec 64} (ha : r.Contains a (64 / 8))
    (hd : r.Disjoint r') (hb : r'.Contains b (64 / 8) := by exact Region.contains_self _ _) :
    (m.writeW b v).readW a 64 = m.readW a 64 :=
  Mem.readW_writeW_sep (hd.sep ha hb) (by decide)

/-- The registers saved and the arguments of the key expansion. -/
theorem init1_ok {s : State} {Kp C S : Addr} {KL : Nat} (Ar : VG.Proof.AesOcb.X86_64.IArgs s Kp C S KL)
    (hdi : s.gpr .rdi = Kp) (hsi : s.gpr .rsi = BitVec.ofNat 64 KL) (hdx : s.gpr .rdx = C) (hcx : s.gpr .rcx = S) :
    ∃ s₁, runBlock isa
      [st .rcx 0 .rbx, st .rcx 8 .rbp, st .rcx 16 .r12, mvr .rbx .rdx, mvr .rbp .rsi, .shift .shr .rbp 2,
        addi .rbp 6, mvr .r12 .rcx, addi .rcx scrO] s = some s₁ ∧
      s₁.gpr .rbx = C ∧ s₁.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₁.gpr .r12 = S ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧
      s₁.mem = ((s.mem.writeW (S + BitVec.ofNat 64 0) (s.gpr .rbx)).writeW (S + BitVec.ofNat 64 8) (s.gpr .rbp)).writeW
        (S + BitVec.ofNat 64 16) (s.gpr .r12) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      KCall s₁ Kp C (S + BitVec.ofNat 64 512) KL ∧ s₁.gpr .rsp = s.gpr .rsp := by
  have hR := VG.Proof.AesOcb.X86_64.rounds_of Ar.klen
  have hKL : KL < 2 ^ 64 := by rcases Ar.klen with h | h | h <;> omega
  have inS : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions s.wr (S + BitVec.ofNat 64 d) 8 := fun h => by
    rw [Ar.wr]; exact ⟨⟨S, 2560⟩, by simp, Offset.contains_base _ h (by have := Ar.wS; omega)⟩
  have e6 : BitVec.signExtend 64 (BitVec.ofNat 32 6) = BitVec.ofNat 64 6 := by decide
  -- The registers saved, the arguments of the key expansion.
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, rbx₁, rbp₁, r12₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [st .rcx 0 .rbx, st .rcx 8 .rbp, st .rcx 16 .r12, mvr .rbx .rdx, mvr .rbp .rsi, .shift .shr .rbp 2,
        addi .rbp 6, mvr .r12 .rcx, addi .rcx scrO] s = some s₁ ∧
      s₁.gpr .rdi = Kp ∧ s₁.gpr .rsi = BitVec.ofNat 64 KL ∧ s₁.gpr .rdx = C ∧ s₁.gpr .rcx = S + BitVec.ofNat 64 512 ∧
      s₁.gpr .rbx = C ∧ s₁.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₁.gpr .r12 = S ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧
      s₁.mem = ((s.mem.writeW (S + BitVec.ofNat 64 0) (s.gpr .rbx)).writeW (S + BitVec.ofNat 64 8) (s.gpr .rbp)).writeW
        (S + BitVec.ofNat 64 16) (s.gpr .r12) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [hcx, inS (d := 0) (by decide), inS (d := 8) (by decide), inS (d := 16) (by decide)],
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hdi]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hsi]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hdx]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hcx]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hdx]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hsi, e6,
        VG.Proof.AesOcb.X86_64.rounds_bv Ar.klen]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hcx]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, h₂, h₃, h₄, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags, hcx]
    all_goals rfl
  have SP := s.gpr .rsp
  have hsp₁ : s₁.gpr .rsp = s.gpr .rsp := g₁ _ (by decide) (by decide) (by decide) (by decide)
  have f₁ : Frame [⟨S, 24⟩] s.mem s₁.mem := by
    have c : ∀ d, d + 8 ≤ 24 → (⟨S, 24⟩ : Region).Contains (S + BitVec.ofNat 64 d) (64 / 8) := fun d hd =>
      Offset.contains_base _ hd (by have := Ar.wS; omega)
    rw [m₁]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 8 (by decide))).writeW (List.mem_singleton_self _) _ (c 16 (by decide))
  have sub_S : ∀ {d k : Nat}, d + k ≤ 2560 → Region.Sub ⟨S + BitVec.ofNat 64 d, k⟩ ⟨S, 2560⟩ :=
    fun h => Offset.sub_base S h
  have sub_C : ∀ {d k : Nat}, d + k ≤ 256 → Region.Sub ⟨C + BitVec.ofNat 64 d, k⟩ ⟨C, 256⟩ :=
    fun h => Offset.sub_base C h
  -- The key schedule.
  have K₁ : KCall s₁ Kp C (S + BitVec.ofNat 64 512) KL :=
    { rdi := rdi₁, rsi := rsi₁, rdx := rdx₁, rcx := rcx₁, klen := Ar.klen
      kc := Ar.kc.sub_right (Region.sub_prefix (by decide))
      ks := Ar.ks.sub_right (sub_S (by decide))
      cs := (Ar.cs.sub_left (Region.sub_prefix (by decide))).sub_right (sub_S (by decide))
      stkK := by rw [hsp₁]; exact Ar.stkK
      stkC := by rw [hsp₁]; exact Ar.stkC.sub_right (Region.sub_prefix (by decide))
      stkS := by rw [hsp₁]; exact Ar.stkS.sub_right (sub_S (by decide))
      reads := by
        rw [rd₁, wr₁, Ar.rd, Ar.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨Kp, KL⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨C, 256⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 2560⟩, by simp, 512, rfl, by simp⟩
      writes := by
        rw [wr₁, Ar.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨C, 256⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 2560⟩, by simp, 512, rfl, by simp⟩ }
  exact ⟨s₁, run₁, rbx₁, rbp₁, r12₁, g₁, m₁, rd₁, wr₁, K₁, hsp₁⟩

/-- A zero block at byte 240 of the key context and the arguments of its encipherment. -/
theorem init3_ok {s : State} {Kp C S : Addr} {KL : Nat} (Ar : VG.Proof.AesOcb.X86_64.IArgs s Kp C S KL) {s₂ : State}
    (h3 : s₂.gpr .rbx = C) (h5 : s₂.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6)) (h12 : s₂.gpr .r12 = S)
    (hrd : s₂.rd = s.rd) (hwr : s₂.wr = s.wr) (hsp : s₂.gpr .rsp = s.gpr .rsp) :
    ∃ s₃, runBlock isa
      [.alu .xor .rax (.reg .rax), st .rbx 240 .rax, st .rbx 248 .rax, mvr .rdi .rbx, mvr .rsi .rbp,
        mvr .rdx .rbx, addi .rdx 240, .mov .rcx (.imm 1), mvr .r8 .r12, addi .r8 scrO] s₂ = some s₃ ∧
      (∀ r ∈ calleeSaved, s₃.gpr r = s₂.gpr r) ∧
      s₃.mem = (s₂.mem.writeW (C + BitVec.ofNat 64 240) 0#64).writeW (C + BitVec.ofNat 64 248) 0#64 ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr ∧
      BCall s₃ C (C + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 512) (KL / 4 + 6) 1 ∧ s₃.gpr .rsp = s.gpr .rsp := by
  have hR := VG.Proof.AesOcb.X86_64.rounds_of Ar.klen
  have sub_S : ∀ {d k : Nat}, d + k ≤ 2560 → Region.Sub ⟨S + BitVec.ofNat 64 d, k⟩ ⟨S, 2560⟩ :=
    fun h => Offset.sub_base S h
  have sub_C : ∀ {d k : Nat}, d + k ≤ 256 → Region.Sub ⟨C + BitVec.ofNat 64 d, k⟩ ⟨C, 256⟩ :=
    fun h => Offset.sub_base C h
  -- `L_*`: a zero block at byte 240, enciphered.
  have w₁ : InRegions s₂.wr (C + BitVec.ofNat 64 240) 8 := by
    rw [hwr, Ar.wr]; exact ⟨⟨C, 256⟩, by simp, Offset.contains_base _ (by decide) (by have := Ar.wC; omega)⟩
  have w₂ : InRegions s₂.wr (C + BitVec.ofNat 64 248) 8 := by
    rw [hwr, Ar.wr]; exact ⟨⟨C, 256⟩, by simp, Offset.contains_base _ (by decide) (by have := Ar.wC; omega)⟩
  obtain ⟨s₃, run₃, rdi₃, rsi₃, rdx₃, rcx₃, r8₃, g₃, m₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa
      [.alu .xor .rax (.reg .rax), st .rbx 240 .rax, st .rbx 248 .rax, mvr .rdi .rbx, mvr .rsi .rbp,
        mvr .rdx .rbx, addi .rdx 240, .mov .rcx (.imm 1), mvr .r8 .r12, addi .r8 scrO] s₂ = some s₃ ∧
      s₃.gpr .rdi = C ∧ s₃.gpr .rsi = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₃.gpr .rdx = C + BitVec.ofNat 64 240 ∧
      s₃.gpr .rcx = BitVec.ofNat 64 1 ∧ s₃.gpr .r8 = S + BitVec.ofNat 64 512 ∧
      (∀ r ∈ calleeSaved, s₃.gpr r = s₂.gpr r) ∧
      s₃.mem = (s₂.mem.writeW (C + BitVec.ofNat 64 240) 0#64).writeW (C + BitVec.ofNat 64 248) 0#64 ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by orun [h3, w₁, w₂], ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h3]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h5]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h3]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, sext1]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h12]
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [mem_setReg, mem_arithFlags, BitVec.xor_self]
    all_goals rfl
  have hsp₃ : s₃.gpr .rsp = s.gpr .rsp := by rw [g₃ _ (by decide), hsp]
  have dC : (⟨C, 240⟩ : Region).Disjoint ⟨C + BitVec.ofNat 64 240, 16 * 1⟩ :=
    Offset.base_disjoint C (Nat.le_refl _) (by decide)
  have B₃ : BCall s₃ C (C + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 512) (KL / 4 + 6) 1 :=
    { rdi := rdi₃, rsi := rsi₃, rdx := rdx₃, rcx := rcx₃, r8 := r8₃, rounds := hR
      wrap := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Ar.wC; omega
      kd := dC
      ks := (Ar.cs.sub_left (Region.sub_prefix (by decide))).sub_right (sub_S (by decide))
      ds := (Ar.cs.sub_left (sub_C (by decide))).sub_right (sub_S (by decide))
      stkK := by rw [hsp₃]; exact Ar.stkC.sub_right (Region.sub_prefix (by decide))
      stkD := by rw [hsp₃]; exact Ar.stkC.sub_right (sub_C (by decide))
      stkS := by rw [hsp₃]; exact Ar.stkS.sub_right (sub_S (by decide))
      reads := by
        rw [rd₃, wr₃, hrd, hwr, Ar.rd, Ar.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨C, 256⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨C, 256⟩, by simp, 240, rfl, by simp⟩
        · exact ⟨⟨S, 2560⟩, by simp, 512, rfl, by simp⟩
      writes := by
        rw [wr₃, hwr, Ar.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨C, 256⟩, by simp, 240, rfl, by simp⟩
        · exact ⟨⟨S, 2560⟩, by simp, 512, rfl, by simp⟩ }
  exact ⟨s₃, run₃, g₃, m₃, rd₃, wr₃, B₃, hsp₃⟩

/-- `vg_aes_ocb_init`, for its arguments. -/
theorem init_wp' (v : BlocksImpl) {s : State} {Kp C S : Addr} {KL : Nat} (Ar : VG.Proof.AesOcb.X86_64.IArgs s Kp C S KL)
    (hdi : s.gpr .rdi = Kp) (hsi : s.gpr .rsi = BitVec.ofNat 64 KL) (hdx : s.gpr .rdx = C) (hcx : s.gpr .rcx = S) :
    WP isa (init (VG.Proof.AesOcb.X86_64.callees v)) s fun s' => gprPreserved s s' ∧
      Spec.Ocb.KeyRepr s'.mem C (bytesAt s.mem Kp KL) := by
  have hR := VG.Proof.AesOcb.X86_64.rounds_of Ar.klen
  have hKL : KL < 2 ^ 64 := by rcases Ar.klen with h | h | h <;> omega
  have inS : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions s.wr (S + BitVec.ofNat 64 d) 8 := fun h => by
    rw [Ar.wr]; exact ⟨⟨S, 2560⟩, by simp, Offset.contains_base _ h (by have := Ar.wS; omega)⟩
  obtain ⟨s₁, run₁, rbx₁, rbp₁, r12₁, g₁, m₁, rd₁, wr₁, K₁, hsp₁⟩ := VG.Proof.AesOcb.X86_64.init1_ok Ar hdi hsi hdx hcx
  have f₁ : Frame [⟨S, 24⟩] s.mem s₁.mem := by
    have c : ∀ d, d + 8 ≤ 24 → (⟨S, 24⟩ : Region).Contains (S + BitVec.ofNat 64 d) (64 / 8) := fun d hd =>
      Offset.contains_base _ hd (by have := Ar.wS; omega)
    rw [m₁]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 8 (by decide))).writeW (List.mem_singleton_self _) _ (c 16 (by decide))
  have sub_S : ∀ {d k : Nat}, d + k ≤ 2560 → Region.Sub ⟨S + BitVec.ofNat 64 d, k⟩ ⟨S, 2560⟩ :=
    fun h => Offset.sub_base S h
  have sub_C : ∀ {d k : Nat}, d + k ≤ 256 → Region.Sub ⟨C + BitVec.ofNat 64 d, k⟩ ⟨C, 256⟩ :=
    fun h => Offset.sub_base C h
  unfold init
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesOcb.X86_64.key_call v K₁) fun s₂ P₂ => ?_)
  have sv₂ : ∀ r ∈ calleeSaved, s₂.gpr r = s₁.gpr r := P₂.saved
  obtain ⟨s₃, run₃, g₃, m₃, rd₃, wr₃, B₃, hsp₃⟩ := VG.Proof.AesOcb.X86_64.init3_ok Ar (by rw [sv₂ _ (by decide), rbx₁])
    (by rw [sv₂ _ (by decide), rbp₁]) (by rw [sv₂ _ (by decide), r12₁]) (by rw [P₂.rd, rd₁]) (by rw [P₂.wr, wr₁])
    (by rw [sv₂ _ (by decide), hsp₁])
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  refine WP.seq (WP.mono (blk_call v.encOk v.encNosp v.encDepth B₃) fun s₄ P₄ => ?_)
  -- The registers back.
  have h12₄ : s₄.gpr .r12 = S := by rw [P₄.saved _ (by decide), g₃ _ (by decide), sv₂ _ (by decide), r12₁]
  have rS : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions (s₄.rd ++ s₄.wr) (S + BitVec.ofNat 64 d) 8 := fun h => by
    rw [P₄.rd, P₄.wr, rd₃, wr₃, P₂.rd, P₂.wr, rd₁, wr₁]; exact Proof.AesCcm.X86_64.in_left (inS h)
  -- What the code after the first block keeps of the save area.
  have dS : ∀ {d k : Nat}, d + k ≤ 2560 → 512 ≤ d → (⟨S, 24⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ h₂ => Offset.base_disjoint S (by omega) (by omega)
  have dSC : ∀ {d k : Nat}, d + k ≤ 256 → (⟨S, 24⟩ : Region).Disjoint ⟨C + BitVec.ofNat 64 d, k⟩ :=
    fun h => (Ar.cs.symm.sub_left (Region.sub_prefix (by decide))).sub_right (sub_C h)
  have dSs : (⟨S, 24⟩ : Region).Disjoint (below (s.gpr .rsp) 8) :=
    (Ar.stkS.sub_right (Region.sub_prefix (by decide))).symm
  have keep : ∀ {d : Nat}, d + 8 ≤ 24 →
      s₄.mem.readW (S + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S + BitVec.ofNat 64 d) 64 := fun {d} hd => by
    have hc : (⟨S, 24⟩ : Region).Contains (S + BitVec.ofNat 64 d) (64 / 8) :=
      Offset.contains_base _ hd (by have := Ar.wS; omega)
    rw [P₄.frame.readW hc (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dSC (by decide)
        · exact dS (by decide) (by decide)
        · rw [hsp₃]; exact dSs) (by decide),
      m₃, VG.Proof.AesOcb.X86_64.readW_writeW_off' hc (dSC (d := 248) (k := 8) (by decide)),
      VG.Proof.AesOcb.X86_64.readW_writeW_off' hc (dSC (d := 240) (k := 8) (by decide)),
      P₂.frame.readW hc (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · simpa using dSC (d := 0) (k := 240) (by decide)
        · exact dS (by decide) (by decide)
        · rw [hsp₁]; exact dSs) (by decide)]
  have sp : ∀ (a b : Nat), a + 8 ≤ b ∨ b + 8 ≤ a → a + 8 ≤ 2560 → b + 8 ≤ 2560 →
      Mem.Sep (S + BitVec.ofNat 64 a) (64 / 8) (S + BitVec.ofNat 64 b) (64 / 8) := fun a b h ha hb =>
    Offset.sep S h (by omega) (by omega)
  have v0 : s₄.mem.readW (S + BitVec.ofNat 64 0) 64 = s.gpr .rbx := by
    rw [keep (by decide), m₁, Mem.readW_writeW_sep (sp 0 16 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sp 0 8 (by omega) (by omega) (by omega)) (by decide), Mem.readW_writeW_self64]
  have v8 : s₄.mem.readW (S + BitVec.ofNat 64 8) 64 = s.gpr .rbp := by
    rw [keep (by decide), m₁, Mem.readW_writeW_sep (sp 8 16 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  have v16 : s₄.mem.readW (S + BitVec.ofNat 64 16) 64 = s.gpr .r12 := by
    rw [keep (by decide), m₁, Mem.readW_writeW_self64]
  obtain ⟨s₅, run₅, rbx₅, rbp₅, r12₅, g₅, m₅⟩ : ∃ s₅, runBlock isa
      [VG.Impl.AesOcb.X86_64.ld .rbx .r12 0, VG.Impl.AesOcb.X86_64.ld .rbp .r12 8, VG.Impl.AesOcb.X86_64.ld .r12 .r12 16] s₄ = some s₅ ∧
      s₅.gpr .rbx = s.gpr .rbx ∧ s₅.gpr .rbp = s.gpr .rbp ∧ s₅.gpr .r12 = s.gpr .r12 ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem := by
    refine ⟨_, by orun [h12₄, rS (d := 0) (by decide), rS (d := 8) (by decide), rS (d := 16) (by decide), v0, v8,
      v16], ?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, h₁, h₂, h₃, ite_false]
    · rfl
  refine WP.of_runBlock ⟨s₅, run₅, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · have hr' := hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rbx₅
    · exact rbp₅
    · rw [g₅ _ (by decide) (by decide) (by decide), P₄.saved _ hr, g₃ _ hr, sv₂ _ hr, hsp₁]
    · exact r12₅
    all_goals rw [g₅ _ (by decide) (by decide) (by decide), P₄.saved _ hr, g₃ _ hr, sv₂ _ hr,
      g₁ _ (by decide) (by decide) (by decide) (by decide)]
  · -- The return address.
    have f₃ : Frame [⟨C + BitVec.ofNat 64 240, 16⟩] s₂.mem s₃.mem := by
      rw [m₃, show C + BitVec.ofNat 64 248 = C + BitVec.ofNat 64 240 + BitVec.ofNat 64 8 from (addr8 C 240).symm]
      exact frame_store2 _ _ _ _
    have fall : Frame [⟨C, 256⟩, ⟨S, 2560⟩, below (s.gpr .rsp) 8] s.mem s₄.mem := by
      refine (((f₁.sub fun r hr => ?_).trans (P₂.frame.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_)).trans
        (P₄.frame.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_S (by decide)⟩
        · rw [hsp₁]; exact ⟨_, by simp, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., sub_C (by decide)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., sub_C (by decide)⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_S (by decide)⟩
        · rw [hsp₃]; exact ⟨_, by simp, fun _ h => h⟩
    rw [m₅]
    exact fall.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Ar.retC
      · exact Ar.retS
      · exact Offset.base_disjoint_below _ (by have := Ar.sp; omega)) (by decide)
  · -- The key context.
    have hn : 16 * (KL / 4 + 6 + 1) ≤ 240 := by rcases Ar.klen with h | h | h <;> subst h <;> decide
    have k₃ : bytesAt s₃.mem C (16 * (KL / 4 + 6 + 1)) = Spec.Aes.expandKey (bytesAt s.mem Kp KL) := by
      rw [m₃, VG.Proof.AesCcm.X86_64.bytesAt_frame (show Frame [⟨C + BitVec.ofNat 64 240, 16⟩] s₂.mem
          ((s₂.mem.writeW (C + BitVec.ofNat 64 240) 0#64).writeW (C + BitVec.ofNat 64 248) 0#64) by
          rw [show C + BitVec.ofNat 64 248 = C + BitVec.ofNat 64 240 + BitVec.ofNat 64 8 from (addr8 C 240).symm]
          exact frame_store2 _ _ _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.base_disjoint C hn (by decide)) (by omega)]
      have := P₂.out
      rw [VG.Proof.AesCcm.X86_64.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.ks.sub_right (Region.sub_prefix (by decide)))
        (by omega)] at this
      exact this
    have k₄ : bytesAt s₄.mem C (16 * (KL / 4 + 6 + 1)) = Spec.Aes.expandKey (bytesAt s.mem Kp KL) := by
      rw [VG.Proof.AesCcm.X86_64.bytesAt_frame P₄.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.base_disjoint C hn (by decide)
        · exact (Ar.cs.sub_left (Region.sub_prefix (by omega))).sub_right (sub_S (by decide))
        · rw [hsp₃]; exact (Ar.stkC.sub_right (Region.sub_prefix (by omega))).symm) (by omega), k₃]
    refine ⟨?_, ?_⟩
    · rw [VG.Proof.AesCcm.X86_64.length_bytesAt, m₅]; exact k₄
    · have := P₄.enc (i := 0) (by decide)
      rw [show 16 * 0 = 0 from rfl, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
      show blockAtMem s₅.mem (C + BitVec.ofNat 64 240) = _
      rw [m₅, this, k₃, m₃,
        show C + BitVec.ofNat 64 248 = C + BitVec.ofNat 64 240 + BitVec.ofNat 64 8 from (addr8 C 240).symm,
        blockAtMem_store2, Spec.Ocb.aes, VG.Proof.AesCcm.X86_64.length_bytesAt]
      rfl

/-- `vg_aes_ocb_init`. -/
theorem init_wp (v : BlocksImpl) {s : State} (h : initX86_64.pre s) :
    WP isa (init (VG.Proof.AesOcb.X86_64.callees v)) s fun s' => gprPreserved s s' ∧ initX86_64.post s s' :=
  VG.Proof.AesOcb.X86_64.init_wp' v (IArgs.of h) rfl (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm rfl rfl

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.InitCT`. -/
section

/-!
# AES-OCB on x86-64: `vg_aes_ocb_init` is constant time

Untrusted: everything here is checked by Lean. The code between the calls
passes the taint analysis from the registers that are public (the
arguments, then the key context's address, the rounds and the scratch
buffer's address); the calls have the same arguments in both runs, by
correctness (`key_rel`, `blk_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem init_rel (v : BlocksImpl) {s₀ s₀' : State} {Kp C S : Addr} {KL : Nat} (Ar : VG.Proof.AesOcb.X86_64.IArgs s₀ Kp C S KL)
    (Ar' : VG.Proof.AesOcb.X86_64.IArgs s₀' Kp C S KL)
    (hdi : s₀.gpr .rdi = Kp) (hsi : s₀.gpr .rsi = BitVec.ofNat 64 KL) (hdx : s₀.gpr .rdx = C) (hcx : s₀.gpr .rcx = S)
    (hdi' : s₀'.gpr .rdi = Kp) (hsi' : s₀'.gpr .rsi = BitVec.ofNat 64 KL) (hdx' : s₀'.gpr .rdx = C)
    (hcx' : s₀'.gpr .rcx = S) (hsp : s₀.gpr .rsp = s₀'.gpr .rsp) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (init (VG.Proof.AesOcb.X86_64.callees v)) fun _ _ => True := by
  -- The first block.
  have first : ∀ {σ : State}, VG.Proof.AesOcb.X86_64.IArgs σ Kp C S KL → σ.gpr .rdi = Kp → σ.gpr .rsi = BitVec.ofNat 64 KL →
      σ.gpr .rdx = C → σ.gpr .rcx = S →
      WP isa (.block [st .rcx 0 .rbx, st .rcx 8 .rbp, st .rcx 16 .r12, mvr .rbx .rdx, mvr .rbp .rsi,
          .shift .shr .rbp 2, addi .rbp 6, mvr .r12 .rcx, addi .rcx scrO]) σ fun s₁ =>
        KCall s₁ Kp C (S + BitVec.ofNat 64 512) KL ∧ s₁.gpr .rsp = σ.gpr .rsp ∧ s₁.gpr .rbx = C ∧
          s₁.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₁.gpr .r12 = S ∧ s₁.rd = σ.rd ∧ s₁.wr = σ.wr :=
    fun A h₁ h₂ h₃ h₄ => by
      obtain ⟨s₁, run₁, rbx₁, rbp₁, r12₁, _, _, rd₁, wr₁, K₁, hsp₁⟩ := VG.Proof.AesOcb.X86_64.init1_ok A h₁ h₂ h₃ h₄
      exact WP.of_runBlock ⟨s₁, run₁, K₁, hsp₁, rbx₁, rbp₁, r12₁, rd₁, wr₁⟩
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp])
      (.block [st .rcx 0 .rbx, st .rcx 8 .rbp, st .rcx 16 .r12, mvr .rbx .rdx, mvr .rbp .rsi,
          .shift .shr .rbp 2, addi .rbp 6, mvr .r12 .rcx, addi .rcx scrO]) hc).isSome = true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [hdi, hdi']
    · rw [hsi, hsi']
    · rw [hdx, hdx']
    · rw [hcx, hcx']
    · exact hsp) hA).wp
    (F₁ := fun (s₁ : State) => KCall s₁ Kp C (S + BitVec.ofNat 64 512) KL ∧ s₁.gpr .rsp = s₀.gpr .rsp ∧ s₁.gpr .rbx = C ∧
      s₁.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₁.gpr .r12 = S ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr)
    (F₂ := fun (s₁ : State) => KCall s₁ Kp C (S + BitVec.ofNat 64 512) KL ∧ s₁.gpr .rsp = s₀'.gpr .rsp ∧ s₁.gpr .rbx = C ∧
      s₁.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₁.gpr .r12 = S ∧ s₁.rd = s₀'.rd ∧ s₁.wr = s₀'.wr)
    fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab; exact ⟨first Ar hdi hsi hdx hcx, first Ar' hdi' hsi' hdx' hcx'⟩
  -- The key schedule.
  have b := (VG.Proof.AesOcb.X86_64.key_rel v (P := fun s₁ s₂ => True ∧
      (KCall s₁ Kp C (S + BitVec.ofNat 64 512) KL ∧ s₁.gpr .rsp = s₀.gpr .rsp ∧ s₁.gpr .rbx = C ∧
        s₁.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₁.gpr .r12 = S ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr) ∧
      (KCall s₂ Kp C (S + BitVec.ofNat 64 512) KL ∧ s₂.gpr .rsp = s₀'.gpr .rsp ∧ s₂.gpr .rbx = C ∧
        s₂.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₂.gpr .r12 = S ∧ s₂.rd = s₀'.rd ∧ s₂.wr = s₀'.wr))
    fun s₁ s₂ h => ⟨_, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.1, h.2.2.2.1, hsp]⟩).wp
    (F₁ := fun (s₂ : State) => s₂.gpr .rsp = s₀.gpr .rsp ∧ s₂.gpr .rbx = C ∧ s₂.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧
      s₂.gpr .r12 = S ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr)
    (F₂ := fun (s₂ : State) => s₂.gpr .rsp = s₀'.gpr .rsp ∧ s₂.gpr .rbx = C ∧ s₂.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧
      s₂.gpr .r12 = S ∧ s₂.rd = s₀'.rd ∧ s₂.wr = s₀'.wr) fun s₁ s₂ h => by
      obtain ⟨_, ⟨K₁, sp₁, bx₁, bp₁, r₁, rd₁, wr₁⟩, ⟨K₂, sp₂, bx₂, bp₂, r₂, rd₂, wr₂⟩⟩ := h
      exact ⟨WP.mono (VG.Proof.AesOcb.X86_64.key_call v K₁) fun t P => ⟨by rw [P.saved _ (by decide), sp₁],
          by rw [P.saved _ (by decide), bx₁], by rw [P.saved _ (by decide), bp₁], by rw [P.saved _ (by decide), r₁],
          by rw [P.rd, rd₁], by rw [P.wr, wr₁]⟩,
        WP.mono (VG.Proof.AesOcb.X86_64.key_call v K₂) fun t P => ⟨by rw [P.saved _ (by decide), sp₂],
          by rw [P.saved _ (by decide), bx₂], by rw [P.saved _ (by decide), bp₂], by rw [P.saved _ (by decide), r₂],
          by rw [P.rd, rd₂], by rw [P.wr, wr₂]⟩⟩
  -- The zero block, enciphered.
  have third : ∀ {σ s₂ : State}, VG.Proof.AesOcb.X86_64.IArgs σ Kp C S KL → s₂.gpr .rsp = σ.gpr .rsp → s₂.gpr .rbx = C →
      s₂.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) → s₂.gpr .r12 = S → s₂.rd = σ.rd → s₂.wr = σ.wr →
      WP isa (.block [.alu .xor .rax (.reg .rax), st .rbx 240 .rax, st .rbx 248 .rax, mvr .rdi .rbx, mvr .rsi .rbp,
          mvr .rdx .rbx, addi .rdx 240, .mov .rcx (.imm 1), mvr .r8 .r12, addi .r8 scrO]) s₂ fun s₃ =>
        BCall s₃ C (C + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 512) (KL / 4 + 6) 1 ∧
          s₃.gpr .rsp = σ.gpr .rsp ∧ s₃.gpr .r12 = S := fun A sp bx bp r rd wr => by
      obtain ⟨s₃, run₃, g₃, _, _, _, B₃, hsp₃⟩ := VG.Proof.AesOcb.X86_64.init3_ok A bx bp r rd wr sp
      exact WP.of_runBlock ⟨s₃, run₃, B₃, hsp₃, by rw [g₃ _ (by decide), r]⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .rsp])
      (.block [.alu .xor .rax (.reg .rax), st .rbx 240 .rax, st .rbx 248 .rax, mvr .rdi .rbx, mvr .rsi .rbp,
          mvr .rdx .rbx, addi .rdx 240, .mov .rcx (.imm 1), mvr .r8 .r12, addi .r8 scrO]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have c := (RelCT.taint (A := taint) _ (fun s₁ s₂ (h : True ∧
      (s₁.gpr .rsp = s₀.gpr .rsp ∧ s₁.gpr .rbx = C ∧ s₁.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧
        s₁.gpr .r12 = S ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr) ∧
      (s₂.gpr .rsp = s₀'.gpr .rsp ∧ s₂.gpr .rbx = C ∧ s₂.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧
        s₂.gpr .r12 = S ∧ s₂.rd = s₀'.rd ∧ s₂.wr = s₀'.wr)) => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2.1, h.2.2.2.2.1]
      · rw [h.2.1.2.2.2.1, h.2.2.2.2.2.1]
      · rw [h.2.1.1, h.2.2.1, hsp]) hB).wp
    (F₁ := fun (s₃ : State) => BCall s₃ C (C + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 512) (KL / 4 + 6) 1 ∧
      s₃.gpr .rsp = s₀.gpr .rsp ∧ s₃.gpr .r12 = S)
    (F₂ := fun (s₃ : State) => BCall s₃ C (C + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 512) (KL / 4 + 6) 1 ∧
      s₃.gpr .rsp = s₀'.gpr .rsp ∧ s₃.gpr .r12 = S) fun s₁ s₂ h => by
      obtain ⟨_, ⟨sp₁, bx₁, bp₁, r₁, rd₁, wr₁⟩, ⟨sp₂, bx₂, bp₂, r₂, rd₂, wr₂⟩⟩ := h
      exact ⟨third Ar sp₁ bx₁ bp₁ r₁ rd₁ wr₁, third Ar' sp₂ bx₂ bp₂ r₂ rd₂ wr₂⟩
  have d := (blk_rel (name := (VG.Proof.AesOcb.X86_64.callees v).enc.name) v.encOk v.encCt (P := fun s₁ s₂ => True ∧
      (BCall s₁ C (C + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 512) (KL / 4 + 6) 1 ∧ s₁.gpr .rsp = s₀.gpr .rsp ∧
        s₁.gpr .r12 = S) ∧
      (BCall s₂ C (C + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 512) (KL / 4 + 6) 1 ∧ s₂.gpr .rsp = s₀'.gpr .rsp ∧
        s₂.gpr .r12 = S))
    fun s₁ s₂ h => ⟨_, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.1, h.2.2.2.1, hsp]⟩).wp
    (F₁ := fun (s : State) => s.gpr .r12 = S) (F₂ := fun (s : State) => s.gpr .r12 = S) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call v.encOk v.encNosp v.encDepth h.2.1.1) fun t P => by rw [P.saved _ (by decide), h.2.1.2.2],
        WP.mono (blk_call v.encOk v.encNosp v.encDepth h.2.2.1) fun t P => by rw [P.saved _ (by decide), h.2.2.2.2]⟩
  -- The registers back.
  obtain ⟨_, hE⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r12])
      (.block [VG.Impl.AesOcb.X86_64.ld .rbx .r12 0, VG.Impl.AesOcb.X86_64.ld .rbp .r12 8, VG.Impl.AesOcb.X86_64.ld .r12 .r12 16]) hc).isSome = true := ⟨_, by taint_decide⟩
  have e := RelCT.taint (A := taint) _ (fun s₁ s₂ (h : True ∧ s₁.gpr .r12 = S ∧ s₂.gpr .r12 = S) => by
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1, h.2.2]) hE
  unfold init
  exact RelCT.seq a (RelCT.seq b (RelCT.seq c (RelCT.seq d e)))

/-- `vg_aes_ocb_init` is constant time. -/
theorem init_ct (v : BlocksImpl) : ConstantTime isa initX86_64.pre initX86_64.pub (init (VG.Proof.AesOcb.X86_64.callees v)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have A₂ := IArgs.of h₂
  rw [← q1, ← q2, ← q3, ← q4] at A₂
  exact (VG.Proof.AesOcb.X86_64.init_rel v (IArgs.of h₁) A₂ rfl (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm rfl rfl q1.symm
    (by rw [← q2]; exact (VG.Proof.AesOcb.X86_64.ofNat_toNat64 _).symm) q3.symm q4.symm q5 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.Verified`. -/
section

/-!
# AES-OCB on x86-64: `Verified`

Correctness and constant time (for any implementations `v` of
`vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks` and `vg_aes_expand_key_scratch`),
a state satisfying each precondition, and the shared contracts of
`Spec/Ocb/Contract.lean` with the working space as a last argument
(`Proof/AesOcb/Scratch.lean`), with 8 bytes of stack: the return address of
the calls, whose callees use no stack. `Frame.lean` allocates the working
space.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem seal_mx (v : BlocksImpl) : («seal» (VG.Proof.AesOcb.X86_64.callees v)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«seal», front, tagOut, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, VG.Impl.AesOcb.X86_64.body,
    whole, pass, nextOffset, VG.Impl.AesOcb.X86_64.rest, padCk, xorPad, tag, callBlocks, VG.Proof.AesOcb.X86_64.callees, Code.allInstrs, v.encMxcsr, v.decMxcsr,
    Bool.true_and, Bool.and_true, ↓reduceIte]
  decide +kernel

theorem open_mx (v : BlocksImpl) : («open» (VG.Proof.AesOcb.X86_64.callees v)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«open», front, recv, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, VG.Impl.AesOcb.X86_64.body,
    whole, pass, nextOffset, VG.Impl.AesOcb.X86_64.rest, padCk, xorPad, tag, cmp, mask, callBlocks, VG.Proof.AesOcb.X86_64.callees, Code.allInstrs, v.encMxcsr,
    v.decMxcsr, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_mx (v : BlocksImpl) : (init (VG.Proof.AesOcb.X86_64.callees v)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, VG.Proof.AesOcb.X86_64.callees, Code.allInstrs, v.encMxcsr, v.expandMxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem seal_spSafe (v : BlocksImpl) : («seal» (VG.Proof.AesOcb.X86_64.callees v)).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«seal», front, tagOut, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, VG.Impl.AesOcb.X86_64.body,
    whole, pass, nextOffset, VG.Impl.AesOcb.X86_64.rest, padCk, xorPad, tag, callBlocks, VG.Proof.AesOcb.X86_64.callees, Code.all, v.encSpSafe, v.decSpSafe,
    Bool.true_and, Bool.and_true, ↓reduceIte]
  decide +kernel

theorem open_spSafe (v : BlocksImpl) : («open» (VG.Proof.AesOcb.X86_64.callees v)).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«open», front, recv, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill, lNtz, hashSum, hashRest, padTo, VG.Impl.AesOcb.X86_64.body,
    whole, pass, nextOffset, VG.Impl.AesOcb.X86_64.rest, padCk, xorPad, tag, cmp, mask, callBlocks, VG.Proof.AesOcb.X86_64.callees, Code.all, v.encSpSafe,
    v.decSpSafe, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_spSafe (v : BlocksImpl) : (init (VG.Proof.AesOcb.X86_64.callees v)).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, VG.Proof.AesOcb.X86_64.callees, Code.all, v.encSpSafe, v.expandSpSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem seal_correct (v : BlocksImpl) (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa («seal» (VG.Proof.AesOcb.X86_64.callees v)) s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.AesOcb.X86_64.seal_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.AesOcb.X86_64.seal_mx v) he hg, hp⟩

theorem open_correct (v : BlocksImpl) (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa («open» (VG.Proof.AesOcb.X86_64.callees v)) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.AesOcb.X86_64.open_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.AesOcb.X86_64.open_mx v) he hg, hp⟩

theorem init_correct (v : BlocksImpl) (s : State) (hs : initX86_64.pre s) :
    ∃ t s', Exec isa (init (VG.Proof.AesOcb.X86_64.callees v)) s t s' ∧ abiPreserved s s' ∧ initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.AesOcb.X86_64.init_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.AesOcb.X86_64.init_mx v) he hg, hp⟩

/-- A state satisfying the precondition of `vg_aes_ocb_seal`: a 1-byte nonce,
no associated data, no data, a 4-byte tag at `0x3000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 1 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8020 then 4 else if a = 0x8019 then 0x30 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x2100, 0⟩, ⟨0x8008, 40⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ocb_init`: a 16-byte key. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩]

theorem seal_verified (v : BlocksImpl) :
    Verified X86_64.target («seal» (VG.Proof.AesOcb.X86_64.callees v)) (Proof.AesOcb.sealScratchContract X86_64.abi 8) :=
  Verified.of_correct (VG.Proof.AesOcb.X86_64.seal_correct v) (VG.Proof.AesOcb.X86_64.seal_ct v) (by
    sig_implies [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Spec.Ocb.sealPost, Proof.AesOcb.sealX86_64, Proof.AesOcb.sealPreX, Proof.AesOcb.oneFacts,
      Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad, Proof.AesOcb.aData, Proof.AesOcb.aTag,
      Proof.AesOcb.aWork, Proof.AesOcb.onePub, X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8,
      Proof.AesOcb.ret, Proof.AesOcb.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
      List.range.loop, VG.X86_64.below, X86_64.argRegs] [sealSat] using VG.Proof.AesOcb.X86_64.sealSat)

theorem init_verified (v : BlocksImpl) :
    Verified X86_64.target (init (VG.Proof.AesOcb.X86_64.callees v)) (Proof.AesOcb.initScratchContract X86_64.abi 8) :=
  Verified.of_correct (VG.Proof.AesOcb.X86_64.init_correct v) (VG.Proof.AesOcb.X86_64.init_ct v) (by
    sig_implies [Proof.AesOcb.initScratchContract, Proof.AesOcb.initScratchSig, Spec.Ocb.initPre,
      Spec.Ocb.initPost, Proof.AesOcb.initX86_64, Proof.AesOcb.stk8, Proof.AesOcb.ret, X86_64.abi, X86_64.argRegs,
      VG.X86_64.below] [initSat] using VG.Proof.AesOcb.X86_64.initSat)

/-- A state satisfying the precondition of `vg_aes_ocb_open`: as `sealSat`,
with the tag read only. -/
def openSat : State := { VG.Proof.AesOcb.X86_64.sealSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x2100, 0⟩, ⟨0x3000, 4⟩, ⟨0x8008, 40⟩]
  wr := [⟨0, 0⟩, ⟨0, 2560⟩] }

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified (v : BlocksImpl) :
    Verified X86_64.target («open» (VG.Proof.AesOcb.X86_64.callees v)) (Proof.AesOcb.openScratchContract X86_64.abi 8) :=
  Verified.of_correct (VG.Proof.AesOcb.X86_64.open_correct v) (VG.Proof.AesOcb.X86_64.open_ct v)
    { pre := by sig_implies_pre [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs]
      post := by sig_implies_post [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs]
        sig_simp [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs] [openSat, sealSat] using VG.Proof.AesOcb.X86_64.openSat }

end VG.Proof.AesOcb.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesOcb.X86_64.Frame`. -/
section

/-!
# AES-OCB on x86-64, with its working space on the stack

Every function runs its code, proved with the working space as its last
argument (`Verified.lean`), in a frame that allocates it. `init`'s working
space is in a register (`rcx`): its frame of 2568 bytes holds the 2560
bytes and 8 more to keep `rsp` aligned (`Verified.stackScratch`). The
working space of `seal` and `open` is passed on the stack after the six
argument registers and four other stack arguments (`data`, `len`, `tag` and
`tag_len`), so their frame of 2608 bytes holds the 2560 bytes of working
space, a copy of those four arguments, the word that stands for the return
address and the address of the working space (`Verified.stackArgScratch`).
The code's own calls use 8 bytes below the frame, the return address, as
`vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks` and `vg_aes_expand_key_scratch` use
no stack. `open`'s leak, whether it succeeds, reads only its buffers
(`openLeak_local`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

variable (v : BlocksImpl)

theorem init_xdepth : (init (VG.Proof.AesOcb.X86_64.callees v)).x86_64Depth ≤ 8 := by
  simp only [init, VG.Proof.AesOcb.X86_64.callees, Code.x86_64Depth, v.encNoStack, v.expandNoStack]
  decide +kernel

theorem seal_xdepth : («seal» (VG.Proof.AesOcb.X86_64.callees v)).x86_64Depth ≤ 8 := by
  simp only [«seal», front, tagOut, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill, lNtz,
    hashSum, hashRest, padTo, VG.Impl.AesOcb.X86_64.body, whole, pass, nextOffset, VG.Impl.AesOcb.X86_64.rest, padCk, xorPad, tag, callBlocks, VG.Proof.AesOcb.X86_64.callees,
    Code.x86_64Depth, v.encNoStack, v.decNoStack, ↓reduceIte]
  decide +kernel

theorem open_xdepth : («open» (VG.Proof.AesOcb.X86_64.callees v)).x86_64Depth ≤ 8 := by
  simp only [«open», front, recv, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill, lNtz,
    hashSum, hashRest, padTo, VG.Impl.AesOcb.X86_64.body, whole, pass, nextOffset, VG.Impl.AesOcb.X86_64.rest, padCk, xorPad, tag, cmp, mask, callBlocks, VG.Proof.AesOcb.X86_64.callees,
    Code.x86_64Depth, v.encNoStack, v.decNoStack, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

/-- A state satisfying `vg_aes_ocb_init`'s precondition, without the working
space. -/
def initFrameSat : State := { VG.Proof.AesOcb.X86_64.initSat with
                                           wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Ocb.initContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Ocb.initContract, Spec.Ocb.initSig, Spec.Ocb.initPre, Spec.Ocb.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using VG.Proof.AesOcb.X86_64.initFrameSat

theorem init_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (init (VG.Proof.AesOcb.X86_64.callees v)))
      (Spec.Ocb.initContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratch (sig := Spec.Ocb.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Ocb.initPre X86_64.abi.ptrBits) (post := Spec.Ocb.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 8) (bytes := 2568) (VG.Proof.AesOcb.X86_64.init_verified v) (by decide) (by decide)
    (by decide) (VG.Proof.AesOcb.X86_64.init_spSafe v) (VG.Proof.AesOcb.X86_64.init_xdepth v) VG.Proof.AesOcb.X86_64.initFrameSat_pre

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space. -/
def sealFrameSat : State :=
  { VG.Proof.AesOcb.X86_64.sealSat with
                 rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x2100, 0⟩, ⟨0x8008, 32⟩], wr := [⟨0, 0⟩, ⟨0x3000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ocb.sealContract X86_64.abi 2616).pre s := by
  implies_sat [Spec.Ocb.sealContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Spec.Ocb.sealPost,
    X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using VG.Proof.AesOcb.X86_64.sealFrameSat

theorem seal_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («seal» (VG.Proof.AesOcb.X86_64.callees v)))
      (Spec.Ocb.sealContract X86_64.abi 2616) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ocb.sealPre X86_64.abi.ptrBits)
    (post := Spec.Ocb.sealPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 2608) (VG.Proof.AesOcb.X86_64.seal_verified v) (by decide) (by decide) (by decide)
    (VG.Proof.AesOcb.X86_64.seal_spSafe v) (VG.Proof.AesOcb.X86_64.seal_xdepth v) (VG.Proof.AesOcb.sealPre_local _) (VG.Proof.AesOcb.sealPost_local _) VG.Proof.AesOcb.X86_64.sealFrameSat_pre

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space. -/
def openFrameSat : State :=
  { VG.Proof.AesOcb.X86_64.sealSat with
                 rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x2100, 0⟩, ⟨0x3000, 4⟩, ⟨0x8008, 32⟩], wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ocb.openContract X86_64.abi 2616).pre s := by
  implies_sat [Spec.Ocb.openContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Spec.Ocb.openPost,
    Spec.Ocb.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, sealSat] using VG.Proof.AesOcb.X86_64.openFrameSat

theorem open_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («open» (VG.Proof.AesOcb.X86_64.callees v)))
      (Spec.Ocb.openContract X86_64.abi 2616) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ocb.openPre X86_64.abi.ptrBits)
    (post := Spec.Ocb.openPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.Ocb.openLeak X86_64.abi.ptrBits)) (bytes := 2608) (VG.Proof.AesOcb.X86_64.open_verified v)
    (by decide) (by decide) (by decide) (VG.Proof.AesOcb.X86_64.open_spSafe v) (VG.Proof.AesOcb.X86_64.open_xdepth v) (VG.Proof.AesOcb.openPre_local _)
    (VG.Proof.AesOcb.openPost_local _) VG.Proof.AesOcb.X86_64.openFrameSat_pre (hleak := VG.Proof.AesOcb.openLeak_local _)

end VG.Proof.AesOcb.X86_64

end
