module

public import VerifiedGarbage.Impl.Camellia.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Camellia.Common
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Camellia.RISCV64.Keys
import VerifiedGarbage.Proof.Camellia.RISCV64.Prologue
import VerifiedGarbage.Proof.Camellia.RISCV64.Group
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Storing the subkeys on RISC-V

As on PPC64LE (`Proof/Camellia/PPC64LE/KeyStore.lean`). The key schedule
keeps the 64-bit halves of `KL`, `KR`, `KA` and `KB` as ECB loads them:
little-endian words of their big-endian bytes (`WordOf`), whose bytes read
big-endian (`loadBE64`) are the halves as numbers (`be64_of_wordOf`).

`storeSubkeys_ok`: with the halves of `KL`, `KR`, `KA` and `KB` in their
registers (`hiReg`, `loReg`), `storeSubkeys ks` stores each subkey of `ks`,
the half of a rotation (`rotHalf`), big-endian a byte at a time
(`storeBE`), at its word of the schedule at `a2`.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.Impl.Camellia.RISCV64 VG.WriteBytes VG.Impl.Words.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 movR shlI shrI)

/-! ## Halves as little-endian words -/

/-- A word is its bytes, the most significant first. -/
theorem bytes_concat (H : BitVec 64) :
    H = Camellia.byteOf H 0 ++ Camellia.byteOf H 1 ++ Camellia.byteOf H 2 ++ Camellia.byteOf H 3 ++
      Camellia.byteOf H 4 ++ Camellia.byteOf H 5 ++ Camellia.byteOf H 6 ++ Camellia.byteOf H 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  simp only [Camellia.byteOf, BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  repeat' split
  all_goals (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega)

/-- The bytes of such a word, read big-endian, are the half. -/
theorem be64_of_wordOf {m : Mem} {p : Addr} {off : Nat} {H : BitVec 64}
    (hw : WordOf (m.readW (p + BitVec.ofNat 64 off) 64) H) : ByteLoad.be64 m p off = H := by
  have hb : ∀ i < 8, m (p + BitVec.ofNat 64 (off + i)) = Camellia.byteOf H i := fun i hi =>
    BitVec.eq_of_getLsbD_eq fun j hj => by
      rw [← hw i hi j hj, Camellia.readW64_bit _ _ hi hj, Offset.add_add]
  have h0 := hb 0 (by decide)
  rw [Nat.add_zero] at h0
  rw [ByteLoad.be64, h0, hb 1 (by decide), hb 2 (by decide), hb 3 (by decide), hb 4 (by decide),
    hb 5 (by decide), hb 6 (by decide), hb 7 (by decide)]
  exact (bytes_concat H).symm

/-- Byte `j` of a word stored big-endian is byte `j` of the word, the most significant first. -/
theorem writeBytes_be_byte (m : Mem) (a : Addr) (w : BitVec 64) {j : Nat} (hj : j < 8) :
    writeBytes m a (ByteLoad.beBytes 8 w) (a + BitVec.ofNat 64 j) = Camellia.byteOf w j := by
  simp only [writeBytes, ByteLoad.beBytes_length, Mem.sub_ofNat_toNat a (show j < 2 ^ 64 by omega), hj,
    ↓reduceIte]
  simp only [ByteLoad.beBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, Camellia.byteOf]
  rw [show 8 * (8 - 1 - j) = 56 - 8 * j by omega]

/-! ## Single instructions -/

theorem shift_ok (s : State) (left : Bool) (d n : Reg) {sh : Nat} (h : sh < 64) :
    ∃ s', runBlock isa [if left then shlI d n sh else shrI d n sh] s = some s' ∧
      s'.gpr d = (if left then s.gpr n <<< sh else s.gpr n >>> sh) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases left
  · exact ⟨s.write d (s.gpr n >>> sh), by
      simp only [Bool.false_eq_true, ↓reduceIte, shrI, runBlock_cons, exec_shift_d h, runStep_some, runBlock_nil],
      RegUpd.gpr_write_self _ _ _, fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩
  · exact ⟨s.write d (s.gpr n <<< sh), by
      simp only [↓reduceIte, shlI, runBlock_cons, exec_shift_d h, runStep_some, runBlock_nil],
      RegUpd.gpr_write_self _ _ _, fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩

theorem orr_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [orR d n m] s = some s' ∧ s'.gpr d = s.gpr n ||| s.gpr m ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write d (s.gpr n ||| s.gpr m), by
    simp only [orR, runBlock_cons, runStep_some, runBlock_nil, exec_logic],
    RegUpd.gpr_write_self _ _ _,
    fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩

/-- `storeBE 8 t0 t1 a2 d`: `t0` big-endian at `d(a2)`. -/
theorem strBE_ok (s : State) {d : Nat} (hd : d + 8 ≤ 2048)
    (hw : InRegions s.wr (s.gpr .a2 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa (storeBE 8 t0 t1 .a2 d) s = some s' ∧
      s'.mem = writeBytes s.mem (s.gpr .a2 + BitVec.ofNat 64 d) (ByteLoad.beBytes 8 (s.gpr t0)) ∧
      (∀ r, r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e', h'⟩ := WP.runBlock_of (ByteLoad.storeBE_ok (s := s) (v := t0) (tmp := t1) (n := .a2) (off := d)
    (w := 8) (by decide) (by decide) (by decide) (by decide) hd (fun j hj => ByteLoad.in_byte' hw hj))
  subst h'
  exact ⟨_, e', rfl, fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl⟩

/-! ## The subkeys -/

theorem hiReg_ne : ∀ v < 4, hiReg v ≠ t0 ∧ hiReg v ≠ t1 ∧ loReg v ≠ t0 ∧ loReg v ≠ t1 := by decide

/-- One subkey, stored big-endian at word `i` of `a2`. -/
theorem subkey_ok (s : State) {i v r : Nat} {hi : Bool} (hv : v < 4) (hi34 : i < 34)
    (hw : InRegions s.wr (s.gpr .a2 + BitVec.ofNat 64 (8 * i)) 8) :
    ∃ s', runBlock isa (subkey i v r hi) s = some s' ∧
      s'.mem = writeBytes s.mem (s.gpr .a2 + BitVec.ofNat 64 (8 * i))
        (ByteLoad.beBytes 8 (Camellia.rotHalf (s.gpr (hiReg v)) (s.gpr (loReg v)) r hi)) ∧
      (∀ r', r' ≠ t0 → r' ≠ t1 → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨n1, n2, n3, n4⟩ := hiReg_ne v hv
  have hr3 : Reg.a2 ≠ t0 := by decide
  have hx1 : Reg.a2 ≠ t1 := by decide
  have hd : 8 * i + 8 ≤ 2048 := by omega_arith
  -- The two halves, `a` first.
  let a := if (r < 64) = (hi = true) then hiReg v else loReg v
  let b := if (r < 64) = (hi = true) then loReg v else hiReg v
  have ha : a ≠ t0 ∧ a ≠ t1 := by simp only [a]; split <;> exact ⟨by assumption, by assumption⟩
  have hb : b ≠ t0 ∧ b ≠ t1 := by simp only [b]; split <;> exact ⟨by assumption, by assumption⟩
  have hrot : Camellia.rotHalf (s.gpr (hiReg v)) (s.gpr (loReg v)) r hi =
      if r % 64 = 0 then s.gpr a else (s.gpr a <<< (r % 64)) ||| (s.gpr b >>> (64 - r % 64)) := by
    by_cases h64 : r < 64 <;> cases hi <;> simp [Camellia.rotHalf, a, b, h64]
  have hcode : subkey i v r hi =
      (if r % 64 = 0 then [movR t0 a] else [shlI t0 a (r % 64), shrI t1 b (64 - r % 64), orR t0 t0 t1]) ++
        storeBE 8 t0 t1 .a2 (8 * i) := by
    by_cases h64 : r < 64 <;> cases hi <;> simp [subkey, a, b, h64]
  by_cases h0 : r % 64 = 0
  · obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s t0 a
    obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := strBE_ok s₁ hd (by rw [wr₁, o₁ _ hr3]; exact hw)
    refine ⟨s₃, by rw [hcode, ite_eq_left h0, runBlock_append', e₁, Option.bind_some, e₃], ?_, ?_, ?_, ?_⟩
    · rw [m₃, m₁, o₁ _ hr3, r₁, hrot, ite_eq_left h0]
    · intro r' h1 h2; rw [g₃ _ h2, o₁ _ h1]
    · rw [rd₃, rd₁]
    · rw [wr₃, wr₁]
  · obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := shift_ok s true t0 a (sh := r % 64) (by omega_arith)
    obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := shift_ok s₁ false t1 b (sh := 64 - r % 64) (by omega_arith)
    obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := orr_ok s₂ t0 t0 t1
    have g₃ : ∀ r', r' ≠ t0 → r' ≠ t1 → s₃.gpr r' = s.gpr r' := fun r' h1 h2 => by
      rw [o₃ _ h1, o₂ _ h2, o₁ _ h1]
    obtain ⟨s₅, e₅, m₅, g₅, rd₅, wr₅⟩ := strBE_ok s₃ hd (by rw [wr₃, wr₂, wr₁, g₃ _ hr3 hx1]; exact hw)
    refine ⟨s₅, by
      rw [hcode, ite_eq_right h0, show ([shlI t0 a (r % 64), shrI t1 b (64 - r % 64), orR t0 t0 t1] :
          List Instr) = [if true then shlI t0 a (r % 64) else shrI t0 a (r % 64)] ++
          ([if false then shlI t1 b (64 - r % 64) else shrI t1 b (64 - r % 64)] ++ [orR t0 t0 t1]) from rfl,
        runBlock_append', runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some, e₃,
        Option.bind_some, e₅], ?_, ?_, ?_, ?_⟩
    · have v0 : s₂.gpr t0 = s.gpr a <<< (r % 64) := by
        rw [o₂ _ (by decide : t0 ≠ t1), r₁]; rfl
      have v1 : s₂.gpr t1 = s.gpr b >>> (64 - r % 64) := by
        rw [r₂, o₁ _ hb.1]; rfl
      rw [m₅, m₃, m₂, m₁, g₃ _ hr3 hx1, r₃, v0, v1, hrot, ite_eq_right h0]
    · intro r' h1 h2; rw [g₅ _ h2, g₃ _ h1 h2]
    · rw [rd₅, rd₃, rd₂, rd₁]
    · rw [wr₅, wr₃, wr₂, wr₁]

theorem q_ne_t (n : Nat) : q n ≠ t0 ∧ q n ≠ t1 := by
  unfold q; split <;> decide

theorem regs_ne_t (x : Nat) : hiReg x ≠ t0 ∧ hiReg x ≠ t1 ∧ loReg x ≠ t0 ∧ loReg x ≠ t1 :=
  ⟨(q_ne_t _).1, (q_ne_t _).2, (q_ne_t _).1, (q_ne_t _).2⟩

/-- The subkey words `ks` from word `n` of `a2` on. -/
theorem storeSubkeys_ok (ks : List (Nat × Nat × Bool)) (hv : ∀ k ∈ ks, k.1 < 4) :
    ∀ (n : Nat) (s : State), (∀ i < ks.length, InRegions s.wr (s.gpr .a2 + BitVec.ofNat 64 (8 * (n + i))) 8) →
      n + ks.length ≤ 34 →
    ∃ s', runBlock isa ((ks.zipIdx n).flatMap fun ((v, r, hi), i) => subkey i v r hi) s = some s' ∧
      (∀ i < ks.length, ∀ j < 8,
        s'.mem (s.gpr .a2 + BitVec.ofNat 64 (8 * (n + i) + j)) =
          Camellia.byteOf (Camellia.rotHalf (s.gpr (hiReg (ks.getD i (0, 0, true)).1))
            (s.gpr (loReg (ks.getD i (0, 0, true)).1)) (ks.getD i (0, 0, true)).2.1
            (ks.getD i (0, 0, true)).2.2) j) ∧
      Frame [⟨s.gpr .a2 + BitVec.ofNat 64 (8 * n), 8 * ks.length⟩] s.mem s'.mem ∧
      (∀ r', r' ≠ t0 → r' ≠ t1 → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction ks with
  | nil => intro n s _ _; exact ⟨s, rfl, fun i hi => by simp at hi, Frame.refl _ _, fun _ _ _ => rfl, rfl, rfl⟩
  | cons k ks ih =>
    intro n s hw hfit
    obtain ⟨v, r, hi⟩ := k
    have hv0 : v < 4 := hv _ List.mem_cons_self
    simp only [List.length_cons] at hfit
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := subkey_ok s (i := n) (r := r) (hi := hi) hv0 (by omega_arith)
      (by simpa using hw 0 (by simp))
    have hx2 : s₁.gpr .a2 = s.gpr .a2 := g₁ _ (by decide) (by decide)
    obtain ⟨s', e', b', f', g', rd', wr'⟩ := ih (fun k hk => hv k (List.mem_cons_of_mem _ hk)) (n + 1) s₁
      (fun i hi => by
        rw [wr₁, hx2, show n + 1 + i = n + (i + 1) by omega_arith]
        exact hw (i + 1) (by simp; omega_arith)) (by omega_arith)
    refine ⟨s', by
      rw [List.zipIdx_cons, List.flatMap_cons, runBlock_append', e₁, Option.bind_some]; exact e',
      fun i hi j hj => ?_, ?_, fun r' h1 h2 => by rw [g' r' h1 h2, g₁ r' h1 h2], by rw [rd', rd₁],
      by rw [wr', wr₁]⟩
    · cases i with
      | zero =>
        have hout : ∀ R ∈ [(⟨s₁.gpr .a2 + BitVec.ofNat 64 (8 * (n + 1)), 8 * ks.length⟩ : Region)],
            ¬ R.Contains (s.gpr .a2 + BitVec.ofNat 64 (8 * (n + 0) + j)) 1 := fun R hR => by
          simp only [List.mem_singleton] at hR; subst hR; rw [hx2]
          by_cases h0 : ks.length = 0
          · simp only [Region.Contains, h0]; omega_arith
          · exact not_contains_off _ (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith)
        rw [f' _ hout, m₁, Nat.add_zero, ← Offset.add_add, writeBytes_be_byte _ _ _ hj]
        simp only [List.getD_cons_zero]
      | succ i =>
        have := b' i (by simp at hi; omega_arith) j hj
        simp only [hx2, g₁ _ (regs_ne_t _).1 (regs_ne_t _).2.1,
          g₁ _ (regs_ne_t _).2.2.1 (regs_ne_t _).2.2.2] at this
        rw [show n + (i + 1) = n + 1 + i by omega_arith, this, List.getD_cons_succ]
    · have f₁ : Frame [⟨s.gpr .a2 + BitVec.ofNat 64 (8 * n), 8 * ((v, r, hi) :: ks).length⟩] s.mem s₁.mem := by
        rw [m₁]; exact writeBytes_frame _ _ _ (by
          simp only [ByteLoad.beBytes_length, List.length_cons]
          simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith)
      refine f₁.trans (f'.sub fun R hR => ⟨_, List.mem_singleton_self _, ?_⟩)
      simp only [List.mem_singleton] at hR; subst hR
      rw [hx2]
      exact VG.Offset.sub _ (by omega_arith) (by simp; omega_arith)

end VG.Proof.Camellia.RISCV64
