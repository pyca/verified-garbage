module

public import VerifiedGarbage.Proof.Camellia.RISCV64.KaKb
public import VerifiedGarbage.Proof.Camellia.RISCV64.Prologue
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Camellia.RISCV64.Group
public import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Camellia.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Camellia.Bitsliced
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.RISCV64.Straight
public import VerifiedGarbage.Proof.Camellia.Scratch
public import VerifiedGarbage.Proof.Camellia.RISCV64.KeyContract
public import VerifiedGarbage.Proof.Camellia.RISCV64.Core
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Camellia.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad

/-! ### `Camellia.RISCV64.KeyStore`, which only this module used -/

section

/-!
# Storing the subkeys on RISC-V

As on PPC64LE (`Proof/Camellia/PPC64LE/KeyVerified.lean`). The key schedule
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
  all_goals (rw [decide_eq_true (by omega_arith), Bool.true_and]; congr 1; omega_arith)

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
  simp only [writeBytes, ByteLoad.beBytes_length, Mem.sub_ofNat_toNat a (show j < 2 ^ 64 by omega_using [hj]), hj,
    ↓reduceIte]
  simp only [ByteLoad.beBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, Camellia.byteOf]
  rw [show 8 * (8 - 1 - j) = 56 - 8 * j by omega_using []]

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

end

end

/-! ### `Camellia.RISCV64.ExpandKey`, which only this module used -/

section

/-! ### `Camellia.RISCV64.KeySetup`, which only this module used -/

section

/-!
# The Camellia key schedule on RISC-V: its parts

As on PPC64LE (`Proof/Camellia/PPC64LE/KeySetup.lean`): the prologue saves
the callee-saved registers, sets the masks and stores the planes of
`Sigma1 … Sigma6` as a table of subkeys (`ekPrologue_ok`; each plane built
by `movImm64` and stored: `sigmaStores_ok`); `loadKey_wp` copies `KL` and
`KR` into their slots a byte at a time, and `loadValues_ok` reads the four
values big-endian into registers.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG.Impl.Camellia (bytePos keyPlane sigmas)
open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Camellia.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 t2 u7 kp movR ldS stS xorR notR)
open VG.Proof.Camellia (HalfRel pair hiW loW pos)

/-! ## Single instructions -/

/-- `sd r, 8 k(sb)`, as slots. -/
theorem st_ok {s : State} {k : Nat} (r : Reg) (hal : (s.gpr sb).toNat % 8 = 0)
    (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr) (hk : k < keySlot) :
    ∃ s', runBlock isa [stS k r] s = some s' ∧ slotW s' k = s.gpr r ∧
      (∀ j < slots, j ≠ k → slotW s' j = slotW s j) ∧ s'.gpr = s.gpr ∧
      Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hk' : k < slots := by rw [keySlot_eq] at hk; rw [slots_eq]; omega_arith
  obtain ⟨s', e, m, g, rd, wr⟩ := stS_slot (k := k) r rfl hal hscr hk
  refine ⟨s', e, ?_, fun j hj hjk => ?_, g, by rw [m]; exact frame_slot _ hk', rd, wr⟩
  · rw [slotW_store m g hk' hk', ite_eq_left rfl]
  · rw [slotW_store m g hj hk', ite_eq_right hjk]

/-! ## The table of `Sigma1 … Sigma6` -/

/-- Plane `j` of the constant `x`, built in `t0` and stored to the entry at `kp`. -/
def sigmaStore (x : BitVec 64) (j : Nat) : List Instr :=
  Impl.Words64.RISCV64.movImm64 t0 t1 (keyPlane x j) ++ [.store .d t0 kp (8 * j)]

theorem sigmaOne_eq (x : BitVec 64) :
    sigmaOne x = (List.range 8).flatMap (sigmaStore x) ++ ([.addi kp kp 64] : List Instr) := rfl

/-- The planes stored so far. -/
structure SigInv (x : BitVec 64) (s : State) (n : Nat) (s' : State) : Prop where
  planes : ∀ j < n, s'.mem.readW (wordAddr (s.gpr kp) j) 64 = keyPlane x j
  frame : Frame [⟨s.gpr kp, 64⟩] s.mem s'.mem
  regs : ∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The stores of `sigmaOne x`: the planes of `x` to the entry at `kp`. -/
theorem sigmaStores_ok (x : BitVec 64) (s : State) (hal : (s.gpr kp).toNat % 8 = 0)
    (hw : ∀ j < 8, InRegions s.wr (s.gpr kp + BitVec.ofNat 64 (8 * j)) 8) :
    ∃ s', runBlock isa ((List.range 8).flatMap (sigmaStore x)) s = some s' ∧ SigInv x s 8 s' := by
  refine WP.runBlock_of (wp_range_flatMap (M := isa) (SigInv x s) (fun k s₁ hk h => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by omega_using []), Frame.refl _ _, fun _ _ _ => rfl, rfl, rfl⟩)
  rw [sigmaStore, WP.block_append_iff (M := isa)]
  refine WP.mono (Words64.movImm64_ok (s := s₁) (d := t0) (tmp := t1) (by decide) (keyPlane x k))
    fun s₂ ⟨v₂, g₂, m₂, rd₂, wr₂, _⟩ => ?_
  obtain hkp : s₂.gpr kp = s.gpr kp := by rw [g₂ _ (by decide) (by decide), h.regs _ (by decide) (by decide)]
  refine Steps.wp_sd (a := wordAddr (s.gpr kp) k) (by omega_using [hk]) (by rw [hkp])
    (Spill.al8 hal (by omega_using [])) (by rw [wr₂, h.wr]; exact hw k hk) fun s₃ u₃ => WP.block_nil ?_
  obtain hm₃ : s₃.mem = s₁.mem.writeW (wordAddr (s.gpr kp) k) (keyPlane x k) := by rw [u₃.mem, m₂, v₂]
  refine ⟨fun j hj => ?_, ?_, fun r h0 h1 => by rw [u₃.gpr, g₂ r h0 h1, h.regs r h0 h1],
    by rw [u₃.rd, rd₂, h.rd], by rw [u₃.wr, wr₂, h.wr]⟩
  · rw [hm₃]
    by_cases hjk : j = k
    · subst hjk; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (slot_sep _ (by omega_using [hk, hj]) (by omega_using [hk]) hjk) (by decide)]
      exact h.planes j (by omega_using [hj, hjk])
  · rw [hm₃]
    exact h.frame.trans (frame_writeW _ (by rw [wordAddr]; exact VG.Offset.sub_base _ (by omega_using [hk])))

/-- `sigmaOne x`: the planes of `x` to the entry at `kp`, and `kp` to the next. -/
theorem sigmaOne_ok (x : BitVec 64) (s : State) (hal : (s.gpr kp).toNat % 8 = 0)
    (hw : ∀ j < 8, InRegions s.wr (s.gpr kp + BitVec.ofNat 64 (8 * j)) 8) :
    ∃ s', runBlock isa (sigmaOne x) s = some s' ∧
      (∀ j < 8, s'.mem.readW (s.gpr kp + BitVec.ofNat 64 (8 * j)) 64 = keyPlane x j) ∧
      s'.gpr kp = s.gpr kp + BitVec.ofNat 64 64 ∧ Frame [⟨s.gpr kp, 64⟩] s.mem s'.mem ∧
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, h₁⟩ := sigmaStores_ok x s hal hw
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := addKp_ok s₁ 64 (by decide)
  refine ⟨s₂, by rw [sigmaOne_eq, runBlock_append', e₁, Option.bind_some, e₂], fun j hj => by
      rw [m₂]; exact h₁.planes j hj,
    by rw [a₂, h₁.regs _ (by decide) (by decide)], by rw [m₂]; exact h₁.frame,
    fun r h0 h1 h2 => by rw [o₂ r h2, h₁.regs r h0 h1], by rw [rd₂, h₁.rd], by rw [wr₂, h₁.wr]⟩

theorem sigmaList_ok {b : Addr} (hfit : b.toNat + 8 * slots ≤ 2 ^ 64) (hal : b.toNat % 8 = 0) :
    ∀ (xs : List (BitVec 64)) (e : Nat) (s : State), (⟨b, 8 * slots⟩ : Region) ∈ s.wr →
      s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * e) → e + xs.length ≤ 34 →
      ∃ s', runBlock isa (xs.flatMap sigmaOne) s = some s' ∧
        (∀ i < xs.length, ∀ j < 8, entryW s'.mem b (e + i) j = keyPlane (xs.getD i 0) j) ∧
        Frame [⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * e), 64 * xs.length⟩] s.mem s'.mem ∧
        s'.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * (e + xs.length)) ∧
        (∀ r, r ≠ t0 → r ≠ t1 → r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], e, s, _, hr, _ => ⟨s, rfl, fun i hi => absurd hi (by simp), Frame.refl _ _, by simpa using hr,
      fun _ _ _ _ => rfl, rfl, rfl⟩
  | x :: xs, e, s, hscr, hr, hl => by
    rw [slots_eq] at hfit
    have hk := keySlot_eq
    simp only [List.length_cons] at hl
    obtain ⟨s₁, e₁, v₁, r₁, f₁, g₁, rd₁, wr₁⟩ := sigmaOne_ok x s (by rw [hr]; exact Spill.al8 hal (by omega_arith))
      (fun j hj => ⟨_, hscr, by
        rw [hr, Offset.add_add]
        exact VG.Offset.contains_base _ (by rw [slots_eq]; omega_arith) (by omega_arith)⟩)
    obtain ⟨s', e', v', f', r', g', rd', wr'⟩ := sigmaList_ok hfit hal xs (e + 1) s₁
      (by rw [wr₁]; exact hscr)
      (by rw [r₁, hr, Offset.add_add, show 8 * keySlot + 64 * e + 64 = 8 * keySlot + 64 * (e + 1) by omega_arith])
      (by omega_arith)
    refine ⟨s', by rw [List.flatMap_cons, runBlock_append', e₁, Option.bind_some, e'], fun i hi j hj => ?_,
      ?_, by rw [r', List.length_cons, show e + 1 + xs.length = e + (xs.length + 1) by omega_arith],
      fun r h0 h1 h2 => by rw [g' r h0 h1 h2, g₁ r h0 h1 h2], by rw [rd', rd₁], by rw [wr', wr₁]⟩
    · rcases i with _ | i
      · rw [entryW, Nat.add_zero, ← Offset.add_add, ← hr]
        refine (f'.readW (Region.contains_self _ _) (fun r hr' => ?_) (by decide)).trans (v₁ j hj)
        simp only [List.mem_singleton] at hr'; subst hr'
        rw [hr, Offset.add_add]
        exact VG.Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
      · rw [show e + (i + 1) = e + 1 + i by omega_arith]
        exact v' i (by simpa using hi) j hj
    · refine Frame.trans (f₁.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩)
        (f'.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩) <;>
        (simp only [List.mem_singleton] at hr'; subst hr')
      · rw [hr]; exact Region.sub_prefix (by simp only [List.length_cons]; omega_arith)
      · exact VG.Offset.sub b (by omega_arith) (by simp only [List.length_cons]; omega_arith)

/-- The table's entries `0 … 5` hold `Sigma1 … Sigma6`, as `KeyCtx` reads them. -/
theorem sigmas_rel {m : Mem} {b : Addr}
    (h : ∀ i < 6, ∀ j < 8, entryW m b i j = keyPlane (sigmas.getD i 0) j) :
    ∀ i < 6, HalfRel (entryW m b i) fun _ => sigE i := fun i hi bb hb c hc j hj => by
  rw [h i hi j hj]; exact sigma_planes _ hb hc hj

/-! ## Loading the key -/

/-- Eight bytes copied: the word they make, in the order ECB loads it. -/
theorem wordOf_copy {m m' : Mem} {a b : Addr} (h : ∀ i < 8, m' (b + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i)) :
    WordOf (m'.readW b 64) (Spec.Camellia.wordAt m a) := fun i hi j hj => by
  rw [Camellia.readW64_bit m' b hi hj, h i hi, Camellia.byteOf_wordAt m a hi]

/-- A step that writes only `t0` and `t1`. -/
structure Pure (s s' : State) : Prop where
  mem : s'.mem = s.mem
  regs : ∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- What a part of `loadKey` keeps: the slots but those of `KL` and `KR`,
the registers but `t0` and `t1`. -/
structure LkKeep (s s' : State) : Prop where
  keep : ∀ k < slots, (k < klSlot ∨ krSlot + 2 ≤ k) → slotW s' k = slotW s k
  regs : ∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r
  frame : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem LkKeep.trans {s₁ s₂ s₃ : State} (h₁ : LkKeep s₁ s₂) (h₂ : LkKeep s₂ s₃) : LkKeep s₁ s₃ where
  keep k hk h := (h₂.keep k hk h).trans (h₁.keep k hk h)
  regs r h0 h1 := (h₂.regs r h0 h1).trans (h₁.regs r h0 h1)
  frame := h₁.frame.trans (by have := h₂.frame; rw [h₁.regs _ (by decide) (by decide)] at this; exact this)
  rd := h₂.rd.trans h₁.rd
  wr := h₂.wr.trans h₁.wr

theorem LkKeep.of_pure {s s' : State} (h : Pure s s') : LkKeep s s' :=
  ⟨fun k _ _ => slotW_eq_of h.mem (h.regs _ (by decide) (by decide)) k, h.regs,
    by rw [h.mem]; exact Frame.refl _ _, h.rd, h.wr⟩

/-- `copyBytes t0 a0 sb soff (8 k) nb`, `nb = 8 n`: `n` words of the key to
slots `k … k + n - 1`. -/
theorem copyKey_ok {s : State} {len soff k n nb : Nat} (hnb : nb = 8 * n)
    (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hkey : (⟨s.gpr .a0, len⟩ : Region) ∈ s.rd)
    (hks : Region.Disjoint ⟨s.gpr .a0, len⟩ ⟨s.gpr sb, 8 * slots⟩) (hlen : len ≤ 32)
    (hsl : soff + 8 * n ≤ len) (hk2 : k + n ≤ keySlot) :
    ∃ s', runBlock isa (copyBytes t0 .a0 sb soff (8 * k) nb) s = some s' ∧
      (∀ w < n, WordOf (slotW s' (k + w))
        (Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 (soff + 8 * w)))) ∧
      (∀ j < slots, (j < k ∨ k + n ≤ j) → slotW s' j = slotW s j) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  subst hnb
  have hK := keySlot_eq
  have hS := slots_eq
  obtain ⟨s', e', c'⟩ := WP.runBlock_of (Bytes.copyBytes_ok (s := s) (tmp := t0) (src := .a0) (dst := sb)
    (soff := soff) (doff := 8 * k) (n := 8 * n) (by decide) (by decide) (by omega_arith) (by omega_arith)
    (fun i hi => ⟨_, List.mem_append_left _ hkey, VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun i hi => ⟨_, hscr, VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun i hi hc => hks _ (VG.Offset.contains_base _ (by omega_arith) (by omega_arith))
      ((VG.Offset.sub_base _ (by omega_arith)) _ hc)))
  obtain hb : s'.gpr sb = s.gpr sb := c'.gpr _ (by decide)
  refine ⟨s', e', fun w hw => ?_, fun j hj hjk => ?_, c'.gpr, ?_, c'.rd, c'.wr⟩
  · simp only [slotW, hb, wordAddr]
    refine wordOf_copy fun i hi => ?_
    have := c'.copied (8 * w + i) (by omega_arith)
    rw [Offset.add_add, Offset.add_add, show 8 * (k + w) + i = 8 * k + (8 * w + i) by omega_arith,
      show soff + 8 * w + i = soff + (8 * w + i) by omega_arith]
    exact this
  · simp only [slotW, hb]
    refine c'.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [wordAddr]
    exact VG.Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  · exact c'.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base _ (by omega_arith)⟩

/-- `KL` and `KR`, from the key's bytes. -/
abbrev klOf (m : Mem) (a : Addr) (len : Nat) : BitVec 128 := (Spec.Camellia.klkr (Spec.Camellia.bytesAt m a len)).1
abbrev krOf (m : Mem) (a : Addr) (len : Nat) : BitVec 128 := (Spec.Camellia.klkr (Spec.Camellia.bytesAt m a len)).2

theorem ofInt_neg_one : BitVec.ofInt 64 (-1) = BitVec.allOnes 64 := by decide

/-- What `loadKey` needs: the scratch buffer and the key, apart. -/
structure LkPre (s : State) (len : Nat) : Prop where
  al : (s.gpr sb).toNat % 8 = 0
  scr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr
  key : (⟨s.gpr .a0, len⟩ : Region) ∈ s.rd
  sep : Region.Disjoint ⟨s.gpr .a0, len⟩ ⟨s.gpr sb, 8 * slots⟩
  alen : s.gpr .a3 = BitVec.ofNat 64 len
  hl : len = 16 ∨ len = 24 ∨ len = 32

theorem LkPre.of_keep {s t : State} {len : Nat} (h : LkPre s len) (hk : LkKeep s t)
    (ha3 : t.gpr .a3 = s.gpr .a3) : LkPre t len where
  al := by rw [hk.regs _ (by decide) (by decide)]; exact h.al
  scr := by rw [hk.regs _ (by decide) (by decide), hk.wr]; exact h.scr
  key := by rw [hk.regs _ (by decide) (by decide), hk.rd]; exact h.key
  sep := by rw [hk.regs _ (by decide) (by decide), hk.regs _ (by decide) (by decide)]; exact h.sep
  alen := by rw [ha3]; exact h.alen
  hl := h.hl

/-- The key's words are those on entry, as long as only the scratch buffer changes. -/
theorem LkPre.word {s t : State} {len : Nat} (h : LkPre s len) (hk : LkKeep s t) {off : Nat}
    (hoff : off + 8 ≤ len) :
    Spec.Camellia.wordAt t.mem (t.gpr .a0 + BitVec.ofNat 64 off) =
      Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 off) := by
  rw [hk.regs _ (by decide) (by decide)]
  refine wordAt_frame hk.frame fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact h.sep.sub_left (VG.Offset.sub_base _ (by omega_arith))

/-- What each of `loadKey`'s branches leaves, from `u`: `KR`'s halves. -/
structure KrDone (s u u' : State) (len : Nat) : Prop where
  kr : WordsAt u' krSlot (hiW (krOf s.mem (s.gpr .a0) len), loW (krOf s.mem (s.gpr .a0) len))
  keep : LkKeep u u'
  low : ∀ k < slots, k < krSlot → slotW u' k = slotW u k

/-- A key of 16 bytes: `KR = 0`. -/
theorem kr16_ok {s u : State} {len : Nat} (hp : LkPre u len) (h16 : len = 16) :
    ∃ u', runBlock isa [.li t0 0, stS krSlot t0, stS (krSlot + 1) t0] u = some u' ∧ KrDone s u u' len := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  obtain ⟨-, -, hK2, hK3⟩ := Proof.Camellia.klkr_halves s.mem (s.gpr .a0) (Or.inl h16)
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := liN_ok u t0 0 (by decide)
  obtain lk₃ : LkKeep u s₃ := LkKeep.of_pure ⟨m₃, fun r h0 _ => o₃ r h0, rd₃, wr₃⟩
  obtain hp₃ := hp.of_keep lk₃ (o₃ _ (by decide))
  obtain ⟨s₄, e₄, v₄, k₄, g₄, f₄, rd₄, wr₄⟩ := st_ok (k := krSlot) t0 hp₃.al hp₃.scr (by omega_arith)
  obtain ⟨s₅, e₅, v₅, k₅, g₅, f₅, rd₅, wr₅⟩ := st_ok (k := krSlot + 1) t0
    (by rw [g₄]; exact hp₃.al) (by rw [g₄, wr₄]; exact hp₃.scr) (by omega_arith)
  refine ⟨s₅, by
    rw [show ([.li t0 0, stS krSlot t0, stS (krSlot + 1) t0] : List Instr) =
        [.li t0 0] ++ ([stS krSlot t0] ++ [stS (krSlot + 1) t0]) from rfl,
      runBlock_append', e₃, Option.bind_some, runBlock_append', e₄, Option.bind_some, e₅],
    ⟨?_, ?_⟩, ?_, fun k hk h => ?_⟩
  · rw [k₅ _ (by omega_arith) (by omega_arith), v₄, a₃, hK2, ite_eq_left h16]; exact WordOf.zero
  · rw [v₅, g₄, a₃, hK3, ite_eq_left h16]; exact WordOf.zero
  · refine lk₃.trans ⟨fun k hk h => by rw [k₅ k hk (by omega_arith), k₄ k hk (by omega_arith)],
      fun r _ _ => by rw [g₅, g₄], ?_, by rw [rd₅, rd₄], by rw [wr₅, wr₄]⟩
    exact f₄.trans (by rw [g₄] at f₅; exact f₅)
  · rw [k₅ k hk (by omega_arith), k₄ k hk (by omega_arith)]
    exact slotW_eq_of m₃ (o₃ _ (by decide)) k

/-- A key of 24 bytes: `KR`'s low half is the complement of its high half. -/
theorem kr24_ok {s u : State} {len : Nat} (hs : LkPre s len) (hp : LkPre u len)
    (h24 : len = 24) (hw : WordOf (slotW u krSlot) (Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 16))) :
    ∃ u', runBlock isa [ldS t0 krSlot, notR t0, stS (krSlot + 1) t0] u = some u' ∧ KrDone s u u' len := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  obtain ⟨-, -, hK2, hK3⟩ := Proof.Camellia.klkr_halves s.mem (s.gpr .a0) hs.hl
  obtain ⟨s₅, e₅, a₅, o₅, m₅, rd₅, wr₅⟩ := ldS_ok (k := krSlot) t0 rfl hp.al hp.scr (by omega_arith)
  let s₆ := s₅.write t0 (s₅.gpr t0 ^^^ BitVec.ofInt 64 (-1))
  obtain e₆ : runBlock isa [notR t0] s₅ = some s₆ := by
    simp only [notR, runBlock_cons, exec_logicImm (show imm12 (-1 : Int) by decide), runStep_some,
      runBlock_nil]
    rfl
  obtain a₆ : s₆.gpr t0 = ~~~ slotW u krSlot := by
    rw [RegUpd.gpr_write_self, a₅, ofInt_neg_one, BitVec.xor_allOnes]
  obtain o₆ : ∀ r, r ≠ t0 → s₆.gpr r = u.gpr r := fun r hr => by
    rw [RegUpd.gpr_write_of_ne _ _ hr, o₅ r hr]
  obtain lk₆ : LkKeep u s₆ := LkKeep.of_pure ⟨m₅, fun r h0 _ => o₆ r h0, rd₅, wr₅⟩
  obtain hp₆ := hp.of_keep lk₆ (o₆ _ (by decide))
  obtain ⟨s₇, e₇, v₇, k₇, g₇, f₇, rd₇, wr₇⟩ := st_ok (k := krSlot + 1) t0 hp₆.al hp₆.scr (by omega_arith)
  obtain hs₆ : ∀ k, slotW s₆ k = slotW u k := slotW_eq_of m₅ (o₆ _ (by decide))
  refine ⟨s₇, by
    rw [show ([ldS t0 krSlot, notR t0, stS (krSlot + 1) t0] : List Instr) =
        [ldS t0 krSlot] ++ ([notR t0] ++ [stS (krSlot + 1) t0]) from rfl,
      runBlock_append', e₅, Option.bind_some, runBlock_append', e₆, Option.bind_some, e₇],
    ⟨?_, ?_⟩, lk₆.trans ⟨fun k hk h => k₇ k hk (by omega_arith), fun r _ _ => by rw [g₇], f₇, rd₇, wr₇⟩,
    fun k hk h => ?_⟩
  · rw [k₇ _ (by omega_arith) (by omega_arith), hs₆, hK2, ite_eq_right (by omega_arith)]; exact hw
  · rw [v₇, a₆, hK3, ite_eq_right (by omega_arith), ite_eq_left h24]; exact hw.not
  · rw [k₇ k hk (by omega_arith), hs₆]

/-- A key of 32 bytes: `KR`'s low half is the key's fourth word. -/
theorem kr32_ok {s u : State} {len : Nat} (hs : LkPre s len) (hk : LkKeep s u) (hp : LkPre u len)
    (h16 : len ≠ 16) (h24 : len ≠ 24)
    (hw : WordOf (slotW u krSlot) (Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 16))) :
    ∃ u', runBlock isa (copyBytes t0 .a0 sb 24 (8 * (krSlot + 1)) 8) u = some u' ∧ KrDone s u u' len := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  obtain ⟨-, -, hK2, hK3⟩ := Proof.Camellia.klkr_halves s.mem (s.gpr .a0) hs.hl
  obtain h32 : len = 32 := by rcases hs.hl with h | h | h <;> omega_arith
  obtain ⟨s₅, e₅, w₅, k₅, g₅, f₅, rd₅, wr₅⟩ := copyKey_ok (s := u) (soff := 24) (k := krSlot + 1) (n := 1)
    (nb := 8) rfl hp.scr hp.key hp.sep (by omega_arith) (by omega_arith) (by omega_arith)
  obtain lk₅ : LkKeep u s₅ := ⟨fun k hk h => k₅ k hk (by omega_arith), fun r h0 _ => g₅ r h0, f₅, rd₅, wr₅⟩
  refine ⟨s₅, e₅, ⟨?_, ?_⟩, lk₅, fun k hk h => k₅ k hk (by omega_arith)⟩
  · rw [k₅ _ (by omega_arith) (by omega_arith), hK2, ite_eq_right h16]; exact hw
  · have := w₅ 0 (by decide)
    rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero, hs.word hk (by omega_arith)] at this
    rw [hK3, ite_eq_right h16, ite_eq_right h24]; exact this

/-- The first block of `loadKey`: `KL`, and `t1 := len - 16`. -/
theorem klBlock_ok {s : State} {len : Nat} (hs : LkPre s len) :
    ∃ s', runBlock isa (copyBytes t0 .a0 sb 0 (8 * klSlot) 16 ++ ([.addi t1 .a3 (-16)] : List Instr)) s =
        some s' ∧ LkKeep s s' ∧ s'.gpr .a3 = s.gpr .a3 ∧
      WordsAt s' klSlot (hiW (klOf s.mem (s.gpr .a0) len), loW (klOf s.mem (s.gpr .a0) len)) ∧
      (s'.gpr t1 == 0) = decide (len = 16) := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  obtain ⟨hK0, hK1, -, -⟩ := Proof.Camellia.klkr_halves s.mem (s.gpr .a0) hs.hl
  obtain hl32 : len ≤ 32 := by rcases hs.hl with h | h | h <;> omega_arith
  obtain hz : s.gpr .a0 + BitVec.ofNat 64 (0 + 8 * 0) = s.gpr .a0 := by simp
  obtain ⟨s₁, e₁, w₁, k₁, g₁, f₁, rd₁, wr₁⟩ := copyKey_ok (soff := 0) (k := klSlot) (n := 2) (nb := 16) rfl
    hs.scr hs.key hs.sep hl32 (by rcases hs.hl with h | h | h <;> omega_arith) (by omega_arith)
  obtain ⟨s₂, e₂, z₂, o₂, m₂, rd₂, wr₂⟩ := subI_ok s₁ t1 .a3 16 (by decide)
  obtain hs₂ : ∀ k, slotW s₂ k = slotW s₁ k := slotW_eq_of m₂ (o₂ _ (by decide))
  refine ⟨s₂, by rw [runBlock_append', e₁, Option.bind_some]; exact e₂,
    ⟨fun k hk h => by rw [hs₂, k₁ k hk (by omega_arith)], fun r h0 h1 => by rw [o₂ r h1, g₁ r h0],
      by rw [m₂]; exact f₁, by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩,
    by rw [o₂ _ (by decide), g₁ _ (by decide)], ⟨?_, ?_⟩, ?_⟩
  · rw [hs₂, hK0, ← hz]; exact w₁ 0 (by decide)
  · rw [hs₂, hK1]; exact w₁ 1 (by decide)
  · rw [z₂, g₁ _ (by decide), hs.alen, VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]

/-- The block of `loadKey` for keys of 24 or 32 bytes: `KR`'s high half, and `t1 := len - 24`. -/
theorem krBlock_ok {s u : State} {len : Nat} (hs : LkPre s len) (hk : LkKeep s u) (hp : LkPre u len)
    (h16 : len ≠ 16) :
    ∃ u', runBlock isa (copyBytes t0 .a0 sb 16 (8 * krSlot) 8 ++ ([.addi t1 .a3 (-24)] : List Instr)) u =
        some u' ∧ LkKeep u u' ∧ u'.gpr .a3 = u.gpr .a3 ∧ (∀ k < slots, k < krSlot → slotW u' k = slotW u k) ∧
      WordOf (slotW u' krSlot) (Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 16)) ∧
      (u'.gpr t1 == 0) = decide (len = 24) := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  obtain hl32 : len ≤ 32 := by rcases hs.hl with h | h | h <;> omega_arith
  obtain hl24 : 24 ≤ len := by rcases hs.hl with h | h | h <;> omega_arith
  obtain ⟨s₃, e₃, w₃, k₃, g₃, f₃, rd₃, wr₃⟩ := copyKey_ok (s := u) (soff := 16) (k := krSlot) (n := 1) (nb := 8)
    rfl hp.scr hp.key hp.sep hl32 (by omega_arith) (by omega_arith)
  obtain ⟨s₄, e₄, z₄, o₄, m₄, rd₄, wr₄⟩ := subI_ok s₃ t1 .a3 24 (by decide)
  obtain hs₄ : ∀ k, slotW s₄ k = slotW s₃ k := slotW_eq_of m₄ (o₄ _ (by decide))
  refine ⟨s₄, by rw [runBlock_append', e₃, Option.bind_some]; exact e₄,
    ⟨fun k hk h => by rw [hs₄, k₃ k hk (by omega_arith)], fun r h0 h1 => by rw [o₄ r h1, g₃ r h0],
      by rw [m₄]; exact f₃, by rw [rd₄, rd₃], by rw [wr₄, wr₃]⟩,
    by rw [o₄ _ (by decide), g₃ _ (by decide)], fun k hk h => by rw [hs₄, k₃ k hk (Or.inl h)], ?_, ?_⟩
  · have := w₃ 0 (by decide)
    rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero, hs.word hk (by omega_arith)] at this
    rw [hs₄]; exact this
  · rw [z₄, g₃ _ (by decide), hp.alen, VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]

/-- `loadKey`'s postcondition, from `KL`'s block and `KR`'s branch. -/
theorem lkPost_of {s s₂ s' : State} {len : Nat}
    (hkl : WordsAt s₂ klSlot (hiW (klOf s.mem (s.gpr .a0) len), loW (klOf s.mem (s.gpr .a0) len)))
    (lk₂ : LkKeep s s₂) (h : KrDone s s₂ s' len) :
    WordsAt s' klSlot (hiW (klOf s.mem (s.gpr .a0) len), loW (klOf s.mem (s.gpr .a0) len)) ∧
      WordsAt s' krSlot (hiW (krOf s.mem (s.gpr .a0) len), loW (krOf s.mem (s.gpr .a0) len)) ∧
      LkKeep s s' := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  exact ⟨hkl.congr (h.low _ (by omega_arith) (by omega_arith)) (h.low _ (by omega_arith) (by omega_arith)),
    h.kr, lk₂.trans h.keep⟩

/-- `KrDone` from the state before the block of `KR`'s high half. -/
theorem krDone_trans {s s₂ s₄ s' : State} {len : Nat} (lk₄ : LkKeep s₂ s₄)
    (lo₄ : ∀ k < slots, k < krSlot → slotW s₄ k = slotW s₂ k) (h : KrDone s s₄ s' len) : KrDone s s₂ s' len :=
  ⟨h.kr, lk₄.trans h.keep, fun k hk h' => by rw [h.low k hk h', lo₄ k hk h']⟩

/-- `loadKey`: `KL`'s and `KR`'s halves, as words, in their slots. -/
theorem loadKey_wp {s : State} {len : Nat} (hs : LkPre s len) :
    WP isa loadKey s fun s' =>
      WordsAt s' klSlot (hiW (klOf s.mem (s.gpr .a0) len), loW (klOf s.mem (s.gpr .a0) len)) ∧
      WordsAt s' krSlot (hiW (krOf s.mem (s.gpr .a0) len), loW (krOf s.mem (s.gpr .a0) len)) ∧
      LkKeep s s' := by
  obtain ⟨hl₁, hr₁, -, -, -, -, hK, hS⟩ := kaKb_slots
  obtain ⟨s₂, e₂, lk₂, a3₂, hkl, hz₂⟩ := klBlock_ok hs
  obtain hp₂ := hs.of_keep lk₂ a3₂
  unfold loadKey
  refine WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)
  refine WP.mono (Q := fun s' => KrDone s s₂ s' len)
    (WP.ite (decide (len = 16)) ((eval_zero s₂ t1).trans (by rw [hz₂])) (fun h16 => ?_) (fun h16 => ?_))
    fun s' h => lkPost_of hkl lk₂ h
  · obtain ⟨u', e', h'⟩ := kr16_ok (s := s) hp₂ (by simpa using h16)
    exact WP.of_runBlock ⟨u', e', h'⟩
  · have h16 : len ≠ 16 := by simpa using h16
    obtain ⟨s₄, e₄, lk₄, a3₄, lo₄, w₄, hz₄⟩ := krBlock_ok hs lk₂ hp₂ h16
    obtain lk₂₄ := lk₂.trans lk₄
    obtain hp₄ := hs.of_keep lk₂₄ (a3₄.trans a3₂)
    refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
    refine WP.mono (Q := fun s' => KrDone s s₄ s' len)
      (WP.ite (decide (len = 24)) ((eval_zero s₄ t1).trans (by rw [hz₄])) (fun h24 => ?_) (fun h24 => ?_))
      fun s' h => krDone_trans lk₄ lo₄ h
    · obtain ⟨u', e', h'⟩ := kr24_ok hs hp₄ (by simpa using h24) w₄
      exact WP.of_runBlock ⟨u', e', h'⟩
    · obtain ⟨u', e', h'⟩ := kr32_ok hs lk₂₄ hp₄ h16 (by simpa using h24) w₄
      exact WP.of_runBlock ⟨u', e', h'⟩


/-! ## Loading the values -/

def lvChunk (v k : Nat) : List Instr :=
  loadBE64 (hiReg v) t0 sb (8 * k) ++ loadBE64 (loReg v) t0 sb (8 * (k + 1))

theorem loadValues_eq :
    loadValues = lvChunk 0 klSlot ++ (lvChunk 1 krSlot ++ (lvChunk 2 kaSlot ++ lvChunk 3 kbSlot)) := by
  rfl

theorem regs_lt4 {v : Nat} (hv : v < 4) : hiReg v ≠ sb ∧ loReg v ≠ sb ∧ hiReg v ≠ loReg v ∧
    hiReg v ≠ t0 ∧ loReg v ≠ t0 := by
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> decide

/-- `loadBE64 t t0 sb (8 k)`: slot `k`, read big-endian. -/
theorem ldBE_ok {s : State} {k : Nat} (t : Reg) (ht : t ≠ sb) (ht0 : t ≠ t0)
    (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr) (hk : k < keySlot) {H : BitVec 64}
    (hw : WordOf (slotW s k) H) :
    ∃ s', runBlock isa (loadBE64 t t0 sb (8 * k)) s = some s' ∧ s'.gpr t = H ∧
      (∀ r, r ≠ t → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hk' : k < slots := by rw [keySlot_eq] at hk; rw [slots_eq]; omega_arith
  obtain ⟨r, hr, hc⟩ := scr_in hscr hk'
  obtain ⟨s', e', h'⟩ := WP.runBlock_of (ByteLoad.loadBE64_ok (s := s) (d := t) (tmp := t0) (n := sb)
    (off := 8 * k) ht (by decide) ht0 (by rw [keySlot_eq] at hk; omega_arith) ⟨r, List.mem_append_right _ hr, hc⟩)
  subst h'
  refine ⟨_, e', ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · rw [RegUpd.gpr_write_self]; exact be64_of_wordOf hw
  · rw [RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]

theorem lvChunk_ok {s : State} {v k : Nat} (hv : v < 4) (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hk : k + 1 < keySlot) {H L : BitVec 64} (hw : WordsAt s k (H, L)) :
    ∃ s', runBlock isa (lvChunk v k) s = some s' ∧ s'.gpr (hiReg v) = H ∧ s'.gpr (loReg v) = L ∧
      (∀ r, r ≠ hiReg v → r ≠ loReg v → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := regs_lt4 hv
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := ldBE_ok (k := k) (hiReg v) n1 n4 hscr (by omega_arith) hw.1
  obtain hb₂ : s₂.gpr sb = s.gpr sb := o₂ _ n1.symm (by decide)
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := ldBE_ok (s := s₂) (k := k + 1) (loReg v) n2 n5
    (by rw [hb₂, wr₂]; exact hscr) hk (by rw [slotW_eq_of m₂ hb₂]; exact hw.2)
  refine ⟨s₄, by rw [lvChunk, runBlock_append', e₂, Option.bind_some, e₄], ?_, a₄,
    fun r h1 h2 h3 => by rw [o₄ r h2 h3, o₂ r h1 h3], by rw [m₄, m₂], by rw [rd₄, rd₂], by rw [wr₄, wr₂]⟩
  rw [o₄ _ n3 n4, a₂]

/-- `loadValues`: the four values' halves, read big-endian into `hiReg v` and `loReg v`. -/
theorem loadValues_ok {s : State} (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr) (vs : List (BitVec 128))
    (hw : ∀ v < 4, WordsAt s ([klSlot, krSlot, kaSlot, kbSlot].getD v 0) (hiW (vs.getD v 0), loW (vs.getD v 0))) :
    ∃ s', runBlock isa loadValues s = some s' ∧
      (∀ v < 4, s'.gpr (hiReg v) = hiW (vs.getD v 0) ∧ s'.gpr (loReg v) = loW (vs.getD v 0)) ∧
      (∀ r, (∀ v < 4, r ≠ hiReg v ∧ r ≠ loReg v) → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hl, hr, hW, hA, hB, -, hK, hS⟩ := kaKb_slots
  obtain ⟨s₁, e₁, h₁, l₁, o₁, m₁, rd₁, wr₁⟩ := lvChunk_ok (v := 0) (k := klSlot) (by decide) hscr (by omega_arith)
    (hw 0 (by decide))
  obtain hb₁ : s₁.gpr sb = s.gpr sb := o₁ _ (by decide) (by decide) (by decide)
  obtain hs₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of m₁ hb₁
  obtain ⟨s₂, e₂, h₂, l₂, o₂, m₂, rd₂, wr₂⟩ := lvChunk_ok (v := 1) (k := krSlot) (by decide)
    (by rw [hb₁, wr₁]; exact hscr) (by omega_arith) ((hw 1 (by decide)).congr (hs₁ _) (hs₁ _))
  obtain hb₂ : s₂.gpr sb = s.gpr sb := by rw [o₂ _ (by decide) (by decide) (by decide), hb₁]
  obtain hs₂ : ∀ k, slotW s₂ k = slotW s k := fun k => by rw [slotW_eq_of m₂ (by rw [hb₂, hb₁]), hs₁]
  obtain ⟨s₃, e₃, h₃, l₃, o₃, m₃, rd₃, wr₃⟩ := lvChunk_ok (v := 2) (k := kaSlot) (by decide)
    (by rw [hb₂, wr₂, wr₁]; exact hscr) (by omega_arith) ((hw 2 (by decide)).congr (hs₂ _) (hs₂ _))
  obtain hb₃ : s₃.gpr sb = s.gpr sb := by rw [o₃ _ (by decide) (by decide) (by decide), hb₂]
  obtain hs₃ : ∀ k, slotW s₃ k = slotW s k := fun k => by rw [slotW_eq_of m₃ (by rw [hb₃, hb₂]), hs₂]
  obtain ⟨s₄, e₄, h₄, l₄, o₄, m₄, rd₄, wr₄⟩ := lvChunk_ok (v := 3) (k := kbSlot) (by decide)
    (by rw [hb₃, wr₃, wr₂, wr₁]; exact hscr) (by omega_arith) ((hw 3 (by decide)).congr (hs₃ _) (hs₃ _))
  refine ⟨s₄, by rw [loadValues_eq, runBlock_append', e₁, Option.bind_some, runBlock_append', e₂,
      Option.bind_some, runBlock_append', e₃, Option.bind_some, e₄], fun v hv => ?_,
    fun r hr h0 => by
      obtain ⟨a0, b0⟩ := hr 0 (by decide); obtain ⟨a1, b1⟩ := hr 1 (by decide)
      obtain ⟨a2, b2⟩ := hr 2 (by decide); obtain ⟨a3, b3⟩ := hr 3 (by decide)
      rw [o₄ r a3 b3 h0, o₃ r a2 b2 h0, o₂ r a1 b1 h0, o₁ r a0 b0 h0],
    by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_arith) with rfl | rfl | rfl | rfl
  · exact ⟨by rw [o₄ _ (by decide) (by decide) (by decide), o₃ _ (by decide) (by decide) (by decide),
        o₂ _ (by decide) (by decide) (by decide), h₁],
      by rw [o₄ _ (by decide) (by decide) (by decide), o₃ _ (by decide) (by decide) (by decide),
        o₂ _ (by decide) (by decide) (by decide), l₁]⟩
  · exact ⟨by rw [o₄ _ (by decide) (by decide) (by decide), o₃ _ (by decide) (by decide) (by decide), h₂],
      by rw [o₄ _ (by decide) (by decide) (by decide), o₃ _ (by decide) (by decide) (by decide), l₂]⟩
  · exact ⟨by rw [o₄ _ (by decide) (by decide) (by decide), h₃],
      by rw [o₄ _ (by decide) (by decide) (by decide), l₃]⟩
  · exact ⟨h₄, l₄⟩

/-! ## The prologue -/

theorem sreg_ne' (i : Nat) (hi : i < 12) : sreg i ≠ sb ∧ sreg i ≠ .a3 := by
  revert i; decide

theorem ekPrologue_ok {s₀ : State} {b : Addr} (hb : s₀.gpr .a3 = b) (hw : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr)
    (hfit : b.toNat + 8 * slots ≤ 2 ^ 64) (hal : b.toNat % 8 = 0) :
    ∃ s, runBlock isa ([movR sb .a3, movR .a3 .a1] ++ saveRegs ++ setSlots allMasks ++ tableSetup ++
        sigmas.flatMap sigmaOne) s₀ = some s ∧
      s.gpr sb = b ∧ s.gpr .a3 = s₀.gpr .a1 ∧
      (∀ r, r ≠ sb → r ≠ .a3 → r ≠ t0 → r ≠ t1 → r ≠ kp → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ MasksOk s ∧
      (∀ i < 6, ∀ j < 8, entryW s.mem b i j = keyPlane (sigmas.getD i 0) j) ∧
      Frame [⟨b, 8 * slots⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have hk := keySlot_eq
  have hsv := savedSlot_eq
  have hS := slots_eq
  obtain ⟨s₁a, e₁a, r₁a, o₁a, m₁a, rd₁a, wr₁a⟩ := movR_ok s₀ sb .a3
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₁a .a3 .a1
  obtain hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), r₁a, hb]
  obtain g₁ : ∀ r, r ≠ sb → r ≠ .a3 → s₁.gpr r = s₀.gpr r := fun r h1 h2 => by rw [o₁ r h2, o₁a r h1]
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂, -⟩ := save_ok (b := b) (by rw [wr₁, wr₁a]; exact hw) hb₁ hal
  obtain ⟨s₃, e₃, v₃, g₃, rd₃, wr₃, f₃⟩ := setSlots_ok (b := b) (by rw [wr₂, wr₁, wr₁a]; exact hw)
    (by rw [g₂, hb₁]) hal
  obtain hb₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide) (by decide), g₂, hb₁]
  obtain ⟨s₄, e₄, k₄, o₄, m₄, rd₄, wr₄⟩ := setKp_ok s₃
  obtain hb₄ : s₄.gpr sb = b := by rw [o₄ _ (by decide), hb₃]
  obtain ⟨s₅, e₅, v₅, f₅, r₅, g₅, rd₅, wr₅⟩ := sigmaList_ok hfit hal sigmas 0 s₄
    (by rw [wr₄, wr₃, wr₂, wr₁, wr₁a]; exact hw)
    (by rw [k₄, hb₃]; simp) (by decide)
  obtain hb₅ : s₅.gpr sb = b := by rw [g₅ _ (by decide) (by decide) (by decide), hb₄]
  -- The slots outside the table keep their values.
  obtain hs₅ : ∀ k, k < keySlot ∨ keySlot + 48 ≤ k → k < slots → slotW s₅ k = slotW s₃ k := fun k h1 h2 => by
    simp only [slotW, hb₅, hb₃]
    rw [← m₄]
    refine f₅.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    simp only [wordAddr, Nat.mul_zero, Nat.add_zero, sigmas, List.length_cons, List.length_nil]
    exact VG.Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
  refine ⟨s₅, ?_, hb₅, ?_, fun r h1 h2 h3 h4 h5 => ?_, fun i hi => ?_, fun kv hkv => ?_,
    fun i hi j hj => ?_, ?_, by rw [rd₅, rd₄, rd₃, rd₂, rd₁, rd₁a],
    by rw [wr₅, wr₄, wr₃, wr₂, wr₁, wr₁a]⟩
  · rw [runBlock_append', runBlock_append', runBlock_append', runBlock_append',
      show ([movR sb .a3, movR .a3 .a1] : List Instr) = [movR sb .a3] ++ [movR .a3 .a1] from rfl,
      runBlock_append', e₁a, Option.bind_some, e₁, Option.bind_some, e₂, Option.bind_some,
      e₃, Option.bind_some, e₄, Option.bind_some, e₅]
  · rw [g₅ _ (by decide) (by decide) (by decide), o₄ _ (by decide), g₃ _ (by decide) (by decide), g₂, r₁,
      o₁a _ (by decide)]
  · rw [g₅ r h3 h4 h5, o₄ r h5, g₃ r h3 h4, g₂, g₁ r h1 h2]
  · have n := sreg_ne' i hi
    have := sv₂ i hi
    rw [show s₁.gpr (sreg i) = s₀.gpr (sreg i) from g₁ _ n.1 n.2] at this
    rw [← this]
    obtain h' := hs₅ (savedSlot + i) (Or.inl (by omega_arith)) (by omega_arith)
    simp only [slotW, hb₅, hb₃] at h'
    rw [h']
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by omega_arith) (by omega_arith)
  · have := mask_lt hkv
    rw [hs₅ _ (Or.inl (by omega_arith)) (by omega_arith)]
    exact v₃ kv hkv
  · have := v₅ i (by simpa [sigmas] using hi) j hj
    rw [Nat.zero_add] at this
    exact this
  · have sub : ∀ {r : Region}, Region.Sub r ⟨b, 8 * slots⟩ → ∀ r' ∈ [r], ∃ r'' ∈ [(⟨b, 8 * slots⟩ : Region)],
        Region.Sub r' r'' := fun hs r' hr' => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr'; subst hr'; exact hs⟩
    obtain f₂' : Frame [⟨b, 8 * slots⟩] s₁.mem s₂.mem :=
      f₂.sub (sub (VG.Offset.sub_base b (by omega_arith)))
    obtain f₃' : Frame [⟨b, 8 * slots⟩] s₂.mem s₃.mem := f₃.sub (sub (Region.sub_prefix (by omega_arith)))
    obtain f₅' : Frame [⟨b, 8 * slots⟩] s₄.mem s₅.mem := f₅.sub (sub (by
      simp only [Nat.mul_zero, Nat.add_zero, sigmas, List.length_cons, List.length_nil]
      exact VG.Offset.sub_base b (by omega_arith)))
    rw [m₁, m₁a] at f₂'
    rw [m₄] at f₅'
    exact f₂'.trans (f₃'.trans f₅')

end VG.Proof.Camellia.RISCV64

end

end


/-!
# The Camellia key schedule on RISCV64: the whole function

As on PPC64LE (`Proof/Camellia/PPC64LE/ExpandKey.lean`). `expandKey_wp`:
`expandKey` meets `expandKeyRISCV64`. After the prologue
(`ekPrologue_ok`), `loadKey_wp` and `kaKb_wp` leave `KL`, `KR`, `KA` and
`KB` in their slots; `loadValues_ok` reads them big-endian into registers, and
`storeSubkeys_ok` stores the subkeys, which are the specification's
(`scheduleWords_expandKey`, `schedule_of_stores`).
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG.Impl.Camellia (bytePos keyPlane sigmas)
open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Camellia.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 u7 kp movR ldS stS)
open VG.Proof.Camellia (hiW loW)

theorem entryW_slot (s : State) (i j : Nat) : entryW s.mem (s.gpr sb) i j = slotW s (keySlot + 8 * i + j) := by
  simp only [entryW, slotW, wordAddr]
  rw [show 8 * (keySlot + 8 * i + j) = 8 * keySlot + 64 * i + 8 * j by omega_using []]

/-- What the subkeys' stores leave: the schedule's bytes. -/
structure StoresPost (s₈ : State) (S : Addr) (len : Nat) (key : List Byte) (s : State) : Prop where
  bytes : Spec.Camellia.bytesAt s.mem S (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len)) =
    Spec.Camellia.scheduleBytes (Spec.Camellia.expandKey key)
  frame : Frame [⟨S, 272⟩] s₈.mem s.mem
  regs : ∀ r, r ≠ t0 → r ≠ t1 → s.gpr r = s₈.gpr r
  rd : s.rd = s₈.rd
  wr : s.wr = s₈.wr

/-- The stores of one key length's subkeys. -/
theorem stores_wp {s₈ : State} {S : Addr} {len : Nat} {key : List Byte} {ks : List (Nat × Nat × Bool)}
    (hS : s₈.gpr .a2 = S) (hw : (⟨S, 272⟩ : Region) ∈ s₈.wr) (hv : ∀ k ∈ ks, k.1 < 4)
    (hks : ks.length ≤ 34)
    (hg : ∀ v < 4, s₈.gpr (hiReg v) = hiW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0) ∧
      s₈.gpr (loReg v) = loW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0))
    (hlen : 8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len) = 8 * ks.length)
    (hks' : ks = if key.length = 16 then Impl.Camellia.subkeys128 else Impl.Camellia.subkeys256) :
    WP isa (.block (storeSubkeys ks)) s₈ (StoresPost s₈ S len key) := by
  obtain ⟨s₉, e₉, b₉, f₉, g₉, rd₉, wr₉⟩ := storeSubkeys_ok ks hv 0 s₈ (fun i hi => ⟨_, hw, by
    rw [hS]; exact VG.Offset.contains_base _ (by omega_using [hks, hi]) (by omega_using [hks, hi])⟩) (by omega_using [hks])
  refine WP.of_runBlock ⟨s₉, e₉, ⟨?_, ?_, g₉, rd₉, wr₉⟩⟩
  · rw [hlen, schedule_of_stores (H := fun v => s₈.gpr (hiReg v)) (L := fun v => s₈.gpr (loReg v)) hv hg (by rw [← hS]; exact b₉), Spec.Camellia.scheduleBytes,
      Proof.Camellia.scheduleWords_expandKey, ← hks']
  · rw [hS] at f₉
    exact f₉.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base S (by omega_using [hks])⟩

theorem expandKey_wp {s₀ : State} (hp : expandKeyRISCV64.pre s₀) :
    WP isa expandKey s₀ fun s' => (∀ i < 12, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      expandKeyRISCV64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB, hlen, hal⟩ := hp
  obtain ⟨hl', hr', hW, hA, hB, hE, hK, hS⟩ := kaKb_slots
  have ht := tailSlot_eq
  have hsv := savedSlot_eq
  obtain hwB : (⟨s₀.gpr .a3, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  obtain hwS : (⟨s₀.gpr .a2, 272⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  obtain hrK : (⟨s₀.gpr .a0, (s₀.gpr .a1).toNat⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  unfold expandKey
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, r6₁, g₁, sv₁, mk₁, ent₁, f₁, rd₁, wr₁⟩ := ekPrologue_ok (b := s₀.gpr .a3) rfl hwB fitB hal
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  obtain r3₁ : s₁.gpr .a0 = s₀.gpr .a0 := g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain r5₁ : s₁.gpr .a2 = s₀.gpr .a2 := g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  -- The key, unchanged so far.
  obtain hkey₁ : Spec.Camellia.bytesAt s₁.mem (s₁.gpr .a0) (s₀.gpr .a1).toNat =
      Spec.Camellia.bytesAt s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat := by
    rw [r3₁]
    refine Proof.Camellia.bytesAt_congr fun i hi => f₁.bytes (R := ⟨s₀.gpr .a0, (s₀.gpr .a1).toNat⟩)
      (fun r hr => ?_) (by simp only; omega_using []) hi
    simp only [List.mem_singleton] at hr; subst hr
    exact dKB.sub_right (Region.sub_prefix (by omega_using []))
  -- `KL` and `KR`.
  refine WP.seq (WP.mono (loadKey_wp (len := (s₀.gpr .a1).toNat) (s := s₁)
    ⟨by rw [b₁]; exact hal, by rw [b₁, wr₁]; exact hwB, by rw [r3₁, rd₁]; exact hrK, by rw [r3₁, b₁]; exact dKB,
      by rw [r6₁, BitVec.ofNat_toNat, BitVec.setWidth_eq], hlen⟩) fun s₂ h₂ => ?_)
  obtain ⟨kl₂, kr₂, ⟨sl₂, g₂, f₂, rd₂, wr₂⟩⟩ := h₂
  simp only [klOf, krOf] at kl₂ kr₂
  rw [hkey₁] at kl₂ kr₂
  -- Abbreviations.
  generalize hkey : Spec.Camellia.bytesAt s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat = key at kl₂ kr₂
  obtain hb₂ : s₂.gpr sb = s₀.gpr .a3 := by rw [g₂ _ (by decide) (by decide), b₁]
  -- `kp` at the table.
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := setKp_ok s₂
  refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
  have hg₄ : ∀ r, r ≠ kp → s₄.gpr r = s₂.gpr r := o₄
  obtain hb₄ : s₄.gpr sb = s₀.gpr .a3 := by rw [hg₄ _ (by decide), hb₂]
  obtain hs₄ : ∀ k, slotW s₄ k = slotW s₂ k := slotW_eq_of m₄ (hg₄ _ (by decide))
  obtain r5₄ : s₄.gpr .a2 = s₀.gpr .a2 := by
    rw [hg₄ _ (by decide), g₂ _ (by decide) (by decide), r5₁]
  obtain r6₄ : s₄.gpr .a3 = s₀.gpr .a1 := by
    rw [hg₄ _ (by decide), g₂ _ (by decide) (by decide), r6₁]
  obtain wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₂, wr₁]
  obtain hlow : ∀ k < slots, (k < klSlot ∨ krSlot + 2 ≤ k) → slotW s₄ k = slotW s₁ k := fun k hk h => by
    rw [hs₄, sl₂ k hk h]
  let KL : BitVec 64 × BitVec 64 := (hiW (Spec.Camellia.klkr key).1, loW (Spec.Camellia.klkr key).1)
  let KR : BitVec 64 × BitVec 64 := (hiW (Spec.Camellia.klkr key).2, loW (Spec.Camellia.klkr key).2)
  obtain hpre : KaPre s₄ KL KR := by
    refine ⟨⟨?_, by rw [hb₄]; exact hal, ?_, by decide, fun kv hkv => ?_, fun i hi => ?_⟩, ?_,
      kl₂.congr (hs₄ _) (hs₄ _), kr₂.congr (hs₄ _) (hs₄ _)⟩
    · rw [hb₄, wr₄']; exact hwB
    · rw [hb₄]; exact fitB
    · have := mask_lt hkv
      rw [hlow _ (by omega_using [hE, hS, this]) (Or.inl (by omega_using [hl', hE, this]))]; exact mk₁ kv hkv
    · refine sigmas_rel (m := s₄.mem) (b := s₄.gpr sb) (fun i hi j hj => ?_) i hi
      rw [entryW_slot, hlow _ (by omega_using [hK, hS, hi, hj]) (Or.inr (by omega_using [hr', hK])), ← entryW_slot, b₁]
      exact ent₁ i hi j hj
    · rw [AtEntry, a₄, hb₄, hb₂]; simp
  -- `KA` and `KB`.
  refine WP.seq (WP.mono (kaKb_wp hpre) fun s₅ h₅ => ?_)
  obtain hb₅ : s₅.gpr sb = s₀.gpr .a3 := h₅.base.trans hb₄
  obtain wr₅ : s₅.wr = s₀.wr := h₅.wr.trans wr₄'
  obtain hscr₅ : (⟨s₀.gpr .a3, 8 * slots⟩ : Region) ∈ s₅.wr := by rw [wr₅]; exact hwB
  -- The values, byte-swapped into registers.
  obtain ⟨hKA, hKB⟩ := kaD_eq (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2
  have hKA' : kaD2 KL KR = _ := hKA
  have hKB' : kaD3 KL KR = _ := hKB
  obtain ⟨s₆, e₆, v₆, o₆, m₆, rd₆, wr₆⟩ := loadValues_ok (s := s₅) (by rw [hb₅]; exact hscr₅)
    [(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
      (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
      (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2] (fun v hv => by
      rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_using [hv]) with rfl | rfl | rfl | rfl
      · exact h₅.kl hpre
      · exact h₅.kr hpre
      · have := h₅.ka (by decide); rw [hKA'] at this; exact this
      · have := h₅.kb (by decide); rw [hKB'] at this; exact this)
  obtain hnv : ∀ r : Reg, r ∈ [sb, Reg.a2, Reg.a3] → ∀ v < 4, r ≠ hiReg v ∧ r ≠ loReg v := by decide
  obtain hb₆ : s₆.gpr sb = s₀.gpr .a3 := by rw [o₆ _ (hnv _ (by simp)) (by decide), hb₅]
  obtain r6₅ : s₅.gpr .a3 = s₀.gpr .a1 := by
    rw [h₅.regs _ (by decide) (by decide) (by decide) (by decide), r6₄]
  -- The key's length.
  obtain ⟨s₈, e₈, z₈, g₈, m₈, rd₈, wr₈⟩ := subI_ok s₆ t0 .a3 16 (by decide)
  obtain hz₈ : (s₈.gpr t0 == 0) = decide ((s₀.gpr .a1).toNat = 16) := by
    rw [z₈, o₆ _ (hnv _ (by simp)) (by decide), r6₅]
    conv => lhs; rw [show s₀.gpr .a1 = BitVec.ofNat 64 (s₀.gpr .a1).toNat by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]]
    rw [VG.Offset.ofNat_sub_ofNat_beq (by omega_using []) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨s₈, by rw [runBlock_append', e₆, Option.bind_some, e₈], ?_⟩)
  -- The subkeys.
  obtain hx2₈ : s₈.gpr .a2 = s₀.gpr .a2 := by
    rw [g₈ _ (by decide), o₆ _ (hnv _ (by simp)) (by decide), h₅.regs _ (by decide) (by decide) (by decide) (by decide), r5₄]
  obtain hwS₈ : (⟨s₀.gpr .a2, 272⟩ : Region) ∈ s₈.wr := by rw [wr₈, wr₆, wr₅]; exact hwS
  obtain hg₈ : ∀ v < 4, s₈.gpr (hiReg v) = hiW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0) ∧
      s₈.gpr (loReg v) = loW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0) :=
    fun v hv => by
      obtain ⟨n1, -, n3, -⟩ := hiReg_ne v hv
      rw [g₈ _ n1, g₈ _ n3]; exact v₆ v hv
  obtain hklen : key.length = (s₀.gpr .a1).toNat := by rw [← hkey]; simp [Spec.Camellia.bytesAt]
  refine WP.seq (WP.mono (Q := StoresPost s₈ (s₀.gpr .a2) (s₀.gpr .a1).toNat key)
    (WP.ite (decide ((s₀.gpr .a1).toNat = 16)) ((eval_zero s₈ t0).trans (by rw [hz₈])) (fun h16 => ?_)
      (fun h16 => ?_))
    fun s₉ h₉ => ?_)
  · have h16 : (s₀.gpr .a1).toNat = 16 := by simpa using h16
    exact stores_wp hx2₈ hwS₈ subkeys_lt4.1 (by rw [subkeys_length.1]; omega_using []) hg₈
      (by rw [h16, subkeys_length.1]; rfl) (by rw [hklen, ite_eq_left h16])
  · have h16 : (s₀.gpr .a1).toNat ≠ 16 := by simpa using h16
    exact stores_wp hx2₈ hwS₈ subkeys_lt4.2 (by rw [subkeys_length.2]) hg₈
      (by rw [subkeys_length.2]; simp only [Spec.Camellia.rounds, h16, ↓reduceIte]; rfl)
      (by rw [hklen, ite_eq_right h16])
  -- The epilogue.
  obtain hb₉ : s₉.gpr sb = s₀.gpr .a3 := by rw [h₉.regs _ (by decide) (by decide), g₈ _ (by decide), hb₆]
  obtain hSB : ∀ k, savedSlot ≤ k → k < savedSlot + 12 →
      s₉.mem.readW (wordAddr (s₀.gpr .a3) k) 64 = s₁.mem.readW (wordAddr (s₀.gpr .a3) k) 64 := by
    intro k h1 h2
    rw [h₉.frame.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dSB.sub_right (by rw [wordAddr]; exact VG.Offset.sub_base _ (by omega_using [hE, hS, h2]))).symm) (by decide)]
    have := h₅.keep k (by omega_using [h1]) (by omega_using [hE, hS, h2]) (Or.inl (by omega_using [hW, hE, h2]))
    rw [hs₄, sl₂ k (by omega_using [hE, hS, h2]) (Or.inl (by omega_using [hl', hE, h2]))] at this
    simp only [slotW, hb₅, b₁] at this
    rw [m₈, m₆]
    exact this
  obtain ⟨s₁₀, e₁₀, rg₁₀, -, m₁₀, -, -⟩ := restore_ok (s₀ := s₀) (b := s₀.gpr .a3)
    (by rw [h₉.wr, wr₈, wr₆, wr₅]; exact hwB) hb₉ hal (fun i hi => by
      rw [hSB _ (by omega_using []) (by omega_using [hi])]; exact sv₁ i hi)
  refine WP.of_runBlock ⟨s₁₀, e₁₀, rg₁₀, ?_⟩
  show Spec.Camellia.bytesAt s₁₀.mem (s₀.gpr .a2) _ = _
  rw [hkey, m₁₀, ← h₉.bytes]

end VG.Proof.Camellia.RISCV64

end

end


/-!
# The Camellia key schedule on RISC-V meets its contracts

As on PPC64LE (`Proof/Camellia/PPC64LE/KeyVerified.lean`):
`expandKey_verified`: `expandKey` is correct (`expandKey_wp`) and constant
time (`expandKey_ct`). `expandKey_framed` runs it with its working space on
the stack, zeroed on return: 3200 bytes, for the 400 words of the scratch
buffer.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.Impl.Camellia.RISCV64

/-- The registers the key schedule writes. -/
def expandKeyWrites : List Reg :=
  [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7,
   .s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11]

theorem expandKey_correct (s : State) (hs : expandKeyRISCV64.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyRISCV64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, hk⟩ := WP.keep expandKeyWrites (expandKey_wp hs) (by lit_decide) (by lit_decide)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, hk.gpr (by decide)⟩, h₂⟩
  obtain ⟨i, hi, rfl⟩ := preserved_sreg r hr
  exact h₁ i hi

/-- A state satisfying the precondition (a key of 16 bytes). -/
def expandKeySat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 16 | .a2 => 0x3000 | .a3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x3000, 272⟩, ⟨0x4000, 8 * 400⟩]

theorem expandKey_verified :
    Verified target expandKey (Proof.Camellia.expandKeyScratchContract abi slots) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Camellia.expandKeyScratchContract, Proof.Camellia.expandKeyScratchSig,
      Spec.Camellia.expandKeySig, Spec.Camellia.expandKeyPre, Spec.Camellia.expandKeyPost, expandKeyRISCV64,
      abi, argRegs, slots, tailSlot, savedSlot, keySlot] [expandKeySat]
      using expandKeySat)

/-- A state satisfying the key schedule's precondition: a key of 16 bytes at
`0x1000`, the schedule at `0x3000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 16 | .a2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x3000, 272⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Camellia.expandKeyContract abi 3200).pre s := by
  implies_sat [Spec.Camellia.expandKeyContract, Spec.Camellia.expandKeySig, Spec.Camellia.expandKeyPre,
    Spec.Camellia.expandKeyPost, abi, argRegs] [expandKeyFrameSat] using expandKeyFrameSat

/-- The key schedule, with its working space on the stack. -/
theorem expandKey_framed :
    Verified target (Impl.StackScratch.RISCV64.withStackScratchWiped 3200 .a3 400 expandKey)
      (Spec.Camellia.expandKeyContract abi 3200) :=
  Verified.stackScratchWiped (sig := Spec.Camellia.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 400) (pre := Spec.Camellia.expandKeyPre abi.ptrBits)
    (post := Spec.Camellia.expandKeyPost abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 3200) (words := 400) (by rw [← Proof.Camellia.expandKeyScratchContract_eq]; exact expandKey_verified)
    (by decide) (by decide) (by decide) (Proof.Camellia.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Camellia.RISCV64
