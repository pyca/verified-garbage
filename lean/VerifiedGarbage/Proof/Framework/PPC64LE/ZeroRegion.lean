module

public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Zeroing a region of memory (PPC64LE)

`zeroRegion_run`: `Impl.Scrub.PPC64LE.zeroRegion n`, from `r12 = q` with `r0`
zero, zeroes the `n` bytes at `q`, within a writable region `⟨q, B⟩`, and
nothing else, with a trace of the addresses alone. The clearing of
`scrubTail` zeroes its frames' regions with it
(`Proof/Framework/PPC64LE/Scrub.lean`), and `withStackScratchWiped` its buffer
(`Proof/Framework/PPC64LE/StackScratchWipe.lean`).
-/

@[expose] public section

open VG.Impl.Scrub.PPC64LE

namespace VG.PPC64LE.Scrub

/-- A byte `d < n` bytes above `a`, where `a` and its `n` bytes do not wrap
around, is at `a.toNat + d`. -/
theorem toNat_of_sub_lt {a x : Addr} {n : Nat} (hn : a.toNat + n ≤ 2 ^ 64) (h : (x - a).toNat < n) :
    x.toNat = a.toNat + (x - a).toNat := by
  have e : x = a + (x - a) := by bv_omega
  have he := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega_using [hn, h])] at he
  exact he

theorem toNat_sub_ofNat (p : Addr) (b : Nat) (h : b ≤ p.toNat) :
    (p - BitVec.ofNat 64 b).toNat = p.toNat - b := by
  have := p.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := b) (by omega_using [h]),
    show 2 ^ 64 - b + p.toNat = (p.toNat - b) + 2 ^ 64 by omega_using [h], Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega_using [])]

theorem toNat_add_ofNat (q : Addr) (o : Nat) (h : q.toNat + o < 2 ^ 64) :
    (q + BitVec.ofNat 64 o).toNat = q.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [h]),
    Nat.mod_eq_of_lt h]

/-! ## The clearing's run -/

/-- `d` bytes above `a` is within `n` bytes of it, where `a` and its `n`
bytes do not wrap around, as natural numbers. -/
theorem sub_lt_iff {a x : Addr} {n : Nat} (hn : a.toNat + n ≤ 2 ^ 64) :
    (x - a).toNat < n ↔ a.toNat ≤ x.toNat ∧ x.toNat < a.toNat + n := by
  constructor
  · intro h
    have := toNat_of_sub_lt hn h
    omega_using [this, h]
  · rintro ⟨h₁, h₂⟩
    rw [BitVec.toNat_sub]
    have := a.isLt
    rw [show 2 ^ 64 - a.toNat + x.toNat = (x.toNat - a.toNat) + 2 ^ 64 by omega_using [h₁, this],
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [h₁, h₂, hn])]
    omega_using [h₁, h₂]

/-- `m` with the bytes at offsets `lo` to `hi - 1` from `q` zeroed. -/
def zeroOn (q : Addr) (lo hi : Nat) (m : Mem) : Mem :=
  fun x => if lo ≤ (x - q).toNat ∧ (x - q).toNat < hi then 0 else m x

theorem off_lt (x p : Addr) (o n : Nat) (ho : o + n < 2 ^ 64) :
    (x - (p + BitVec.ofNat 64 o)).toNat < n ↔ o ≤ (x - p).toNat ∧ (x - p).toNat < o + n := by
  have e : (x - (p + BitVec.ofNat 64 o)) + BitVec.ofNat 64 o = x - p := by bv_omega
  have e' := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [ho])] at e'
  have h1 := (x - (p + BitVec.ofNat 64 o)).isLt
  have h2 := (x - p).isLt
  generalize (x - (p + BitVec.ofNat 64 o)).toNat = r at *
  generalize (x - p).toNat = d at *
  by_cases hc : r + o < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hc] at e'; omega_using [e']
  · rw [show r + o = (r + o - 2 ^ 64) + 2 ^ 64 by omega_using [hc], Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_using [ho, h1])] at e'
    omega_using [ho, h1, e', hc]

/-- The trace of `stores k n` from `r12 = q`. -/
def storesTr (q : Addr) : Nat → Nat → List Leak
  | _, 0 => []
  | k, n + 1 => .addr (q + BitVec.ofNat 64 (8 * k)) :: storesTr q (k + 1) n

/-- `stores k n` zeroes the doublewords at offsets `8k` to `8(k + n) - 1`
from `r12 = q + o`, within a writable region `⟨q, B⟩`. -/
theorem storesAt_run (q : Addr) (o B : Nat) (hB : B < 4096) (hqB : q.toNat + B ≤ 2 ^ 64) :
    ∀ (n k : Nat) (u : State), o + 8 * (k + n) ≤ B → u.gpr .r0 = 0 →
      u.gpr .r12 = q + BitVec.ofNat 64 o → ⟨q, B⟩ ∈ u.wr →
      execBlock isa (stores k n) u = some ({ u with
          mem := zeroOn (q + BitVec.ofNat 64 o) (8 * k) (8 * (k + n)) u.mem },
        storesTr (q + BitVec.ofNat 64 o) k n)
  | 0, k, u, _, _, _, _ => by
    simp only [stores, execBlock, storesTr]
    congr
    cases u; simp only [State.mk.injEq, and_true, true_and]
    funext x; simp only [zeroOn, Nat.add_zero]; split
    · next h => omega_using [h.1, h.2]
    · rfl
  | n + 1, k, u, hk, h0, h1, hw => by
    have hlt : q.toNat + (o + 8 * k) < 2 ^ 64 := by omega_using [hk, hqB]
    have hc : InRegions u.wr (u.gpr .r12 + BitVec.ofNat 64 (8 * k)) 8 := by
      refine ⟨_, hw, ?_⟩
      simp only [Region.Contains]
      rw [h1, show q + BitVec.ofNat 64 o + BitVec.ofNat 64 (8 * k) - q = BitVec.ofNat 64 (o + 8 * k) by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]; bv_omega,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hlt])]
      omega_using [hk]
    simp only [stores, execBlock, exec_store_d (show Reg.r12 ≠ .r0 by decide)
      ⟨by omega_using [hk, hB], by omega_using []⟩ hc]
    rw [storesAt_run q o B hB hqB n (k + 1) { u with mem := u.mem.writeW (u.gpr .r12 + BitVec.ofNat 64 (8 * k)) (u.gpr .r0) }
      (by omega_using [hk]) h0 h1 hw]
    have hm : zeroOn (q + BitVec.ofNat 64 o) (8 * (k + 1)) (8 * (k + 1 + n))
        (u.mem.writeW (u.gpr .r12 + BitVec.ofNat 64 (8 * k)) (u.gpr .r0)) =
        zeroOn (q + BitVec.ofNat 64 o) (8 * k) (8 * (k + (n + 1))) u.mem := by
      funext x
      have e := off_lt x (q + BitVec.ofNat 64 o) (8 * k) 8 (by omega_using [hk, hB])
      simp only [zeroOn, Mem.writeW, Mem.write, h0, h1, Nat.reduceDiv, Nat.reduceMul]
      generalize (x - (q + BitVec.ofNat 64 o + BitVec.ofNat 64 (8 * k))).toNat = r at e ⊢
      generalize (x - (q + BitVec.ofNat 64 o)).toNat = d at e ⊢
      repeat' split
      all_goals first | (exfalso; omega) | rfl | (simp; done)
    simp only [Option.map_some, isa, addrs, h1, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, storesTr]
    rw [h1] at hm
    rw [hm]

/-! ### The `dcbz`s of `zeroRegion`

`dcbz r12, r0` zeroes the 128-byte block holding `r12`, at `r12` with its
low 7 bits cleared (`toNat_align`). From `r12 = q`, the blocks of
`zeroBlocks` start `blockOff q 1` bytes past `q` (between 1 and 128) and
follow each other (`blockOff_succ`), so together with the `std`s of the first
128 bytes and of those from the last `r12` on they zero the region and
nothing outside it (`zeroRegion_run`). -/

/-- Clearing the low 7 bits of a 64-bit number. -/
theorem nat_align (n : Nat) (hn : n < 2 ^ 64) : n &&& (2 ^ 57 - 1) * 2 ^ 7 = n / 2 ^ 7 * 2 ^ 7 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_two_pow_sub_one]
  by_cases h7 : 7 ≤ i
  · by_cases h64 : i < 64
    · simp [h7, show i - 7 < 57 by omega, show i - 7 + 7 = i by omega]
    · have : n.testBit i = false := Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [h7, show ¬ i - 7 < 57 by omega, show i - 7 + 7 = i by omega, this]
  · simp [h7]

/-- The address of the block `dcbz` zeroes. -/
theorem toNat_align (y : Addr) :
    (y &&& ~~~BitVec.ofNat 64 (dcbzBytes - 1)).toNat = y.toNat / 128 * 128 := by
  have hy := y.isLt
  rw [BitVec.toNat_and, BitVec.toNat_not]
  simp only [dcbzBytes, BitVec.toNat_ofNat]
  exact nat_align _ hy

/-- Each byte of zero is zero. -/
theorem extract_zero (w r : Nat) : BitVec.extractLsb' r 8 (0 : BitVec w) = 0 := by
  simp [BitVec.extractLsb']

/-- The offset from `q` of the block `dcbz` zeroes at `q + 128 j`. -/
def blockOff (q : Addr) (j : Nat) : Nat := (q.toNat + 128 * j) / 128 * 128 - q.toNat

/-- The blocks follow each other. -/
theorem blockOff_succ (q : Addr) (j : Nat) (hj : 1 ≤ j) : blockOff q j = blockOff q 1 + 128 * (j - 1) := by
  simp only [blockOff]; omega

/-- The first block starts within the first 128 bytes, past `q`. -/
theorem blockOff_one (q : Addr) : 1 ≤ blockOff q 1 ∧ blockOff q 1 ≤ 128 := by
  simp only [blockOff]; omega

/-- The block `dcbz` zeroes at `q + 128 j`, `j ≥ 1`, as an offset from `q`. -/
theorem dcbz_addr (q : Addr) (j : Nat) (hj : 1 ≤ j) (h : q.toNat + 128 * j < 2 ^ 64) :
    (q + BitVec.ofNat 64 (128 * j)) &&& ~~~BitVec.ofNat 64 (dcbzBytes - 1) =
      q + BitVec.ofNat 64 (blockOff q j) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_align, toNat_add_ofNat _ _ h, toNat_add_ofNat _ _ (by simp only [blockOff]; omega)]
  simp only [blockOff]; omega

/-- Of two writes of `r12`, the last is what is left. -/
theorem write_write12 (s : State) (a b : Addr) : (s.write .r12 a).write .r12 b = s.write .r12 b := by
  cases s; simp only [State.write, State.mk.injEq, and_true]
  funext r; split <;> rfl

/-- Writing `r12` with what it holds changes nothing. -/
theorem write_self12 (s : State) : s.write .r12 (s.gpr .r12) = s := by
  cases s; simp only [State.write, State.mk.injEq, and_true]
  funext r; split <;> simp_all

/-- The trace of `zeroBlocks k` from `r12 = q + 128 j`. -/
def zeroBlocksTr (q : Addr) (j : Nat) : Nat → List Leak
  | 0 => []
  | k + 1 => .addr (q + BitVec.ofNat 64 (128 * (j + 1))) :: zeroBlocksTr q (j + 1) k

/-- `zeroBlocks k` from `r12 = q + 128 j` zeroes its `k` blocks, within a
writable region `⟨q, n⟩` that ends past the last of them. -/
theorem zeroBlocks_run (q : Addr) (n : Nat) (hqn : q.toNat + n ≤ 2 ^ 64) (hn : n < 4096) :
    ∀ (k j : Nat) (u : State), 128 * (j + k) + 128 ≤ n → u.gpr .r0 = 0 →
      u.gpr .r12 = q + BitVec.ofNat 64 (128 * j) → ⟨q, n⟩ ∈ u.wr →
      execBlock isa (zeroBlocks k) u = some ({ u.write .r12 (q + BitVec.ofNat 64 (128 * (j + k))) with
          mem := zeroOn q (blockOff q 1 + 128 * j) (blockOff q 1 + 128 * (j + k)) u.mem },
        zeroBlocksTr q j k)
  | 0, j, u, _, _, h12, _ => by
    simp only [zeroBlocks, execBlock, zeroBlocksTr, Nat.add_zero, ← h12, write_self12]
    congr
    cases u; simp only [State.mk.injEq, and_true, true_and]
    funext x; simp only [zeroOn]; split
    · next h => omega
    · rfl
  | k + 1, j, u, hk, h0, h12, hw => by
    have hb := blockOff_one q
    have hbo := blockOff_succ q (j + 1) (by omega)
    have hlt : q.toNat + 128 * (j + 1) < 2 ^ 64 := by omega
    -- after `addi`
    have ha : exec (.addi .r12 .r12 128) u = some (u.write .r12 (q + BitVec.ofNat 64 (128 * (j + 1)))) := by
      rw [exec_addi (by decide) (by decide), h12]
      congr 2
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2
    generalize hu₁ : u.write .r12 (q + BitVec.ofNat 64 (128 * (j + 1))) = u₁ at ha
    have hu₁12 : u₁.gpr .r12 = q + BitVec.ofNat 64 (128 * (j + 1)) := by rw [← hu₁]; exact RegUpd.gpr_write_self ..
    have hu₁0 : u₁.gpr .r0 = 0 := by rw [← hu₁, RegUpd.gpr_write_of_ne _ _ (by decide)]; exact h0
    have hu₁wr : u₁.wr = u.wr := by rw [← hu₁]; rfl
    have hu₁m : u₁.mem = u.mem := by rw [← hu₁]; rfl
    have hea : u₁.gpr .r12 + u₁.gpr .r0 = q + BitVec.ofNat 64 (128 * (j + 1)) := by
      rw [hu₁12, hu₁0]; exact BitVec.add_zero _
    have hal := dcbz_addr q (j + 1) (by omega) hlt
    have hin : InRegions u₁.wr (q + BitVec.ofNat 64 (blockOff q (j + 1))) dcbzBytes := by
      refine ⟨_, hu₁wr ▸ hw, ?_⟩
      simp only [Region.Contains, dcbzBytes]
      rw [show q + BitVec.ofNat 64 (blockOff q (j + 1)) - q = BitVec.ofNat 64 (blockOff q (j + 1)) by bv_omega,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hd : exec (.dcbz .r12 .r0) u₁ =
        some { u₁ with mem := u₁.mem.write (q + BitVec.ofNat 64 (blockOff q (j + 1))) dcbzBytes 0 } := by
      simp only [exec, addrX, show Reg.r12 ≠ .r0 by decide, ne_eq, not_false_eq_true, ite_true,
        Option.bind_some, hea, hal, State.store, hin]
    have ih := zeroBlocks_run q n hqn hn k (j + 1)
      { u₁ with mem := u₁.mem.write (q + BitVec.ofNat 64 (blockOff q (j + 1))) dcbzBytes 0 }
      (by omega) hu₁0 hu₁12 (hu₁wr ▸ hw)
    simp only [zeroBlocks, execBlock, isa] at ha hd ih ⊢
    simp only [ha, hd, ih, Option.map_some]
    have hm : zeroOn q (blockOff q 1 + 128 * (j + 1)) (blockOff q 1 + 128 * (j + 1 + k))
        (u₁.mem.write (q + BitVec.ofNat 64 (blockOff q (j + 1))) dcbzBytes 0) =
        zeroOn q (blockOff q 1 + 128 * j) (blockOff q 1 + 128 * (j + (k + 1))) u.mem := by
      rw [hu₁m]
      funext x
      have e := off_lt x q (blockOff q (j + 1)) dcbzBytes (by simp only [dcbzBytes]; omega)
      simp only [zeroOn, Mem.write]
      generalize (x - (q + BitVec.ofNat 64 (blockOff q (j + 1)))).toNat = r at e ⊢
      generalize (x - q).toNat = d at e ⊢
      have hdz : dcbzBytes = 128 := rfl
      by_cases h1 : r < dcbzBytes <;>
        by_cases h2 : blockOff q 1 + 128 * (j + 1) ≤ d ∧ d < blockOff q 1 + 128 * (j + 1 + k) <;>
        by_cases h3 : blockOff q 1 + 128 * j ≤ d ∧ d < blockOff q 1 + 128 * (j + (k + 1)) <;>
        simp only [h1, h2, h3, ite_true, ite_false] <;>
        first | (exfalso; omega) | simp only [extract_zero, and_self, ite_true]
    rw [hm, show j + 1 + k = j + (k + 1) by omega]
    simp only [zeroBlocksTr, addrs, hea, List.map_cons, List.map_nil, List.nil_append, List.cons_append]
    rw [← hu₁]
    cases u
    simp only [State.write, Option.some.injEq, Prod.mk.injEq, State.mk.injEq, and_true]
    funext r; split <;> rfl


/-- Where `zeroRegion n` leaves `r12`, from `r12 = q`. -/
def zeroEnd (q : Addr) (n : Nat) : Addr :=
  if n < 512 then q else q + BitVec.ofNat 64 (128 * ((n - 128) / 128))

/-- The trace of `zeroRegion n` from `r12 = q`. -/
def zeroTr (q : Addr) (n : Nat) : List Leak :=
  if n < 512 then storesTr (q + BitVec.ofNat 64 0) 0 (n / 8)
  else storesTr (q + BitVec.ofNat 64 0) 0 16 ++ zeroBlocksTr q 0 ((n - 128) / 128) ++
    storesTr (q + BitVec.ofNat 64 (128 * ((n - 128) / 128))) 0 ((n - 128 * ((n - 128) / 128)) / 8)

/-- `zeroRegion n` zeroes the first `n` bytes of the writable region `⟨q, B⟩`
at `r12 = q`. -/
theorem zeroRegion_runIn (q : Addr) (n B : Nat) (hnB : n ≤ B) (hB : B < 4096) (h8 : n % 8 = 0)
    (hqB : q.toNat + B ≤ 2 ^ 64)
    (u : State) (h0 : u.gpr .r0 = 0) (h12 : u.gpr .r12 = q) (hw : ⟨q, B⟩ ∈ u.wr) :
    execBlock isa (zeroRegion n) u =
      some ({ u.write .r12 (zeroEnd q n) with mem := zeroOn q 0 n u.mem }, zeroTr q n) := by
  have hq0 : q + BitVec.ofNat 64 0 = q := BitVec.add_zero q
  have h12' : u.gpr .r12 = q + BitVec.ofNat 64 0 := by rw [hq0]; exact h12
  by_cases hs : n < 512
  · simp only [zeroRegion, zeroEnd, zeroTr, hs, ite_true]
    rw [storesAt_run q 0 B hB hqB (n / 8) 0 u (by omega) h0 h12' hw, hq0,
      show 8 * (0 + n / 8) = n by omega, show 8 * 0 = 0 from rfl, ← h12, write_self12]
  · simp only [zeroRegion, zeroEnd, zeroTr, hs, ite_false]
    generalize hK : (n - 128) / 128 = K
    have hK1 : 128 * K + 128 ≤ n := by omega
    have hK2 : n - 128 * K < 256 := by omega
    have hb := blockOff_one q
    have hm : zeroOn (q + BitVec.ofNat 64 (128 * K)) (8 * 0) (8 * (0 + (n - 128 * K) / 8))
        (zeroOn q (blockOff q 1 + 128 * 0) (blockOff q 1 + 128 * (0 + K))
          (zeroOn (q + BitVec.ofNat 64 0) (8 * 0) (8 * (0 + 16)) u.mem)) = zeroOn q 0 n u.mem := by
      funext x
      have e := off_lt x q (128 * K) (n - 128 * K) (by omega)
      rw [hq0]
      simp only [zeroOn]
      generalize (x - (q + BitVec.ofNat 64 (128 * K))).toNat = r at e ⊢
      generalize (x - q).toNat = d at e ⊢
      by_cases h1 : 8 * 0 ≤ r ∧ r < 8 * (0 + (n - 128 * K) / 8) <;>
        by_cases h2 : blockOff q 1 + 128 * 0 ≤ d ∧ d < blockOff q 1 + 128 * (0 + K) <;>
        by_cases h3 : 8 * 0 ≤ d ∧ d < 8 * (0 + 16) <;>
        by_cases h4 : 0 ≤ d ∧ d < n <;>
        simp only [h1, h2, h3, h4, ite_false] <;>
        first | (exfalso; omega) | rfl
    rw [execBlock_append, execBlock_append,
      storesAt_run q 0 B hB hqB 16 0 u (by omega) h0 h12' hw]
    simp only [Option.bind_some]
    generalize hu₁ : ({ u with mem := zeroOn (q + BitVec.ofNat 64 0) (8 * 0) (8 * (0 + 16)) u.mem } : State) = u₁
    rw [zeroBlocks_run q B hqB hB K 0 u₁ (by omega) (by rw [← hu₁]; exact h0)
      (by rw [← hu₁, Nat.mul_zero]; exact h12') (by rw [← hu₁]; exact hw)]
    simp only [Option.map_some, Option.bind_some]
    generalize hu₂ : ({ u₁.write .r12 (q + BitVec.ofNat 64 (128 * (0 + K))) with
      mem := zeroOn q (blockOff q 1 + 128 * 0) (blockOff q 1 + 128 * (0 + K)) u₁.mem } : State) = u₂
    rw [storesAt_run q (128 * K) B hB hqB ((n - 128 * K) / 8) 0 u₂ (by omega)
      (by rw [← hu₂, RegUpd.gpr_write_of_ne _ _ (by decide), ← hu₁]; exact h0)
      (by rw [← hu₂, RegUpd.gpr_write_self, Nat.zero_add])
      (by rw [← hu₂, ← hu₁]; exact hw)]
    simp only [Option.map_some, List.append_assoc]
    subst hu₂ hu₁
    rw [← hm]
    cases u
    simp only [State.write, Nat.zero_add]

/-- `zeroRegion n` zeroes the `n` bytes of the writable region at `r12 = q`. -/
theorem zeroRegion_run (q : Addr) (n : Nat) (hn : n < 4096) (h8 : n % 8 = 0) (hqn : q.toNat + n ≤ 2 ^ 64)
    (u : State) (h0 : u.gpr .r0 = 0) (h12 : u.gpr .r12 = q) (hw : ⟨q, n⟩ ∈ u.wr) :
    execBlock isa (zeroRegion n) u =
      some ({ u.write .r12 (zeroEnd q n) with mem := zeroOn q 0 n u.mem }, zeroTr q n) :=
  zeroRegion_runIn q n n (Nat.le_refl n) hn h8 hqn u h0 h12 hw

end VG.PPC64LE.Scrub
