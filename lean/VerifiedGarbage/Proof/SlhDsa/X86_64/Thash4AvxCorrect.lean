module

public import VerifiedGarbage.Proof.Sha3.X86_64.X4.Round
public import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha3.Spec
public import VerifiedGarbage.Proof.Sha3.X86_64.Permute
public import VerifiedGarbage.Proof.Sha3.X86_64.X4.Wp
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Thash4
public import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4Contract
public import VerifiedGarbage.Proof.SlhDsa.Shake
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Squeeze
import VerifiedGarbage.Proof.Framework.X86_64.Steps
import VerifiedGarbage.Proof.Sha3.Arith

/-!
# SLH-DSA on x86-64: `thash4` with AVX2, correctness

`thash4 n fast` from a state satisfying `Thash4Pre n 0` ends with each
output `SHAKE256` of its message (`correct`). The proof follows the code:
the prologue (`pro_ok`), the loop that absorbs a word of each message at a
time with the invariant `Inv` (`body_ok`), the padding, the last
permutation and the extraction.
-/

@[expose] public section

/-! ## SLH-DSA on x86-64: the four interleaved Keccak states, byte by byte

The four states at `p` (`Lanes4`, lane `i` of state `k` at `p + 32 i + 8 k`)
as their bytes, byte `q` of state `k` at `ba p k q`; and what writing one
lane, its bytes XORed with eight bytes, does to them (`lanes4_xorLane`), and
writing a lane with its bytes XORed with eight others in a block
(`xorAt`), as the absorbing of `thash4` does.
-/


namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64
open VG.Proof.Sha3.X86_64.X4 (Lanes4 la KState)
open VG.Proof.Sha3 (byteOf byteOf_eq xorAt byteOf_xorAt getElem!_eq)

/-- Byte `q` of state `k` of the four at `p`. -/
abbrev ba (p : Addr) (k q : Nat) : Addr := p + BitVec.ofNat 64 (32 * (q / 8) + 8 * k + q % 8)

/-- Two lanes with the same bytes. -/
theorem lane_ext {v w : BitVec 64} (h : ∀ j < 8, v.extractLsb' (8 * j) 8 = w.extractLsb' (8 * j) 8) :
    v = w := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have := congrArg (·.getLsbD (b % 8)) (h (b / 8) (by omega_using [hb]))
  simp only [BitVec.getLsbD_extractLsb', show b % 8 < 8 by omega_using [], decide_true, Bool.true_and] at this
  rwa [show 8 * (b / 8) + b % 8 = b by omega_using []] at this

theorem la_byte (p : Addr) {i k j : Nat} (hj : j < 8) :
    la p i k + BitVec.ofNat 64 j = ba p k (8 * i + j) := by
  rw [la, BitVec.add_assoc, ← BitVec.ofNat_add, ba, show (8 * i + j) / 8 = i by omega_using [hj],
    show (8 * i + j) % 8 = j by omega_using [hj]]

theorem lanes4_of_bytes {m : Mem} {p : Addr} {A : Nat → KState}
    (h : ∀ k < 4, ∀ q < 200, m (ba p k q) = byteOf (A k) q) : Lanes4 m p A := fun i hi k hk =>
  lane_ext fun j hj => by
    rw [byte_readW _ _ (by omega_using [hj]), la_byte _ hj, h k hk _ (by omega_using [hi, hj]),
      byteOf_eq _ hi hj, getElem!_eq _ hi]

theorem byte_of_lanes4 {m : Mem} {p : Addr} {A : Nat → KState} (h : Lanes4 m p A) {k q : Nat} (hk : k < 4)
    (hq : q < 200) : m (ba p k q) = byteOf (A k) q := by
  rw [byteOf, ← h (q / 8) (by omega_using [hq]) k hk, byte_readW _ _ (by omega_using []),
    la_byte _ (by omega_using []), show 8 * (q / 8) + q % 8 = q by omega_using []]

/-- The offset of byte `q` of state `k` within the 800 bytes. -/
theorem ba_off_lt {k q : Nat} (hk : k < 4) (hq : q < 200) : 32 * (q / 8) + 8 * k + q % 8 < 800 := by
  omega_using [hk, hq]

/-- Writing lane `i` of state `k`, its bytes those of the lane XORed with
`bs`: state `k` has `bs` XORed into its bytes `8 i` to `8 i + 7`, and the
others are unchanged. -/
theorem lanes4_xorLane {m : Mem} {p : Addr} {A : Nat → KState} (h : Lanes4 m p A) {i k : Nat}
    (hi : i < 25) (hk : k < 4) {v : BitVec 64} {bs : List Byte} (hbs : bs.length = 8)
    (hv : ∀ d < 8, v.extractLsb' (8 * d) 8 = m (la p i k + BitVec.ofNat 64 d) ^^^ bs.getD d 0) :
    Lanes4 (m.writeW (la p i k) v) p (fun k' => if k' = k then xorAt (A k') (8 * i) bs else A k') := by
  refine lanes4_of_bytes fun k' hk' q hq => ?_
  by_cases c : k' = k ∧ q / 8 = i
  · obtain ⟨rfl, hqi⟩ := c
    have e : ba p k' q = la p i k' + BitVec.ofNat 64 (q % 8) := by
      rw [la_byte _ (by omega_using []), ← hqi, show 8 * (q / 8) + q % 8 = q by omega_using []]
    rw [e, writeW_byte _ _ _ (by omega_using []) (by decide), hv _ (by omega_using []), la_byte _ (by omega_using []),
      ← hqi, show 8 * (q / 8) + q % 8 = q by omega_using [], byte_of_lanes4 h hk hq, ite_eq_left rfl,
      byteOf_xorAt _ _ _ hq, hbs, ite_eq_left (by omega_using [hqi]), show q - 8 * (q / 8) = q % 8 by omega_using []]
  · have hne : 8 ≤ (ba p k' q - la p i k).toNat := by
      rw [ba, la, Offset.sub_toNat' _ (by omega_using [hi, hk]) (by omega_using [hk', hq])]
      split <;> rename_i hs <;> omega_using [c, hi, hk, hk', hq, hs]
    rw [writeW_byte_off _ _ _ _ (by omega_using [hne]), byte_of_lanes4 h hk' hq]
    by_cases e : k' = k
    · subst e
      rw [ite_eq_left rfl, byteOf_xorAt _ _ _ hq, hbs, ite_eq_right (by omega_using [c])]
    · rw [ite_eq_right e]

end VG.Proof.SlhDsa.X86_64

/-! ## SLH-DSA on x86-64: `thash4` with AVX2, the steps

Weakest-precondition rules the proof of `thash4` needs beyond those of
`Proof/Sha3/X86_64/Permute.lean` (`cmp` with an immediate, `vzeroupper`),
the addresses of its memory operands, and the padding bytes as `xorAt`s of
a lane.
-/


namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64
open VG.Impl.SlhDsa.X86_64.Thash4
open VG.Proof.Sha3 (byteOf xorAt byteOf_xorAt xorByte byteOf_xorByte ext_bytes)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `cmp d, imm32`: ZF is `d = imm` (sign-extended). -/
theorem wp_cmpi {d : Reg} {v : BitVec 32}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  Proof.Sha3.X86_64.WP.cons rfl (k _ rfl rfl rfl rfl rfl)

/-- `vzeroupper`. -/
theorem wp_vzu
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.vop .vzeroupper :: is)) s Q :=
  Proof.Sha3.X86_64.WP.cons rfl (k _ (VOp.exec_gpr _ _) (VOp.exec_mem _ _) (VOp.exec_rd _ _) (VOp.exec_wr _ _))

end

/-! ## Addresses -/

theorem ea_at' (s : State) (b : Reg) (d : Nat) :
    s.ea (VG.Impl.Sha3.X86_64.at_ b d) = s.gpr b + BitVec.ofNat 64 d :=
  Proof.Sha3.X86_64.ea_at s b d

theorem ea_base (s : State) (b : Reg) : s.ea { base := b } = s.gpr b := by
  simp [State.ea]

theorem ea_rowLane (s : State) (k : Nat) :
    s.ea (rowLane k) = s.gpr .r8 + s.gpr .rcx + BitVec.ofNat 64 (8 * k) := by
  simp only [State.ea, rowLane, BitVec.mul_one]
  rw [show (8 * (k : Int)) = ((8 * k : Nat) : Int) by omega, Proof.Sha3.X86_64.ofInt_natCast]

theorem ea_msgAt (s : State) (k : Nat) : s.ea (msgAt k) = s.gpr (lanePtr k) + s.gpr .rsi := by
  simp [State.ea, msgAt]

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega_using [h]
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using [h]

theorem sx8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
theorem sx32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
theorem sx544 : BitVec.signExtend 64 (544 : BitVec 32) = 544 := by decide
theorem sx1f : BitVec.signExtend 64 (0x1f : BitVec 32) = 0x1f := by decide

theorem add_ofNat (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## The padding as `xorAt`s -/

/-- XORing `[b, 0, …, 0]` at `j` is XORing `b` into byte `j`. -/
theorem xorAt_lo (A : Spec.Sha3.State) (j : Nat) (b : Byte) :
    xorAt A j [b, 0, 0, 0, 0, 0, 0, 0] = xorByte A j b :=
  ext_bytes fun i hi => by
    rw [byteOf_xorAt _ _ _ hi, byteOf_xorByte _ _ _ hi]
    by_cases e : i = j
    · subst e; simp
    · rw [ite_eq_right e]
      split
      · rename_i h
        obtain ⟨d, hd, rfl⟩ : ∃ d, d < 8 ∧ i = j + d := ⟨i - j, by simp at h; omega_using [h], by omega_using [h]⟩
        rcases (by omega_using [hd, e] : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      · rfl

/-- XORing `[0, …, 0, b]` at `j` is XORing `b` into byte `j + 7`. -/
theorem xorAt_hi (A : Spec.Sha3.State) (j : Nat) (b : Byte) :
    xorAt A j [0, 0, 0, 0, 0, 0, 0, b] = xorByte A (j + 7) b :=
  ext_bytes fun i hi => by
    rw [byteOf_xorAt _ _ _ hi, byteOf_xorByte _ _ _ hi]
    by_cases e : i = j + 7
    · subst e; simp
    · rw [ite_eq_right e]
      split
      · rename_i h
        obtain ⟨d, hd, rfl⟩ : ∃ d, d < 8 ∧ i = j + d := ⟨i - j, by simp at h; omega_using [h], by omega_using [h]⟩
        rcases (by omega_using [hd, e] : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      · rfl

theorem bytes_0x1f : ∀ d < 8, (0x1f : BitVec 64).extractLsb' (8 * d) 8 =
    [(0x1f : Byte), 0, 0, 0, 0, 0, 0, 0].getD d 0 := by decide

theorem bytes_0x80 : ∀ d < 8, (0x8000000000000000 : BitVec 64).extractLsb' (8 * d) 8 =
    [(0 : Byte), 0, 0, 0, 0, 0, 0, 0x80].getD d 0 := by decide

end VG.Proof.SlhDsa.X86_64


namespace VG.Proof.SlhDsa.X86_64.Thash4Avx

open VG VG.X86_64
open VG.Impl.SlhDsa.X86_64.Thash4
open VG.Impl.Sha3.X86_64.X4 (vb st permute4)
open VG.Proof.Sha3.X86_64.X4 (Lanes4 la KState Pre4 permute4_ok q4 VUpd wp_vxor wp_vst q4_ymm)
open VG.Proof.Sha3 (byteOf xorAt xorByte Rep rep_nil rep_append absorb_pad)
open VG.Spec.Sha3 (bytesAt keccakF RC)
open VG.Proof.SlhDsa (finalState)
open VG.Proof.SlhDsa.X86_64 (Thash4Pre msg outAt thash4Changes RcTable workLen ba lanes4_of_bytes
  byte_of_lanes4 lanes4_xorLane ea_at' ea_base ea_rowLane sx_ofNat add_ofNat)

/-! ## Registers -/

/-- A callee-saved register is none of the registers the code writes. -/
theorem cs_ne {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .rdi ∧
    r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A postcondition of code that never writes `r` keeps `r`. -/
theorem wp_gpr_keep {c : Prog isa} {r : Reg} (hc : ∀ i ∈ instrs c, Taint.clobbers i r = false) {s : State}
    {Q : State → Prop} (h : WP isa c s Q) : WP isa c s fun s' => Q s' ∧ s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.gpr hc he⟩

/-! ## Regions -/

/-- A region that is the first `k` bytes of another's, or one at an offset
within it. -/
theorem sub_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Region.Sub ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := Offset.sub_base p h

theorem sub_pre (p : Addr) {n k : Nat} (h : n ≤ k) : Region.Sub ⟨p, n⟩ ⟨p, k⟩ :=
  Region.sub_prefix h

/-- A word framed. -/
theorem readW_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {a : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, 8⟩ r) : m'.readW a 64 = m.readW a 64 := by
  simp only [Mem.readW]
  rw [hf.read (r := ⟨a, 8⟩) (by simp [Region.Contains]) hd (by decide)]

/-- Memory that frames `rs` keeps the four states at `p` if none of `rs`
meets them. -/
theorem lanes4_frame {m m' : Mem} {p : Addr} {A : Nat → KState} (h : Lanes4 m p A) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 800⟩ r) : Lanes4 m' p A := fun i hi k hk => by
  rw [← h i hi k hk]
  exact readW_frame hf fun r hr => (hd r hr).sub_left (sub_off p (by omega_using [hi, hk]))

/-- `[p + d, p + d + n)` lies above `[p, p + k)`. -/
theorem disj_base (p : Addr) {d n k : Nat} (h : k ≤ d) (hd : d + n ≤ 2 ^ 64) :
    Region.Disjoint ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := by
  have := Offset.disjoint p (d := d) (n := n) (e := 0) (k := k) (Or.inr (by omega_using [h])) hd
    (by omega_using [h, hd])
  simpa using this

theorem lanes4_congr {m : Mem} {p : Addr} {A B : Nat → KState} (h : Lanes4 m p A) (e : ∀ k < 4, A k = B k) :
    Lanes4 m p B := fun i hi k hk => by rw [← e k hk]; exact h i hi k hk

/-! ## The entry state -/

section
variable (σ : State)

abbrev inp : Addr := σ.gpr .rdi
abbrev str : Nat := (σ.gpr .rsi).toNat
abbrev L : Nat := (σ.gpr .rdx).toNat
abbrev W : Addr := σ.gpr .r8
abbrev laneP (k : Nat) : Addr := inp σ + BitVec.ofNat 64 (k * str σ)
abbrev lanesR : Region := ⟨inp σ, 4 * str σ⟩
abbrev workR : Region := ⟨W σ, workLen⟩
/-- What the code changes in `work` and on the stack: the states and the
slots, and the `stk` bytes below the stack pointer. -/
abbrev wf (stk : Nat) : List Region :=
  [⟨W σ, 1600⟩, ⟨W σ + BitVec.ofNat 64 2368, workLen - 2368⟩, below (σ.gpr .rsp) stk]
/-- The number of words of each message. -/
abbrev nw : Nat := L σ / 8

end

variable {n stk : Nat} {σ : State}

theorem wr_work (hp : Thash4Pre n stk σ) {s : State} (hw : s.wr = σ.wr) {d k : Nat} (h : d + k ≤ workLen) :
    InRegions s.wr (W σ + BitVec.ofNat 64 d) k :=
  ⟨workR σ, by rw [hw, hp.wr]; simp, Offset.contains_base _ h (by simp [workLen] at h ⊢; omega_using [h])⟩

theorem rw_work (hp : Thash4Pre n stk σ) {s : State} (hw : s.wr = σ.wr) {d k : Nat} (h : d + k ≤ workLen) :
    InRegions (s.rd ++ s.wr) (W σ + BitVec.ofNat 64 d) k :=
  let ⟨r, hr, hc⟩ := wr_work hp hw h; ⟨r, List.mem_append_right _ hr, hc⟩

theorem str_lt (hp : Thash4Pre n stk σ) : 4 * str σ ≤ 2 ^ 64 := by
  have h1 := hp.lanes_fit; have h2 := hp.len_pos; have h3 := hp.len_le
  show 4 * (σ.gpr .rsi).toNat ≤ 2 ^ 64
  omega_using [h1, h2, h3]

theorem kstr_le {k : Nat} (hk : k < 4) : k * str σ + str σ ≤ 4 * str σ := by
  have := Nat.mul_le_mul_right (str σ) (show k + 1 ≤ 4 by omega_using [hk])
  rw [Nat.succ_mul] at this; exact this

theorem laneP_off (k d : Nat) : laneP σ k + BitVec.ofNat 64 d = inp σ + BitVec.ofNat 64 (k * str σ + d) :=
  add_ofNat _ _ _

theorem laneP_zero : laneP σ 0 = σ.gpr .rdi := by simp [laneP, inp]

theorem laneP_succ (k : Nat) : laneP σ (k + 1) = laneP σ k + σ.gpr .rsi := by
  simp only [laneP, inp, str]
  rw [Nat.succ_mul, ← add_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem rd_lane (hp : Thash4Pre n stk σ) {s : State} (hw : s.wr = σ.wr) {k d : Nat} (hk : k < 4)
    (hd : d + 8 ≤ str σ) : InRegions (s.rd ++ s.wr) (laneP σ k + BitVec.ofNat 64 d) 8 := by
  have := str_lt hp
  refine ⟨lanesR σ, List.mem_append_right _ (by rw [hw, hp.wr]; simp), ?_⟩
  have h2 := kstr_le (σ := σ) hk
  rw [laneP_off]
  exact Offset.contains_base _ (by omega_using [hd, h2]) (by omega_using [hd, h2, this])

/-- The lanes do not meet the regions the loop changes. -/
theorem lanes_wf (hp : Thash4Pre n stk σ) : ∀ r ∈ wf σ stk, Region.Disjoint (lanesR σ) r := by
  intro r hr
  simp only [wf, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.lanes_work.sub_right (sub_pre _ (by decide))
  · exact hp.lanes_work.sub_right (sub_off _ (by decide))
  · exact hp.stk_lanes.symm

/-- A byte of the lanes, framed by `wf`. -/
theorem lane_byte {m : Mem} (hp : Thash4Pre n stk σ) (hf : Frame (wf σ stk) σ.mem m) {a : Addr}
    (ha : (lanesR σ).Contains a 1) : m a = σ.mem a :=
  hf a fun r hr hc => lanes_wf hp r hr a ha hc

/-- Byte `j` of message `k`. -/
theorem msg_byte (k : Nat) {j : Nat} (hj : j < L σ) :
    (msg σ k).getD j 0 = σ.mem (laneP σ k + BitVec.ofNat 64 j) := by
  simp [msg, bytesAt, hj]

theorem length_msg (k : Nat) : (msg σ k).length = L σ := by simp [msg, bytesAt]

theorem len_eq (hp : Thash4Pre n stk σ) : L σ = 8 * nw σ := by
  have h := hp.len_mod
  show (σ.gpr .rdx).toNat = 8 * ((σ.gpr .rdx).toNat / 8)
  omega_using [h]

/-- The table of round constants, as `permute4` reads it. -/
theorem rc_of {m : Mem} (hp : Thash4Pre n stk σ) (hf : Frame (wf σ stk) σ.mem m) :
    ∀ r < 24, ∀ k < 4, m.readW (la (W σ + BitVec.ofNat 64 1600) r k) 64 = RC r := by
  intro r hr k hk
  have e : la (W σ + BitVec.ofNat 64 1600) r k = W σ + BitVec.ofNat 64 (1600 + 32 * r + 8 * k) := by
    rw [la, add_ofNat, Nat.add_assoc]
  have hrc : σ.mem.readW (W σ + BitVec.ofNat 64 (1600 + 32 * r + 8 * k)) 64 = RC r := hp.rc r hr k hk
  rw [e, ← hrc]
  refine readW_frame hf fun x hx => ?_
  simp only [wf, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact disj_base _ (by omega_using []) (by omega_using [hr, hk])
  · exact Offset.disjoint _ (Or.inl (by omega_using [hr, hk])) (by omega_using [hr, hk]) (by simp [workLen])
  · exact hp.stk_work.symm.sub_left (sub_off _ (by simp [workLen]; omega_using [hr, hk]))

/-! ## The invariant of the loop -/

/-- After `w` words of each message: the lanes' addresses, the position, the
bytes left and the row, the states those of the first `8 w` bytes of each,
and the memory changed only in the states and the slots. -/
structure Inv (σ : State) (stk w : Nat) (s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  r8 : s.gpr .r8 = W σ
  ptr : ∀ k < 4, s.gpr (lanePtr k) = laneP σ k
  pos : s.gpr .rsi = BitVec.ofNat 64 (8 * w)
  dx : s.gpr .rdx = BitVec.ofNat 64 (L σ - 8 * w)
  cx : s.gpr .rcx = BitVec.ofNat 64 (32 * (w % 17))
  lanes : Lanes4 s.mem (W σ) (fun k => Rep 136 ((msg σ k).take (8 * w)))
  frame : Frame (wf σ stk) σ.mem s.mem
  sp : s.gpr .rsp = σ.gpr .rsp
  cs : ∀ r ∈ calleeSaved, s.gpr r = σ.gpr r

/-! ## The prologue -/

theorem ymm_zero {s : State} {r : XReg} (h : ∀ k < 4, q4 s r k = 0) : s.ymm r = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (·.getLsbD (i % 64)) (show (s.ymm r).extractLsb' (64 * (i / 64)) 64 = 0 by
    rw [q4_ymm _ _ (by omega_using [hi]), h _ (by omega_using [hi])])
  simp only [BitVec.getLsbD_extractLsb', show i % 64 < 64 by omega_using [], decide_true, Bool.true_and] at e
  rw [show 64 * (i / 64) + i % 64 = i by omega_using []] at e
  simpa using e

theorem byteOf_zero (q : Nat) : byteOf Spec.Sha3.zero q = 0 := by
  have : (Spec.Sha3.zero)[q / 8]! = 0 := by
    by_cases h : q / 8 < 25
    · rw [getElem!_pos Spec.Sha3.zero (q / 8) h]; simp [Spec.Sha3.zero]
    · rw [getElem!_neg Spec.Sha3.zero (q / 8) h]; rfl
  rw [byteOf, this]; simp

/-- The 25 rows of the states zeroed. -/
theorem zeros_ok (hp : Thash4Pre n stk σ) : ∀ j ≤ 25, ∀ t : State, t.gpr .r8 = W σ → t.wr = σ.wr →
    (∀ k < 4, q4 t .xmm0 k = 0) →
    WP isa (.block ((List.range j).map fun i => st .r8 i .xmm0)) t (fun t' => t'.gpr = t.gpr ∧
      t'.rd = t.rd ∧ t'.wr = t.wr ∧ (∀ k < 4, q4 t' .xmm0 k = 0) ∧
      (∀ q < 32 * j, t'.mem (W σ + BitVec.ofNat 64 q) = 0) ∧ Frame [⟨W σ, 800⟩] t.mem t'.mem) := by
  intro j
  induction j with
  | zero => intro _ t _ _ h0; exact WP.block_nil ⟨rfl, rfl, rfl, h0, fun q hq => absurd hq (by omega_using []), Frame.refl _ _⟩
  | succ j ih =>
    intro hj t h8 hw h0
    rw [List.range_succ, List.map_append]
    refine WP.block_append (WP.mono (ih (by omega_using [hj]) t h8 hw h0) fun t₁ ⟨g₁, r₁, w₁, z₁, b₁, f₁⟩ => ?_)
    refine Proof.Sha3.X86_64.X4.wp_vst (a := W σ + BitVec.ofNat 64 (32 * j))
      (by rw [ea_at', g₁, h8])
      (wr_work hp (by rw [w₁, hw]) (by simp [workLen]; omega_using [hj])) fun t₂ g₂ q₂ m₂ r₂ w₂ => WP.block_nil ?_
    have hy : t₁.ymm .xmm0 = 0 := ymm_zero z₁
    refine ⟨by rw [g₂, g₁], by rw [r₂, r₁], by rw [w₂, w₁], fun k hk => by rw [q₂]; exact z₁ k hk, fun q hq => ?_, ?_⟩
    · rw [m₂, hy]
      by_cases c : q < 32 * j
      · rw [writeW_byte_off _ _ _ _ (by
            rw [Offset.sub_toNat' _ (by omega_using [hj]) (by omega_using [hq, hj])]; split <;> rename_i hs <;> omega_using [c, hs, hq, hj]),
          b₁ q c]
      · rw [show W σ + BitVec.ofNat 64 q = W σ + BitVec.ofNat 64 (32 * j) + BitVec.ofNat 64 (q - 32 * j) by
            rw [add_ofNat, show 32 * j + (q - 32 * j) = q by omega_using [c]],
          writeW_byte _ _ _ (by omega_using [hq, c]) (by decide)]
        simp
    · rw [m₂]
      exact f₁.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))

/-- What the proof needs of the code `zero` that zeroes the states: it
keeps every register but `rax`, and zeroes the 800 bytes of the states and
nothing else. -/
def ZeroOk (zero : List Instr) (σ : State) : Prop :=
  WP isa (.block zero) σ fun t => (∀ r, r ≠ .rax → t.gpr r = σ.gpr r) ∧ t.rd = σ.rd ∧ t.wr = σ.wr ∧
    (∀ q < 800, t.mem (W σ + BitVec.ofNat 64 q) = 0) ∧ Frame [⟨W σ, 800⟩] σ.mem t.mem

theorem zeroOk_V (hp : Thash4Pre n stk σ) : ZeroOk zeroV σ :=
  Proof.Sha3.X86_64.X4.wp_vxor fun s₃ u₃ =>
    WP.mono (zeros_ok hp 25 (by decide) s₃ (by rw [u₃.gpr]) (by rw [u₃.wr])
      fun k hk => by rw [u₃.val k hk]; exact BitVec.xor_self) fun s₄ ⟨g₄, r₄, w₄, _, b₄, f₄⟩ =>
      ⟨fun r _ => by rw [g₄, u₃.gpr], by rw [r₄, u₃.rd], by rw [w₄, u₃.wr], b₄, by rw [← u₃.mem]; exact f₄⟩

theorem pro_ok {zero : List Instr} (hz : ZeroOk zero σ) :
    WP isa (.block (pro zero)) σ (Inv σ stk 0) := by
  refine WP.block_append (WP.mono hz fun s₄ ⟨g₄, r₄, w₄, b₄, f₄⟩ => ?_)
  refine Steps.wp_mov fun s₅ u₅ => Steps.wp_add fun s₆ u₆ => Steps.wp_mov fun s₇ u₇ => Steps.wp_add fun s₈ u₈ =>
    Steps.wp_mov fun s₉ u₉ => Steps.wp_add fun s₁₀ u₁₀ => Steps.wp_mov32i fun s₁₁ u₁₁ =>
    Steps.wp_mov32i fun s₁₂ u₁₂ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rax → s₄.gpr r = σ.gpr r := g₄
  have hmem : s₁₂.mem = s₄.mem := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]
  refine ⟨by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, r₄],
    by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, w₄], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r hr => ?_⟩
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), g _ (by decide)]
  · intro k hk
    have h9 : s₁₂.gpr .r9 = laneP σ 1 := by
      rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
        u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₅.other _ (by decide), g _ (by decide), g _ (by decide),
        laneP_succ, laneP_zero]
    have h10 : s₁₂.gpr .r10 = laneP σ 2 := by
      rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
        u₈.gpr, u₇.gpr, u₇.other _ (by decide), u₆.gpr, u₆.other _ (by decide), u₅.gpr, u₅.other _ (by decide), g _ (by decide), g _ (by decide),
        laneP_succ, laneP_succ, laneP_zero]
    have h11 : s₁₂.gpr .r11 = laneP σ 3 := by
      rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.gpr, u₉.other _ (by decide), u₈.gpr,
        u₈.other _ (by decide), u₇.gpr, u₇.other _ (by decide), u₆.gpr, u₆.other _ (by decide), u₅.gpr,
        u₅.other _ (by decide), g _ (by decide), g _ (by decide), laneP_succ, laneP_succ, laneP_succ, laneP_zero]
    have h0 : s₁₂.gpr .rdi = laneP σ 0 := by
      rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
        u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), g _ (by decide), laneP_zero]
    rcases Proof.Sha3.X86_64.X4.cases4 hk with rfl | rfl | rfl | rfl
    · exact h0
    · exact h9
    · exact h10
    · exact h11
  · rw [u₁₂.other _ (by decide), u₁₁.gpr]; rfl
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), g _ (by decide)]
    simp
  · rw [u₁₂.gpr]; rfl
  · rw [hmem]
    refine lanes4_of_bytes fun k hk q hq => ?_
    rw [b₄ _ (by have := ba_off_lt hk hq; omega_using [this])]
    simp [rep_nil, byteOf_zero]
  · rw [hmem]
    exact f₄.sub fun r hr => ⟨_, List.mem_cons_self .., by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_pre _ (by decide)⟩
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), g _ (by decide)]
  · obtain ⟨hax, hcx, -, hsi, -, -, h9, h10, h11⟩ := cs_ne hr
    rw [u₁₂.other _ hcx, u₁₁.other _ hsi, u₁₀.other _ h11, u₉.other _ h11, u₈.other _ h10, u₇.other _ h10,
      u₆.other _ h9, u₅.other _ h9, g _ hax]

/-! ## A row -/

/-- The 8 bytes of message `k` after its first `8 w`. -/
abbrev chunk8 (σ : State) (k w : Nat) : List Byte := ((msg σ k).drop (8 * w)).take 8

theorem chunk8_getD (k w : Nat) {d : Nat} (hd : d < 8) :
    (chunk8 σ k w).getD d 0 = (msg σ k).getD (8 * w + d) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hd]

theorem length_chunk8 (k : Nat) {w : Nat} (hw : 8 * w + 8 ≤ L σ) : (chunk8 σ k w).length = 8 := by
  simp [length_msg]; omega_using [hw]

/-- The local frame of a step: the states and the slots of the pointer and
the bytes left. -/
abbrev wl (σ : State) (stk : Nat) : List Region :=
  [⟨W σ, 1600⟩, ⟨W σ + BitVec.ofNat 64 2368, 24⟩, below (σ.gpr .rsp) stk]

theorem wl_wf {m m' : Mem} (h : Frame (wl σ stk) m m') : Frame (wf σ stk) m m' :=
  h.sub fun r hr => by
    simp only [wl, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_pre _ (by simp [workLen])⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩

/-- One lane of a row: the next word of message `k` XORed into lane `k` of
row `r`. -/
theorem lane_ok (hp : Thash4Pre n stk σ) {w : Nat} (hw8 : 8 * w + 8 ≤ L σ) {k : Nat} (hk : k < 4) {r : Nat}
    (hr : r < 17) {A : Nat → KState} {t : State} (hwr : t.wr = σ.wr) (h8 : t.gpr .r8 = W σ)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 (32 * r)) (hpk : t.gpr (lanePtr k) = laneP σ k)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 (8 * w)) (hl : Lanes4 t.mem (W σ) A) (hf : Frame (wf σ stk) σ.mem t.mem) :
    WP isa (.block (xorLane k)) t (fun t' => (∀ g, g ≠ .rax → t'.gpr g = t.gpr g) ∧ t'.rd = t.rd ∧
      t'.wr = t.wr ∧ Lanes4 t'.mem (W σ) (fun k' => if k' = k then xorAt (A k') (8 * r) (chunk8 σ k w) else A k') ∧
      Frame (wf σ stk) σ.mem t'.mem ∧ Frame (wl σ stk) t.mem t'.mem) := by
  have hle : L σ ≤ str σ := hp.len_le
  have hla : la (W σ) r k = W σ + BitVec.ofNat 64 (32 * r + 8 * k) := rfl
  refine Proof.Sha3.X86_64.wp_movm (a := laneP σ k + BitVec.ofNat 64 (8 * w)) (by rw [Proof.SlhDsa.X86_64.ea_msgAt, hpk, hsi])
    (rd_lane hp hwr hk (by omega_using [hw8, hle])) fun t₁ u₁ => ?_
  refine Proof.Sha3.X86_64.wp_xorm (a := la (W σ) r k) (by rw [ea_rowLane, u₁.other _ (by decide),
    u₁.other _ (by decide), h8, hcx, hla, add_ofNat])
    (by rw [hla, u₁.rd, u₁.wr]; exact rw_work hp hwr (by simp [workLen]; omega_using [hr, hk])) fun t₂ u₂ => ?_
  refine Proof.Sha3.X86_64.wp_store (a := la (W σ) r k) (by rw [ea_rowLane, u₂.other _ (by decide),
    u₁.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h8, hcx, hla, add_ofNat])
    (by rw [hla, u₂.wr, u₁.wr]; exact wr_work hp hwr (by simp [workLen]; omega_using [hr, hk]))
    fun t₃ g₃ m₃ r₃ w₃ => WP.block_nil ?_
  have hm₂ : t₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  have hcont : (⟨W σ, 1600⟩ : Region).Contains (la (W σ) r k) (64 / 8) := by
    rw [hla]; exact Offset.contains_base _ (by omega_using [hr, hk]) (by omega_using [hr, hk])
  refine ⟨fun g hg => by rw [g₃, u₂.other _ hg, u₁.other _ hg], by rw [r₃, u₂.rd, u₁.rd],
    by rw [w₃, u₂.wr, u₁.wr], ?_, ?_, ?_⟩
  · rw [m₃, hm₂, u₂.gpr, u₁.gpr, u₁.mem]
    refine lanes4_xorLane hl (by omega_using [hr]) hk (length_chunk8 k hw8) fun d hd => ?_
    rw [BitVec.extractLsb'_xor, byte_readW _ _ (by omega_using [hd]), byte_readW _ _ (by omega_using [hd]),
      BitVec.xor_comm, chunk8_getD _ _ hd, msg_byte _ (by omega_using [hd, hw8]), add_ofNat]
    congr 1
    have h2 := kstr_le (σ := σ) hk
    have := str_lt hp
    rw [add_ofNat]
    refine lane_byte hp hf ?_
    rw [laneP_off]
    exact Offset.contains_base _ (by omega_using [hd, hw8, hle, h2]) (by omega_using [hd, hw8, hle, h2, this])
  · rw [m₃, hm₂]; exact hf.writeW (List.mem_cons_self ..) _ hcont
  · rw [m₃, hm₂]; exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ hcont

/-- After a row of the loop from `Inv σ w s`. -/
structure RowPost (σ : State) (stk w : Nat) (s t : State) : Prop where
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  r8 : t.gpr .r8 = W σ
  ptr : ∀ k < 4, t.gpr (lanePtr k) = laneP σ k
  pos : t.gpr .rsi = BitVec.ofNat 64 (8 * (w + 1))
  dx : t.gpr .rdx = BitVec.ofNat 64 (L σ - 8 * (w + 1))
  cx : t.gpr .rcx = BitVec.ofNat 64 (32 * (w % 17) + 32)
  zf : t.zf = some (decide (w % 17 = 16))
  lanes : Lanes4 t.mem (W σ) (fun k => xorAt (Rep 136 ((msg σ k).take (8 * w))) (8 * (w % 17)) (chunk8 σ k w))
  frame : Frame (wf σ stk) σ.mem t.mem
  loc : Frame (wl σ stk) s.mem t.mem
  sp : t.gpr .rsp = σ.gpr .rsp
  cs : ∀ r ∈ calleeSaved, t.gpr r = σ.gpr r

theorem row_eq : row = xorLane 0 ++ (xorLane 1 ++ (xorLane 2 ++ (xorLane 3 ++
    ([.alu .add .rsi (.imm 8), .alu .add .rcx (.imm 32), .alu .sub .rdx (.imm 8), .alu .cmp .rcx (.imm 544)] :
      List Instr)))) := rfl

theorem row_ok (hp : Thash4Pre n stk σ) {w : Nat} (hw : w + 1 ≤ nw σ) {s : State} (hI : Inv σ stk w s) :
    WP isa (.block row) s (RowPost σ stk w s) := by
  have hL := len_eq hp
  have hw8 : 8 * w + 8 ≤ L σ := by omega_using [hL, hw]
  have hr : w % 17 < 17 := Nat.mod_lt _ (by decide)
  rw [row_eq]
  refine WP.block_append (WP.mono (lane_ok hp hw8 (k := 0) (by decide) hr hI.wr hI.r8 hI.cx (hI.ptr 0 (by decide))
    hI.pos hI.lanes hI.frame) fun t₀ ⟨g₀, r₀, w₀, l₀, f₀, c₀⟩ => ?_)
  refine WP.block_append (WP.mono (lane_ok hp hw8 (k := 1) (by decide) hr (by rw [w₀, hI.wr])
    (by rw [g₀ _ (by decide), hI.r8]) (by rw [g₀ _ (by decide), hI.cx])
    (by rw [g₀ _ (by decide)]; exact hI.ptr 1 (by decide)) (by rw [g₀ _ (by decide), hI.pos]) l₀ f₀)
    fun t₁ ⟨g₁, r₁, w₁, l₁, f₁, c₁⟩ => ?_)
  refine WP.block_append (WP.mono (lane_ok hp hw8 (k := 2) (by decide) hr (by rw [w₁, w₀, hI.wr])
    (by rw [g₁ _ (by decide), g₀ _ (by decide), hI.r8]) (by rw [g₁ _ (by decide), g₀ _ (by decide), hI.cx])
    (by rw [g₁ _ (by decide), g₀ _ (by decide)]; exact hI.ptr 2 (by decide))
    (by rw [g₁ _ (by decide), g₀ _ (by decide), hI.pos]) l₁ f₁)
    fun t₂ ⟨g₂, r₂, w₂, l₂, f₂, c₂⟩ => ?_)
  refine WP.block_append (WP.mono (lane_ok hp hw8 (k := 3) (by decide) hr (by rw [w₂, w₁, w₀, hI.wr])
    (by rw [g₂ _ (by decide), g₁ _ (by decide), g₀ _ (by decide), hI.r8])
    (by rw [g₂ _ (by decide), g₁ _ (by decide), g₀ _ (by decide), hI.cx])
    (by rw [g₂ _ (by decide), g₁ _ (by decide), g₀ _ (by decide)]; exact hI.ptr 3 (by decide))
    (by rw [g₂ _ (by decide), g₁ _ (by decide), g₀ _ (by decide), hI.pos]) l₂ f₂)
    fun t₃ ⟨g₃, r₃, w₃, l₃, f₃, c₃⟩ => ?_)
  have g : ∀ r, r ≠ .rax → t₃.gpr r = s.gpr r := fun r h => by rw [g₃ _ h, g₂ _ h, g₁ _ h, g₀ _ h]
  refine Steps.wp_addi fun u₄ v₄ => Steps.wp_addi fun u₅ v₅ => Proof.Sha3.X86_64.wp_subi fun u₆ v₆ _ =>
    Proof.SlhDsa.X86_64.wp_cmpi fun u₇ g₇ m₇ r₇ w₇ z₇ => WP.block_nil ?_
  have hcx : u₆.gpr .rcx = BitVec.ofNat 64 (32 * (w % 17) + 32) := by
    rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), g _ (by decide), hI.cx, Proof.SlhDsa.X86_64.sx32,
      show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]
  have hm : u₇.mem = t₃.mem := by rw [m₇, v₆.mem, v₅.mem, v₄.mem]
  refine ⟨by rw [r₇, v₆.rd, v₅.rd, v₄.rd, r₃, r₂, r₁, r₀, hI.rd],
    by rw [w₇, v₆.wr, v₅.wr, v₄.wr, w₃, w₂, w₁, w₀, hI.wr], ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r hr => ?_⟩
  · rw [g₇, v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), g _ (by decide), hI.r8]
  · have hne : lanePtr k ≠ .rsi ∧ lanePtr k ≠ .rcx ∧ lanePtr k ≠ .rdx ∧ lanePtr k ≠ .rax := by
      rcases Proof.Sha3.X86_64.X4.cases4 hk with rfl | rfl | rfl | rfl <;> decide
    rw [g₇, v₆.other _ hne.2.2.1, v₅.other _ hne.2.1, v₄.other _ hne.1, g _ hne.2.2.2, hI.ptr k hk]
  · rw [g₇, v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, g _ (by decide), hI.pos,
      Proof.SlhDsa.X86_64.sx8, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add, Nat.mul_succ]
  · rw [g₇, v₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), g _ (by decide), hI.dx, Proof.SlhDsa.X86_64.sx8,
      show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, Proof.Sha3.sub_ofNat (by omega_using [hw8])]
    congr 1
  · rw [g₇, hcx]
  · rw [z₇, hcx, Proof.SlhDsa.X86_64.sx544, show (544 : BitVec 64) = BitVec.ofNat 64 544 from rfl,
      Proof.Sha3.sub_beq (by omega_using [hr]) (by decide)]
    congr 1; simp only [decide_eq_decide]; omega_using [hr]
  · rw [hm]
    refine lanes4_congr l₃ fun k hk => ?_
    rcases Proof.Sha3.X86_64.X4.cases4 hk with rfl | rfl | rfl | rfl <;> simp
  · rw [hm]; exact f₃
  · rw [hm]; exact ((c₀.trans c₁).trans c₂).trans c₃
  · rw [g₇, v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), g _ (by decide), hI.sp]
  · obtain ⟨hax, hcx, hdx, hsi, -⟩ := cs_ne hr
    rw [g₇, v₆.other _ hdx, v₅.other _ hcx, v₄.other _ hsi, g _ hax, hI.cs r hr]

/-! ## The permutation in the loop -/

theorem permArgs_ok {t : State} {Q : State → Prop}
    (k : ∀ u, u.gpr .rdi = t.gpr .r8 → u.gpr .rsi = t.gpr .r8 + BitVec.ofNat 64 800 →
      u.gpr .rdx = t.gpr .r8 + BitVec.ofNat 64 1600 → u.gpr .rcx = t.gpr .r8 + BitVec.ofNat 64 2368 →
      (∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → u.gpr g = t.gpr g) → u.mem = t.mem → u.rd = t.rd →
      u.wr = t.wr → Q u) :
    WP isa (.block permArgs) t Q := by
  refine Steps.wp_mov fun u₁ v₁ => Steps.wp_mov fun u₂ v₂ => Steps.wp_addi fun u₃ v₃ => Steps.wp_mov fun u₄ v₄ =>
    Steps.wp_addi fun u₅ v₅ => Steps.wp_mov fun u₆ v₆ => Steps.wp_addi fun u₇ v₇ => WP.block_nil ?_
  refine k u₇ ?_ ?_ ?_ ?_ (fun g h1 h2 h3 h4 => ?_) ?_ ?_ ?_
  · rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr]
  · rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.gpr, v₂.gpr, v₁.other _ (by decide), sx_ofNat (by decide)]; rfl
  · rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.gpr, v₄.gpr,
      v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), sx_ofNat (by decide)]; rfl
  · rw [v₇.gpr, v₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), sx_ofNat (by decide)]; rfl
  · rw [v₇.other _ h4, v₆.other _ h4, v₅.other _ h3, v₄.other _ h3, v₃.other _ h2, v₂.other _ h2, v₁.other _ h1]
  · rw [v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  · rw [v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd]
  · rw [v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr]

/-- What the proof needs of the permutation `perm`, from the entry state `σ`
with `stk` bytes of stack: from a state with the regions and the stack
pointer of `σ`, its arguments (the states, the second buffer, the table and
its end) and the table of round constants, it applies Keccak-f[1600] to each
of the four states, changes memory only in the states and the second buffer
(`work[0..1600)`) and the `stk` bytes below the stack pointer, and keeps the
regions, `r8`–`r11` and the callee-saved registers. -/
def PermOk (perm : Prog isa) (σ : State) (stk : Nat) : Prop :=
  ∀ (u : State) (X : Nat → KState), u.rd = σ.rd → u.wr = σ.wr → u.gpr .rsp = σ.gpr .rsp → u.gpr .r8 = W σ →
    u.gpr .rdi = W σ → u.gpr .rsi = W σ + BitVec.ofNat 64 800 → u.gpr .rdx = W σ + BitVec.ofNat 64 1600 →
    u.gpr .rcx = W σ + BitVec.ofNat 64 2368 → Lanes4 u.mem (W σ) X →
    (∀ r < 24, ∀ k < 4, u.mem.readW (la (W σ + BitVec.ofNat 64 1600) r k) 64 = RC r) →
    WP isa perm u fun v => Lanes4 v.mem (W σ) (fun k => keccakF (X k)) ∧
      Frame [⟨W σ, 1600⟩, below (σ.gpr .rsp) stk] u.mem v.mem ∧ v.rd = u.rd ∧ v.wr = u.wr ∧
      (∀ g, g = .r8 ∨ g = .r9 ∨ g = .r10 ∨ g = .r11 ∨ g = .rsp → v.gpr g = u.gpr g) ∧
      ∀ g ∈ calleeSaved, v.gpr g = u.gpr g

/-- `permute4` meets it. -/
theorem permOk_V (hp : Thash4Pre n stk σ) (fast : Bool) : PermOk (permute4 fast) σ stk := by
  intro u X _ hwr _ _ hdi hsi hdx hcx hl hrc
  have hW := hp.work_fit
  have p4 : Pre4 u (W σ) (W σ + BitVec.ofNat 64 800) (W σ + BitVec.ofNat 64 1600) :=
    { src_in := fun i hi => wr_work hp hwr (by simp [workLen]; omega_using [hi])
      oth_in := fun i hi => by rw [add_ofNat]; exact wr_work hp hwr (by simp [workLen]; omega_using [hi])
      tbl_in := fun r hr => by rw [add_ofNat]; exact rw_work hp hwr (by simp [workLen]; omega_using [hr])
      src_oth := (disj_base _ (by decide) (by simp [workLen] at hW; omega_using [hW])).symm
      src_tbl := (disj_base _ (by decide) (by simp [workLen] at hW; omega_using [hW])).symm
      oth_tbl := Offset.disjoint _ (Or.inl (by decide)) (by decide) (by decide)
      rc := hrc }
  refine WP.mono (permute4_ok p4 hdi hsi hdx (by rw [hcx, add_ofNat]) hl fast) fun v ⟨l, f, r, w, _, g⟩ =>
    ⟨l, f.sub fun r hr => ?_, r, w, fun g' hg' => g g' (by rcases hg' with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hg' with rfl | rfl | rfl | rfl | rfl <;> decide),
    fun g' hg' => g g' (cs_ne hg').1 (cs_ne hg').2.2.1⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self .., sub_pre _ (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., sub_off _ (by decide)⟩

/-- `permuteKeep perm`: the permutation, with `rdi`, the bytes left and the
position kept across it, and the row back to 0. -/
theorem permKeep_ok (hp : Thash4Pre n stk σ) {perm : Prog isa} (hperm : PermOk perm σ stk) {t : State}
    (hrd : t.rd = σ.rd) (hwr : t.wr = σ.wr) (hsp : t.gpr .rsp = σ.gpr .rsp) (h8 : t.gpr .r8 = W σ)
    {X : Nat → KState} (hl : Lanes4 t.mem (W σ) X) (hf : Frame (wf σ stk) σ.mem t.mem) :
    WP isa (permuteKeep perm) t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.gpr .rdi = t.gpr .rdi ∧
      t'.gpr .rdx = t.gpr .rdx ∧ t'.gpr .rsi = t.gpr .rsi ∧ t'.gpr .rcx = 0 ∧
      (∀ g, g = .r8 ∨ g = .r9 ∨ g = .r10 ∨ g = .r11 ∨ g = .rsp → t'.gpr g = t.gpr g) ∧
      Lanes4 t'.mem (W σ) (fun k => keccakF (X k)) ∧ Frame (wf σ stk) σ.mem t'.mem ∧
      Frame (wl σ stk) t.mem t'.mem ∧ ∀ g ∈ calleeSaved, t'.gpr g = t.gpr g := by
  have hW := hp.work_fit
  unfold permuteKeep
  refine WP.seq (WP.block_append ?_)
  refine Proof.Sha3.X86_64.wp_store (a := W σ + BitVec.ofNat 64 oPtr) (by rw [ea_at', h8])
    (wr_work hp hwr (by decide)) fun s₁ g₁ m₁ r₁ w₁ => ?_
  refine Proof.Sha3.X86_64.wp_store (a := W σ + BitVec.ofNat 64 oLeft) (by rw [ea_at', g₁, h8])
    (wr_work hp (by rw [w₁, hwr]) (by decide)) fun s₂ g₂ m₂ r₂ w₂ => ?_
  refine Proof.Sha3.X86_64.wp_store (a := W σ + BitVec.ofNat 64 oPos) (by rw [ea_at', g₂, g₁, h8])
    (wr_work hp (by rw [w₂, w₁, hwr]) (by decide)) fun s₃ g₃ m₃ r₃ w₃ => WP.block_nil ?_
  have g₃' : ∀ r, s₃.gpr r = t.gpr r := fun r => by rw [g₃, g₂, g₁]
  have hcs : ∀ d, oPtr ≤ d → d + 8 ≤ oPtr + 24 →
      (⟨W σ + BitVec.ofNat 64 2368, 24⟩ : Region).Contains (W σ + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h1 h2 => Offset.contains _ (by simp [oPtr] at h1; omega_using [h1]) (by simp [oPtr] at h2; omega_using [h2])
      (by decide)
  have fs : Frame [⟨W σ + BitVec.ofNat 64 2368, 24⟩] t.mem s₃.mem := by
    rw [m₃, m₂, m₁]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hcs oPtr (Nat.le_refl _) (by decide))).writeW
      (List.mem_singleton_self _) _ (hcs oLeft (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (hcs oPos (by decide) (by decide))
  have fsl : Frame (wl σ stk) t.mem s₃.mem :=
    fs.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  have hsl : ∀ r ∈ [(⟨W σ + BitVec.ofNat 64 2368, 24⟩ : Region)], Region.Disjoint ⟨W σ, 800⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (Offset.disjoint (W σ) (d := 0) (n := 800) (e := 2368) (k := 24) (Or.inl (by decide)) (by decide)
      (by decide)) |> fun h => by simpa using h
  refine permArgs_ok fun u gdi gsi gdx gcx go um urd uwr => ?_
  have hu8 : u.gpr .r8 = W σ := by rw [go _ (by decide) (by decide) (by decide) (by decide), g₃', h8]
  have hf₃ : Frame (wf σ stk) σ.mem s₃.mem := hf.trans (wl_wf fsl)
  refine WP.seq (WP.mono (hperm u X (by rw [urd, r₃, r₂, r₁, hrd]) (by rw [uwr, w₃, w₂, w₁, hwr])
    (by rw [go _ (by decide) (by decide) (by decide) (by decide), g₃', hsp]) hu8
    (by rw [gdi, g₃', h8]) (by rw [gsi, g₃', h8]) (by rw [gdx, g₃', h8]) (by rw [gcx, g₃', h8])
    (by rw [um]; exact lanes4_frame hl fs hsl) (by rw [um]; exact rc_of hp hf₃))
    fun v ⟨lv, fv, rv, wv, gv, cv⟩ => ?_)
  have hv8 : v.gpr .r8 = W σ := by rw [gv _ (Or.inl rfl), hu8]
  have slot : ∀ d, oPtr ≤ d → d + 8 ≤ oPtr + 24 →
      v.mem.readW (W σ + BitVec.ofNat 64 d) 64 = s₃.mem.readW (W σ + BitVec.ofNat 64 d) 64 := fun d h1 h2 => by
    rw [← um]
    refine readW_frame fv fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_base _ (by simp [oPtr] at h1; omega_using [h1]) (by simp [oPtr] at h2; omega_using [h2, hW])
    · exact hp.stk_work.symm.sub_left (sub_off _ (by simp [oPtr, workLen] at h1 h2 ⊢; omega_using [h1, h2]))
  refine Steps.wp_movm (a := W σ + BitVec.ofNat 64 oPtr) (by rw [ea_at', hv8])
    (rw_work hp (by rw [wv, uwr, w₃, w₂, w₁, hwr]) (by decide)) fun x₁ y₁ =>
    Steps.wp_movm (a := W σ + BitVec.ofNat 64 oLeft) (by rw [ea_at', y₁.other _ (by decide), hv8])
    (rw_work hp (by rw [y₁.wr, wv, uwr, w₃, w₂, w₁, hwr]) (by decide)) fun x₂ y₂ =>
    Steps.wp_movm (a := W σ + BitVec.ofNat 64 oPos) (by rw [ea_at', y₂.other _ (by decide), y₁.other _ (by decide), hv8])
    (rw_work hp (by rw [y₂.wr, y₁.wr, wv, uwr, w₃, w₂, w₁, hwr]) (by decide)) fun x₃ y₃ =>
    Steps.wp_mov32i fun x₄ y₄ => WP.block_nil ?_
  have hm : x₄.mem = v.mem := by rw [y₄.mem, y₃.mem, y₂.mem, y₁.mem]
  have fv' : Frame (wl σ stk) s₃.mem v.mem := by
    rw [← um]
    exact fv.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
  have ftl : Frame (wl σ stk) t.mem x₄.mem := by rw [hm]; exact fsl.trans fv'
  have rd3 : ∀ d e (v : BitVec 64) (m : Mem), d + 8 ≤ e ∨ e + 8 ≤ d → d < 2400 → e < 2400 →
      (m.writeW (W σ + BitVec.ofNat 64 e) v).readW (W σ + BitVec.ofNat 64 d) 64 = m.readW (W σ + BitVec.ofNat 64 d) 64 :=
    fun d e v m h hd he => readW_writeW_off m (W σ) v (d := d) (e := e) (n := 8) (by omega_using [hd])
      (by omega_using [he]) h
  refine ⟨by rw [y₄.rd, y₃.rd, y₂.rd, y₁.rd, rv, urd, r₃, r₂, r₁], by rw [y₄.wr, y₃.wr, y₂.wr, y₁.wr, wv, uwr, w₃, w₂, w₁],
    ?_, ?_, ?_, by rw [y₄.gpr]; rfl, fun g hg => ?_, by rw [hm]; exact lv, hf.trans (wl_wf ftl), ftl,
    fun g hg => ?_⟩
  · rw [y₄.other _ (by decide), y₃.other _ (by decide), y₂.other _ (by decide), y₁.gpr,
      slot oPtr (Nat.le_refl _) (by decide), m₃, m₂, m₁, rd3 _ _ _ _ (by decide) (by decide) (by decide),
      rd3 _ _ _ _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  · rw [y₄.other _ (by decide), y₃.other _ (by decide), y₂.gpr, y₁.mem, slot oLeft (by decide) (by decide), m₃, m₂,
      rd3 _ _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64, g₁]
  · rw [y₄.other _ (by decide), y₃.gpr, y₂.mem, y₁.mem, slot oPos (by decide) (by decide), m₃,
      Mem.readW_writeW_self64, g₂, g₁]
  · have h1 : g ≠ .rcx ∧ g ≠ .rsi ∧ g ≠ .rdx ∧ g ≠ .rdi := by
      rcases hg with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [y₄.other _ h1.1, y₃.other _ h1.2.1, y₂.other _ h1.2.2.1, y₁.other _ h1.2.2.2, gv _ hg,
      go _ h1.2.2.2 h1.2.1 h1.2.2.1 h1.1, g₃']
  · obtain ⟨-, hcx, hdx, hsi, hdi, -⟩ := cs_ne hg
    rw [y₄.other _ hcx, y₃.other _ hsi, y₂.other _ hdx, y₁.other _ hdi, cv g hg, go _ hdi hsi hdx hcx, g₃']

/-! ## The loop -/

theorem rep_step {w : Nat} (hw8 : 8 * w + 8 ≤ L σ) (k : Nat) :
    Rep 136 ((msg σ k).take (8 * (w + 1))) =
      if w % 17 = 16 then keccakF (xorAt (Rep 136 ((msg σ k).take (8 * w))) (8 * (w % 17)) (chunk8 σ k w))
      else xorAt (Rep 136 ((msg σ k).take (8 * w))) (8 * (w % 17)) (chunk8 σ k w) := by
  have hl : ((msg σ k).take (8 * w)).length = 8 * w := by
    rw [List.length_take, length_msg]; omega_using [hw8]
  have hm : ((msg σ k).take (8 * w)).length % 136 = 8 * (w % 17) := by rw [hl]; omega_using []
  rw [show 8 * (w + 1) = 8 * w + 8 by omega_using [], List.take_add,
    rep_append (by decide) (by decide) _ _ (by rw [length_chunk8 k hw8]; decide)
      (by rw [hm, length_chunk8 k hw8]; omega_using []),
    hm, length_chunk8 k hw8]
  by_cases h : w % 17 = 16
  · rw [ite_eq_left (show 8 * (w % 17) + 8 = 136 by omega_using [h]), ite_eq_left h]
  · rw [ite_eq_right (show ¬ 8 * (w % 17) + 8 = 136 by omega_using [h]), ite_eq_right h]

theorem Inv.congr {w : Nat} {s t : State} (h : Inv σ stk w s) (hg : t.gpr = s.gpr) (hm : t.mem = s.mem)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) : Inv σ stk w t :=
  ⟨by rw [hr, h.rd], by rw [hw, h.wr], by rw [hg, h.r8], fun k hk => by rw [hg, h.ptr k hk], by rw [hg, h.pos],
    by rw [hg, h.dx], by rw [hg, h.cx], by rw [hm]; exact h.lanes, by rw [hm]; exact h.frame, by rw [hg, h.sp],
    fun r hr => by rw [hg, h.cs r hr]⟩

theorem test_ok {w : Nat} {t : State} (hI : Inv σ stk w t) :
    WP isa (.block [.alu .test .rdx (.reg .rdx)]) t
      (fun s' => Inv σ stk w s' ∧ s'.zf = some (decide (L σ - 8 * w = 0))) :=
  Proof.Sha3.X86_64.wp_test fun s' g m r w z => WP.block_nil ⟨hI.congr g m r w, by
    rw [z, hI.dx, BitVec.and_self, Proof.Sha3.ofNat_beq_zero (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (σ.gpr .rdx).isLt)]⟩

theorem body_ok (hp : Thash4Pre n stk σ) {perm : Prog isa} (hperm : PermOk perm σ stk) {w : Nat}
    (hw : w + 1 ≤ nw σ) {s : State} (hI : Inv σ stk w s) :
    WP isa (body perm) s (fun s' => Inv σ stk (w + 1) s' ∧ s'.zf = some (decide (w + 1 = nw σ))) := by
  have hL := len_eq hp
  have hw8 : 8 * w + 8 ≤ L σ := by omega_using [hL, hw]
  have hz : decide (L σ - 8 * (w + 1) = 0) = decide (w + 1 = nw σ) := by
    simp only [decide_eq_decide]; omega_using [hL, hw]
  unfold body
  refine WP.seq (WP.mono (row_ok hp hw hI) fun t ht => WP.seq ?_)
  refine WP.ite (decide (w % 17 = 16)) ht.zf (fun hb => ?_) (fun hb => ?_)
  · have h16 : w % 17 = 16 := of_decide_eq_true hb
    refine WP.mono (permKeep_ok hp hperm ht.rd ht.wr ht.sp ht.r8 ht.lanes ht.frame)
      fun t' ⟨r', w', di', dx', si', cx', g', l', f', _, c'⟩ => WP.mono (test_ok ?_) fun s' ⟨h1, h2⟩ =>
        ⟨h1, by rw [h2, hz]⟩
    refine ⟨by rw [r', ht.rd], by rw [w', ht.wr], by rw [g' _ (Or.inl rfl), ht.r8], fun k hk => ?_,
      by rw [si', ht.pos], by rw [dx', ht.dx], ?_, lanes4_congr l' fun k _ => by rw [rep_step hw8 k, ite_eq_left h16],
      f', by rw [g' _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), ht.sp], fun r hr => by rw [c' r hr, ht.cs r hr]⟩
    · rcases Proof.Sha3.X86_64.X4.cases4 hk with rfl | rfl | rfl | rfl
      · show t'.gpr .rdi = _; rw [di']; exact ht.ptr 0 (by decide)
      · show t'.gpr .r9 = _; rw [g' _ (Or.inr (Or.inl rfl))]; exact ht.ptr 1 (by decide)
      · show t'.gpr .r10 = _; rw [g' _ (Or.inr (Or.inr (Or.inl rfl)))]; exact ht.ptr 2 (by decide)
      · show t'.gpr .r11 = _; rw [g' _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact ht.ptr 3 (by decide)
    · rw [cx', show 32 * ((w + 1) % 17) = 0 by omega_using [h16]]; rfl
  · have h16 : ¬ w % 17 = 16 := fun h => by simp [h] at hb
    refine WP.block_nil (WP.mono (test_ok ?_) fun s' ⟨h1, h2⟩ => ⟨h1, by rw [h2, hz]⟩)
    exact ⟨ht.rd, ht.wr, ht.r8, ht.ptr, ht.pos, ht.dx, by rw [ht.cx, show 32 * ((w + 1) % 17) = 32 * (w % 17) + 32 by
        omega_using [h16]],
      lanes4_congr ht.lanes fun k _ => by rw [rep_step hw8 k, ite_eq_right h16], ht.frame, ht.sp, ht.cs⟩

theorem loop_ok (hp : Thash4Pre n stk σ) {perm : Prog isa} (hperm : PermOk perm σ stk) {s : State}
    (hI : Inv σ stk 0 s) : WP isa (.loop (body perm) .ne) s (Inv σ stk (nw σ)) := by
  have hL := len_eq hp
  have h0 : 0 < L σ := hp.len_pos
  have hpos : 1 ≤ nw σ := by omega_using [h0, hL]
  refine WP.loop (M := isa) (Q := Inv σ stk (nw σ))
    (fun (m : Nat) (t : State) => ∃ w, m = nw σ - w ∧ w + 1 ≤ nw σ ∧ Inv σ stk w t) ?_ (nw σ) s ⟨0, rfl, hpos, hI⟩
  rintro m t ⟨w, rfl, hw, hIw⟩
  refine WP.mono (body_ok hp hperm hw hIw) fun t' ⟨h1, h2⟩ => ?_
  by_cases e : w + 1 = nw σ
  · exact Or.inl ⟨by show t'.zf.map (!·) = some false; rw [h2]; simp [e], e ▸ h1⟩
  · exact Or.inr ⟨by show t'.zf.map (!·) = some true; rw [h2]; simp [e],
      _, by omega_using [hw, e], w + 1, rfl, by omega_using [hw, e], h1⟩

/-! ## The padding -/

/-- The padding of lane `k`: `0x1f` XORed into its byte `8 r`, and `0x80`
into its byte 135. -/
theorem padLane_ok (hp : Thash4Pre n stk σ) {k : Nat} (hk : k < 4) {r : Nat} (hr : r < 17) {A : Nat → KState}
    {t : State} (hwr : t.wr = σ.wr) (h8 : t.gpr .r8 = W σ) (hcx : t.gpr .rcx = BitVec.ofNat 64 (32 * r))
    (hsi : t.gpr .rsi = 0x8000000000000000) (hl : Lanes4 t.mem (W σ) A) (hf : Frame (wf σ stk) σ.mem t.mem) :
    WP isa (.block (padLane k)) t (fun t' => (∀ g, g ≠ .rax → t'.gpr g = t.gpr g) ∧ t'.rd = t.rd ∧
      t'.wr = t.wr ∧
      Lanes4 t'.mem (W σ) (fun k' => if k' = k then xorByte (xorByte (A k') (8 * r) 0x1f) 135 0x80 else A k') ∧
      Frame (wf σ stk) σ.mem t'.mem ∧ Frame (wl σ stk) t.mem t'.mem) := by
  have hla : la (W σ) r k = W σ + BitVec.ofNat 64 (32 * r + 8 * k) := rfl
  have hlb : la (W σ) 16 k = W σ + BitVec.ofNat 64 (512 + 8 * k) := rfl
  have hc : ∀ i, i < 17 → (⟨W σ, 1600⟩ : Region).Contains (la (W σ) i k) (64 / 8) := fun i hi =>
    Offset.contains_base _ (by omega_using [hi, hk]) (by omega_using [hi, hk])
  refine Proof.Sha3.X86_64.wp_movm (a := la (W σ) r k) (by rw [ea_rowLane, h8, hcx, hla, add_ofNat])
    (by rw [hla]; exact rw_work hp hwr (by simp [workLen]; omega_using [hr, hk])) fun t₁ u₁ => ?_
  refine Proof.Sha3.X86_64.wp_xori fun t₂ u₂ => ?_
  refine Proof.Sha3.X86_64.wp_store (a := la (W σ) r k) (by rw [ea_rowLane, u₂.other _ (by decide),
    u₁.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h8, hcx, hla, add_ofNat])
    (by rw [hla, u₂.wr, u₁.wr]; exact wr_work hp hwr (by simp [workLen]; omega_using [hr, hk]))
    fun t₃ g₃ m₃ r₃ w₃ => ?_
  have hm₃ : t₃.mem = t.mem.writeW (la (W σ) r k) (t.mem.readW (la (W σ) r k) 64 ^^^
      BitVec.signExtend 64 (0x1f : BitVec 32)) := by rw [m₃, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem]
  have l₃ := lanes4_xorLane hl (i := r) (v := t.mem.readW (la (W σ) r k) 64 ^^^ BitVec.signExtend 64 (0x1f : BitVec 32))
    (by omega_using [hr]) hk (bs := [0x1f, 0, 0, 0, 0, 0, 0, 0]) rfl fun d hd => by
    rw [BitVec.extractLsb'_xor, byte_readW _ _ (by omega_using [hd]), Proof.SlhDsa.X86_64.sx1f,
      Proof.SlhDsa.X86_64.bytes_0x1f d hd]
  rw [← hm₃] at l₃
  have f₃ : Frame (wl σ stk) t.mem t₃.mem := by
    rw [hm₃]; exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (hc r hr)
  have g₃' : ∀ g, g ≠ .rax → t₃.gpr g = t.gpr g := fun g h => by rw [g₃, u₂.other _ h, u₁.other _ h]
  refine Proof.Sha3.X86_64.wp_movm (a := la (W σ) 16 k) (by rw [ea_at', g₃' _ (by decide), h8, hlb])
    (by rw [hlb, r₃, w₃, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rw_work hp hwr (by simp [workLen]; omega_using [hk]))
    fun t₄ u₄ => ?_
  refine Proof.Sha3.X86_64.wp_xor fun t₅ u₅ => ?_
  refine Proof.Sha3.X86_64.wp_store (a := la (W σ) 16 k) (by rw [ea_at', u₅.other _ (by decide),
    u₄.other _ (by decide), g₃' _ (by decide), h8, hlb])
    (by rw [hlb, u₅.wr, u₄.wr, w₃, u₂.wr, u₁.wr]; exact wr_work hp hwr (by simp [workLen]; omega_using [hk]))
    fun t₆ g₆ m₆ r₆ w₆ => WP.block_nil ?_
  have hm₆ : t₆.mem = t₃.mem.writeW (la (W σ) 16 k) (t₃.mem.readW (la (W σ) 16 k) 64 ^^^ 0x8000000000000000) := by
    rw [m₆, u₅.gpr, u₄.gpr, u₄.other _ (by decide), g₃' _ (by decide), hsi, u₅.mem, u₄.mem]
  have l₆ := lanes4_xorLane l₃ (i := 16) (v := t₃.mem.readW (la (W σ) 16 k) 64 ^^^ 0x8000000000000000)
    (by decide) hk (bs := [0, 0, 0, 0, 0, 0, 0, 0x80]) rfl fun d hd => by
    rw [BitVec.extractLsb'_xor, byte_readW _ _ (by omega_using [hd]), Proof.SlhDsa.X86_64.bytes_0x80 d hd]
  rw [← hm₆] at l₆
  have f₆ : Frame (wl σ stk) t₃.mem t₆.mem := by
    rw [hm₆]; exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (hc 16 (by decide))
  refine ⟨fun g h => by rw [g₆, u₅.other _ h, u₄.other _ h, g₃' _ h], by rw [r₆, u₅.rd, u₄.rd, r₃, u₂.rd, u₁.rd],
    by rw [w₆, u₅.wr, u₄.wr, w₃, u₂.wr, u₁.wr], lanes4_congr l₆ fun k' _ => ?_, hf.trans (wl_wf (f₃.trans f₆)),
    f₃.trans f₆⟩
  by_cases e : k' = k
  · subst e
    simp only [ite_true]
    rw [Proof.SlhDsa.X86_64.xorAt_lo, Proof.SlhDsa.X86_64.xorAt_hi]
  · simp only [e, ite_false]

theorem pad_eq : pad = .movImm64 .rsi 0x8000000000000000 :: (padLane 0 ++ (padLane 1 ++ (padLane 2 ++
    (padLane 3 ++ [])))) := rfl

/-- The state of the padding. -/
abbrev padState (A : KState) (r : Nat) : KState := xorByte (xorByte A (8 * r) 0x1f) 135 0x80

theorem pad_ok (hp : Thash4Pre n stk σ) {s : State} (hI : Inv σ stk (nw σ) s) :
    WP isa (.block pad) s (fun t => t.rd = σ.rd ∧ t.wr = σ.wr ∧ t.gpr .r8 = W σ ∧
      (∀ k < 4, t.gpr (lanePtr k) = laneP σ k) ∧ t.gpr .rsp = σ.gpr .rsp ∧
      Lanes4 t.mem (W σ) (fun k => padState (Rep 136 ((msg σ k).take (8 * nw σ))) (nw σ % 17)) ∧
      Frame (wf σ stk) σ.mem t.mem ∧ ∀ r ∈ calleeSaved, t.gpr r = σ.gpr r) := by
  have hr : nw σ % 17 < 17 := Nat.mod_lt _ (by decide)
  rw [pad_eq]
  refine Proof.Sha3.X86_64.wp_movi64 fun t₀ u₀ => ?_
  have h8₀ : t₀.gpr .r8 = W σ := by rw [u₀.other _ (by decide), hI.r8]
  have hcx₀ : t₀.gpr .rcx = BitVec.ofNat 64 (32 * (nw σ % 17)) := by rw [u₀.other _ (by decide), hI.cx]
  have hw₀ : t₀.wr = σ.wr := by rw [u₀.wr, hI.wr]
  refine WP.block_append (WP.mono (padLane_ok hp (k := 0) (A := fun k => Rep 136 ((msg σ k).take (8 * nw σ)))
    (by decide) hr hw₀ h8₀ hcx₀ u₀.gpr
    (by rw [u₀.mem]; exact hI.lanes) (by rw [u₀.mem]; exact hI.frame)) fun t₁ ⟨g₁, r₁, w₁, l₁, f₁, _⟩ => ?_)
  refine WP.block_append (WP.mono (padLane_ok hp (k := 1) (by decide) hr (by rw [w₁, hw₀])
    (by rw [g₁ _ (by decide), h8₀]) (by rw [g₁ _ (by decide), hcx₀]) (by rw [g₁ _ (by decide), u₀.gpr]) l₁ f₁)
    fun t₂ ⟨g₂, r₂, w₂, l₂, f₂, _⟩ => ?_)
  refine WP.block_append (WP.mono (padLane_ok hp (k := 2) (by decide) hr (by rw [w₂, w₁, hw₀])
    (by rw [g₂ _ (by decide), g₁ _ (by decide), h8₀]) (by rw [g₂ _ (by decide), g₁ _ (by decide), hcx₀])
    (by rw [g₂ _ (by decide), g₁ _ (by decide), u₀.gpr]) l₂ f₂) fun t₃ ⟨g₃, r₃, w₃, l₃, f₃, _⟩ => ?_)
  refine WP.block_append (WP.mono (padLane_ok hp (k := 3) (by decide) hr (by rw [w₃, w₂, w₁, hw₀])
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h8₀])
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hcx₀])
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), u₀.gpr]) l₃ f₃)
    fun t₄ ⟨g₄, r₄, w₄, l₄, f₄, _⟩ => WP.block_nil ?_)
  have g : ∀ r, r ≠ .rax → r ≠ .rsi → t₄.gpr r = s.gpr r := fun r h1 h2 => by
    rw [g₄ _ h1, g₃ _ h1, g₂ _ h1, g₁ _ h1, u₀.other _ h2]
  refine ⟨by rw [r₄, r₃, r₂, r₁, u₀.rd, hI.rd], by rw [w₄, w₃, w₂, w₁, hw₀],
    by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h8₀], fun k hk => ?_,
    by rw [g _ (by decide) (by decide), hI.sp], lanes4_congr l₄ fun k hk => ?_, f₄,
    fun r hr => by rw [g _ (cs_ne hr).1 (cs_ne hr).2.2.2.1, hI.cs r hr]⟩
  · have hne : lanePtr k ≠ .rax ∧ lanePtr k ≠ .rsi := by
      rcases Proof.Sha3.X86_64.X4.cases4 hk with rfl | rfl | rfl | rfl <;> decide
    rw [g _ hne.1 hne.2, hI.ptr k hk]
  · rcases Proof.Sha3.X86_64.X4.cases4 hk with rfl | rfl | rfl | rfl <;> simp <;> rfl

/-! ## The outputs -/

theorem outAt_succ (k : Nat) : outAt σ (k + 1) = outAt σ k + σ.gpr .rsi := by
  simp only [outAt]
  rw [Nat.succ_mul, ← add_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Where output `k` is, within the lanes. -/
theorem outAt_eq {off : Nat} (ho : σ.gpr .rcx = σ.gpr .rdi + BitVec.ofNat 64 off) (k : Nat) :
    outAt σ k = inp σ + BitVec.ofNat 64 (off + k * str σ) := by
  simp only [outAt, ho, add_ofNat]

theorem out_sub (hp : Thash4Pre n stk σ) {k : Nat} (hk : k < 4) : Region.Sub ⟨outAt σ k, n⟩ (lanesR σ) := by
  have hoff' : n + 32 + n ≤ str σ := hp.out_fit
  have h2 := kstr_le (σ := σ) hk
  rw [outAt_eq hp.out_eq]; exact sub_off _ (by omega_using [hoff', h2])

theorem out_disj (hp : Thash4Pre n stk σ) {k k' : Nat} (hk : k < 4) (hk' : k' < 4) (hne : k ≠ k') :
    Region.Disjoint ⟨outAt σ k, n⟩ ⟨outAt σ k', n⟩ := by
  have hoff' : n + 32 + n ≤ str σ := hp.out_fit
  have h1 := kstr_le (σ := σ) hk
  have h2 := kstr_le (σ := σ) hk'
  have hs := str_lt hp
  rw [outAt_eq hp.out_eq, outAt_eq hp.out_eq]
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : k * str σ + str σ ≤ k' * str σ := by
      have := Nat.mul_le_mul_right (str σ) (show k + 1 ≤ k' by omega_using [h]); rw [Nat.succ_mul] at this; exact this
    exact Offset.disjoint _ (Or.inl (by omega_using [this, hoff'])) (by omega_using [h1, hoff', hs])
      (by omega_using [h2, hoff', hs])
  · have : k' * str σ + str σ ≤ k * str σ := by
      have := Nat.mul_le_mul_right (str σ) (show k' + 1 ≤ k by omega_using [h]); rw [Nat.succ_mul] at this; exact this
    exact Offset.disjoint _ (Or.inr (by omega_using [this, hoff'])) (by omega_using [h1, hoff', hs])
      (by omega_using [h2, hoff', hs])

theorem out_work (hp : Thash4Pre n stk σ) {k : Nat} (hk : k < 4) : Region.Disjoint ⟨outAt σ k, n⟩ (workR σ) :=
  hp.lanes_work.sub_left (out_sub hp hk)

/-- Word `i` of state `k` to output `k`. -/
abbrev word (n k i : Nat) : List Instr :=
  [.mov .rax (.mem (VG.Impl.Sha3.X86_64.at_ .r8 (32 * i + 8 * k))),
    .store (VG.Impl.Sha3.X86_64.at_ (lanePtr k) (n + 32 + 8 * i)) .rax]

theorem byteOf_word (A : KState) {i d : Nat} (hi : i < 25) (hd : d < 8) :
    A[i]!.extractLsb' (8 * d) 8 = byteOf A (8 * i + d) := by
  rw [Proof.Sha3.byteOf_eq _ hi hd, Proof.Sha3.getElem!_eq _ hi]

theorem outAt_lane (hp : Thash4Pre n stk σ) (k : Nat) : outAt σ k = laneP σ k + BitVec.ofNat 64 (n + 32) := by
  rw [outAt_eq hp.out_eq, laneP_off, Nat.add_comm]

theorem words_ok (hp : Thash4Pre n stk σ) (hn : n ≤ 136) {k : Nat} (hk : k < 4) {F : Nat → KState} :
    ∀ i, 8 * i ≤ n → ∀ t : State, t.wr = σ.wr → t.gpr .r8 = W σ → t.gpr (lanePtr k) = laneP σ k →
      Lanes4 t.mem (W σ) F →
      WP isa (.block ((List.range i).flatMap (word n k))) t (fun t' => (∀ g, g ≠ .rax → t'.gpr g = t.gpr g) ∧
        t'.rd = t.rd ∧ t'.wr = t.wr ∧ (∀ j < 8 * i, t'.mem (outAt σ k + BitVec.ofNat 64 j) = byteOf (F k) j) ∧
        Frame [⟨outAt σ k, n⟩] t.mem t'.mem) := by
  intro i
  induction i with
  | zero => intro _ t _ _ _ _; exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, fun j hj => absurd hj (by omega_using []),
      Frame.refl _ _⟩
  | succ i ih =>
    intro hi t hw h8 hpk hl
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ih (by omega_using [hi]) t hw h8 hpk hl) fun t₁ ⟨g₁, r₁, w₁, b₁, f₁⟩ => ?_)
    have hoff' : n + 32 + n ≤ str σ := hp.out_fit
    have h2 := kstr_le (σ := σ) hk
    have hs := str_lt hp
    have hpk₁ : t₁.gpr (lanePtr k) = laneP σ k := by
      rw [g₁ _ (by rcases Proof.Sha3.X86_64.X4.cases4 hk with rfl | rfl | rfl | rfl <;> decide), hpk]
    have hl₁ : Lanes4 t₁.mem (W σ) F := lanes4_frame hl f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((out_work hp hk).sub_right (sub_pre _ (by decide))).symm
    refine Proof.Sha3.X86_64.wp_movm (a := la (W σ) i k) (by rw [ea_at', g₁ _ (by decide), h8])
      (by rw [r₁, w₁]; exact rw_work hp hw (by simp [workLen]; omega_using [hi, hn, hk])) fun t₂ u₂ => ?_
    refine Proof.Sha3.X86_64.wp_store (a := outAt σ k + BitVec.ofNat 64 (8 * i))
      (by rw [ea_at', u₂.other _ (by rcases Proof.Sha3.X86_64.X4.cases4 hk with rfl | rfl | rfl | rfl <;> decide), hpk₁,
        outAt_lane hp, add_ofNat (laneP σ k) (n + 32) (8 * i)])
      (by
        rw [u₂.wr, w₁, hw, hp.wr]
        refine ⟨lanesR σ, by simp, ?_⟩
        rw [outAt_eq hp.out_eq, add_ofNat]
        exact Offset.contains_base _ (by omega_using [hi, hoff', h2]) (by omega_using [hi, hoff', h2, hs]))
      fun t₃ g₃ m₃ r₃ w₃ => WP.block_nil ?_
    have hm₃ : t₃.mem = t₁.mem.writeW (outAt σ k + BitVec.ofNat 64 (8 * i)) ((F k)[i]!) := by
      rw [m₃, u₂.gpr, u₂.mem, hl₁ i (by omega_using [hi, hn]) k hk]
    refine ⟨fun g h => by rw [g₃, u₂.other _ h, g₁ _ h], by rw [r₃, u₂.rd, r₁], by rw [w₃, u₂.wr, w₁],
      fun j hj => ?_, ?_⟩
    · rw [hm₃]
      by_cases c : j < 8 * i
      · rw [writeW_byte_off _ _ _ _ (by
            rw [Offset.sub_toNat' _ (by omega_using [hi, hn]) (by omega_using [hj, hi, hn])]
            split <;> rename_i hs' <;> omega_using [c, hs', hj, hi, hn]), b₁ j c]
      · rw [show outAt σ k + BitVec.ofNat 64 j = outAt σ k + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 (j - 8 * i) by
            rw [add_ofNat, show 8 * i + (j - 8 * i) = j by omega_using [c]],
          writeW_byte _ _ _ (by omega_using [hj, c]) (by decide), byteOf_word _ (by omega_using [hi, hn])
            (by omega_using [hj, c]), show 8 * i + (j - 8 * i) = j by omega_using [c]]
    · rw [hm₃]
      exact f₁.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hn]))

/-- The outputs of the four lanes. -/
abbrev outs (n : Nat) (σ : State) : List Region := (List.range 4).map fun k => ⟨outAt σ k, n⟩

theorem extract_eq : extract n = (List.range (n / 8)).flatMap (word n 0) ++ ((List.range (n / 8)).flatMap (word n 1) ++
    ((List.range (n / 8)).flatMap (word n 2) ++ ((List.range (n / 8)).flatMap (word n 3) ++ []))) := rfl

theorem extract_ok (hp : Thash4Pre n stk σ) (hn : n % 8 = 0) (hn' : n ≤ 136) {F : Nat → KState} {t : State}
    (hw : t.wr = σ.wr) (h8 : t.gpr .r8 = W σ) (hpk : ∀ k < 4, t.gpr (lanePtr k) = laneP σ k)
    (hl : Lanes4 t.mem (W σ) F) :
    WP isa (.block (extract n)) t (fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ k < 4, ∀ j < n, t'.mem (outAt σ k + BitVec.ofNat 64 j) = byteOf (F k) j) ∧
      Frame (outs n σ) t.mem t'.mem) := by
  have hn8 : 8 * (n / 8) = n := by omega_using [hn]
  rw [extract_eq]
  have lf : ∀ {k : Nat} {m m' : Mem}, k < 4 → Lanes4 m (W σ) F → Frame [⟨outAt σ k, n⟩] m m' →
      Lanes4 m' (W σ) F := fun {k _ _} hk hl hf => lanes4_frame hl hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((out_work hp hk).sub_right (sub_pre _ (by decide))).symm
  have keep : ∀ {k k' : Nat} {m m' : Mem}, k < 4 → k' < 4 → k ≠ k' → Frame [⟨outAt σ k', n⟩] m m' →
      ∀ j < n, m' (outAt σ k + BitVec.ofNat 64 j) = m (outAt σ k + BitVec.ofNat 64 j) := fun {k k' _ _} hk hk' hne hf j hj =>
    Frame.bytes (R := ⟨outAt σ k, n⟩) hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact out_disj hp hk hk' hne) (show n ≤ 2 ^ 64 by omega_using [hn']) hj
  have pk : ∀ {k : Nat} {u : State}, k < 4 → (∀ g, g ≠ .rax → u.gpr g = t.gpr g) → u.gpr (lanePtr k) = laneP σ k :=
    fun {k u} hk h => by rw [h _ (by rcases Proof.Sha3.X86_64.X4.cases4 hk with rfl | rfl | rfl | rfl <;> decide), hpk k hk]
  refine WP.block_append (WP.mono (words_ok hp hn' (k := 0) (F := F) (by decide) (n / 8) (by omega_using [hn8]) t hw h8
    (hpk 0 (by decide)) hl) fun t₃ ⟨g₃, r₃, w₃, b₃, f₃⟩ => ?_)
  refine WP.block_append (WP.mono (words_ok hp hn' (k := 1) (F := F) (by decide) (n / 8) (by omega_using [hn8]) t₃
    (by rw [w₃, hw]) (by rw [g₃ _ (by decide), h8]) (pk (by decide) g₃) (lf (by decide) hl f₃))
    fun t₄ ⟨g₄, r₄, w₄, b₄, f₄⟩ => ?_)
  have g₄' : ∀ g, g ≠ .rax → t₄.gpr g = t.gpr g := fun g h => by rw [g₄ _ h, g₃ _ h]
  refine WP.block_append (WP.mono (words_ok hp hn' (k := 2) (F := F) (by decide) (n / 8) (by omega_using [hn8]) t₄
    (by rw [w₄, w₃, hw]) (by rw [g₄' _ (by decide), h8]) (pk (by decide) g₄') (lf (by decide) (lf (by decide) hl f₃) f₄))
    fun t₅ ⟨g₅, r₅, w₅, b₅, f₅⟩ => ?_)
  have g₅' : ∀ g, g ≠ .rax → t₅.gpr g = t.gpr g := fun g h => by rw [g₅ _ h, g₄' _ h]
  refine WP.block_append (WP.mono (words_ok hp hn' (k := 3) (F := F) (by decide) (n / 8) (by omega_using [hn8]) t₅
    (by rw [w₅, w₄, w₃, hw]) (by rw [g₅' _ (by decide), h8]) (pk (by decide) g₅')
    (lf (by decide) (lf (by decide) (lf (by decide) hl f₃) f₄) f₅))
    fun t₆ ⟨_, r₆, w₆, b₆, f₆⟩ => WP.block_nil ?_)
  rw [hn8] at b₃ b₄ b₅ b₆
  refine ⟨by rw [r₆, r₅, r₄, r₃], by rw [w₆, w₅, w₄, w₃], fun k hk j hj => ?_, ?_⟩
  · rcases Proof.Sha3.X86_64.X4.cases4 hk with rfl | rfl | rfl | rfl
    · rw [keep (by decide) (by decide) (by decide) f₆ j hj, keep (by decide) (by decide) (by decide) f₅ j hj,
        keep (by decide) (by decide) (by decide) f₄ j hj, b₃ j hj]
    · rw [keep (by decide) (by decide) (by decide) f₆ j hj, keep (by decide) (by decide) (by decide) f₅ j hj, b₄ j hj]
    · rw [keep (by decide) (by decide) (by decide) f₆ j hj, b₅ j hj]
    · exact b₆ j hj
  · have m : ∀ k, k < 4 → (⟨outAt σ k, n⟩ : Region) ∈ outs n σ := fun k hk => List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
    have sub : ∀ k, k < 4 → ∀ r ∈ [(⟨outAt σ k, n⟩ : Region)], ∃ r' ∈ outs n σ, Region.Sub r r' := fun k hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, m k hk, fun _ h => h⟩
    exact (((f₃.sub (sub 0 (by decide))).trans (f₄.sub (sub 1 (by decide)))).trans
      (f₅.sub (sub 2 (by decide)))).trans (f₆.sub (sub 3 (by decide)))

/-! ## `thash4` -/

theorem final_eq (hp : Thash4Pre n stk σ) (k : Nat) :
    keccakF (padState (Rep 136 ((msg σ k).take (8 * nw σ))) (nw σ % 17)) = finalState (msg σ k) := by
  have hL := len_eq hp
  rw [List.take_of_length_le (by rw [length_msg]; omega_using [hL]), finalState, length_msg,
    show L σ % 136 = 8 * (nw σ % 17) by omega_using [hL]]

/-- What the proof needs of the code `tail` after the outputs: it keeps the
memory and the regions. -/
def TailOk (tail : List Instr) : Prop :=
  ∀ t : State, WP isa (.block tail) t fun t' => t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.gpr = t.gpr

theorem tailOk_vzu : TailOk [.vop .vzeroupper] := fun _ =>
  Proof.SlhDsa.X86_64.wp_vzu fun _ g m r w => WP.block_nil ⟨m, r, w, g⟩

theorem tailOk_nil : TailOk [] := fun _ => WP.block_nil ⟨rfl, rfl, rfl, rfl⟩

/-- `extract` writes no callee-saved register. -/
theorem extract_keep (n : Nat) : ∀ r ∈ calleeSaved, ∀ i ∈ instrs (Code.block (C := Cond) (extract n)),
    Taint.clobbers i r = false := by
  intro r hr i hi
  simp only [instrs, extract, extractLane, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  obtain ⟨_, _, _, _, rfl | rfl⟩ := hi <;>
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A postcondition of code that never writes the registers `P` keeps them. -/
theorem wp_gprs_keep {c : Prog isa} {P : Reg → Prop} (hc : ∀ r, P r → ∀ i ∈ instrs c, Taint.clobbers i r = false)
    {s : State} {Q : State → Prop} (h : WP isa c s Q) : WP isa c s fun s' => Q s' ∧ ∀ r, P r → s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => Exec.gpr (hc r hr) he⟩

/-- `thash4With zero perm n tail` writes each output, and changes only the
outputs, `work` but its table, and the `stk` bytes below the stack
pointer, and keeps the callee-saved registers. -/
theorem correctWith (hp : Thash4Pre n stk σ) (hn : n % 8 = 0) (hn' : n ≤ 136) {zero : List Instr}
    {perm : Prog isa} {tail : List Instr} (hz : ZeroOk zero σ) (hperm : PermOk perm σ stk) (htail : TailOk tail) :
    WP isa (thash4With zero perm n tail) σ (fun s' =>
      (∀ k < 4, bytesAt s'.mem (outAt σ k) n = Spec.Sha3.shake256 (msg σ k) n) ∧
      Frame (thash4Changes n stk σ) σ.mem s'.mem ∧ ∀ r ∈ calleeSaved, s'.gpr r = σ.gpr r) := by
  unfold thash4With
  refine WP.seq (WP.mono (pro_ok hz) fun s₀ h₀ => WP.seq (WP.mono (loop_ok hp hperm h₀) fun s₁ h₁ =>
    WP.seq (WP.mono (pad_ok hp h₁) fun s₂ ⟨r₂, w₂, h8₂, p₂, sp₂, l₂, f₂, cs₂⟩ => WP.seq ?_)))
  refine WP.mono (permKeep_ok hp hperm r₂ w₂ sp₂ h8₂ l₂ f₂) fun v ⟨_, wv, dv, _, _, _, gv, lv, fv, _, cv⟩ => ?_
  refine WP.block_append (WP.mono (wp_gprs_keep (extract_keep n) (extract_ok hp hn hn' (F := fun k => finalState (msg σ k))
    (by rw [wv, w₂]) (by rw [gv _ (Or.inl rfl), h8₂]) (fun k hk => ?_) (lanes4_congr lv fun k _ => final_eq hp k)))
    fun t ⟨⟨_, _, bt, ft⟩, gt⟩ => WP.mono (htail t) fun t' ⟨mt', _, _, gt'⟩ => ⟨fun k hk => ?_, ?_,
      fun r hr => by rw [gt', gt r hr, cv r hr, cs₂ r hr]⟩)
  · rcases Proof.Sha3.X86_64.X4.cases4 hk with rfl | rfl | rfl | rfl
    · show v.gpr .rdi = _; rw [dv]; exact p₂ 0 (by decide)
    · show v.gpr .r9 = _; rw [gv _ (Or.inr (Or.inl rfl))]; exact p₂ 1 (by decide)
    · show v.gpr .r10 = _; rw [gv _ (Or.inr (Or.inr (Or.inl rfl)))]; exact p₂ 2 (by decide)
    · show v.gpr .r11 = _; rw [gv _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact p₂ 3 (by decide)
  · refine Proof.SlhDsa.shake256_ext hn' (Proof.Sha3.bytesAt_length _ _ _) fun j hj => ?_
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [mt']; exact bt k hk j hj
  · rw [mt']
    exact (fv.mono fun r hr => List.mem_append_right _ hr).trans (ft.mono fun r hr => List.mem_append_left _ hr)

/-- `thash4 n fast` writes each output, and changes only the outputs and
`work` but its table. -/
theorem correct (hp : Thash4Pre n stk σ) (hn : n % 8 = 0) (hn' : n ≤ 136) (fast : Bool) :
    WP isa (thash4 n fast) σ (fun s' => (∀ k < 4, bytesAt s'.mem (outAt σ k) n = Spec.Sha3.shake256 (msg σ k) n) ∧
      Frame (thash4Changes n stk σ) σ.mem s'.mem ∧ ∀ r ∈ calleeSaved, s'.gpr r = σ.gpr r) :=
  correctWith hp hn hn' (zeroOk_V hp) (permOk_V hp fast) tailOk_vzu

end VG.Proof.SlhDsa.X86_64.Thash4Avx
