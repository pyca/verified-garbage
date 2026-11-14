module

public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Calls
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Bytes
public import VerifiedGarbage.Proof.Pbkdf2.MdStep
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Framework.Covers

/-! ### `Pbkdf2.RISCV64.Iterate`, which only this module used -/

section

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on RISC-V: the steps

The iteration (`Impl/Pbkdf2/RISCV64.lean`) is correct for any hash function
the generic streaming proofs describe (`Md`), whose digest code is as
`OutOk` says and whose padding is `Md.tailPad`, with any correct compression
function (`CalleeOk`), used as a black box through its proof; `Md.iterate_hmac`
says that its two compressions per step compute HMAC.

The lemmas here are about the states between the pieces of a step (`St`):
loading a key's hash value into the scratch space (`load_ok`), compressing
the block into it (`cmp_ok`), writing its digest over the block's first `D`
bytes (`digest_ok`), and `T ← T ⊕ U` with the count (`tail_ok`). Every write
is in the scratch space or `T`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_li wp_mv wp_addi wp_subi)
open VG.Impl.Pbkdf2.RISCV64 (It mov)
open VG.Proof.MdStream (Md)
open VG.WriteBytes (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Pbkdf2 (xorBytes)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_writeBytes_self writeBytes_at bytesAt_getD')

/-! ## The precondition -/

section
variable (P : It) (Wi : Nat) (s₀ : State)

abbrev key : Addr := s₀.gpr .a0
abbrev up : Addr := s₀.gpr .a1
abbrev tp : Addr := s₀.gpr .a3
abbrev scr : Addr := s₀.gpr .a4
/-- The number of steps. -/
abbrev nn : Nat := ((s₀.gpr .a2).setWidth 32).toNat
/-- `scratch`, rounded up to a multiple of 8. -/
abbrev sc : Addr := scr s₀ + BitVec.ofNat 64 (Align.pad (scr s₀))
abbrev keyR : Region := ⟨key s₀, 2 * P.S⟩
abbrev uR : Region := ⟨up s₀, P.D⟩
abbrev tR : Region := ⟨tp s₀, P.D⟩
abbrev scR : Region := ⟨scr s₀, Wi⟩
/-- The hash value being compressed, and the block. -/
abbrev hv : Addr := sc s₀ + BitVec.ofNat 64 P.hvO
abbrev blk : Addr := sc s₀ + BitVec.ofNat 64 P.blkO

end

structure Pre (P : It) (Wi : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [keyR P s₀, uR P s₀]
  wr : s₀.wr = [tR P s₀, scR Wi s₀]
  k_t : (keyR P s₀).Disjoint (tR P s₀)
  k_s : (keyR P s₀).Disjoint (scR Wi s₀)
  u_t : (uR P s₀).Disjoint (tR P s₀)
  u_s : (uR P s₀).Disjoint (scR Wi s₀)
  t_s : (tR P s₀).Disjoint (scR Wi s₀)

/-- The sizes the proof supports, checked for each hash function by `decide`. -/
structure Sizes (P : It) (Wi : Nat) : Prop where
  N0 : 0 < P.N
  N64 : P.N ≤ 64
  B128 : P.B ≤ 128
  D0 : 0 < P.D
  DN : P.D ≤ P.N
  DB : P.D < P.B
  padL : P.pad.length = P.B - P.D
  padV : ∀ i < P.pad.length, P.pad.getD i 0 < 256
  CW8 : P.CW % 8 = 0
  CWle : P.CW ≤ 1024
  fits : P.CW + 56 + P.N + P.B + 7 ≤ Wi
  W : Wi ≤ 8192

variable {P : It} {Wi : Nat} {s₀ : State} {L : Nat}

/-! ## The parts of the scratch space -/

theorem pad_le (x : Addr) : Align.pad x ≤ 7 := Nat.le_of_lt_succ (Align.pad_lt x)

theorem sc_add (s₀ : State) (a : Nat) :
    sc s₀ + BitVec.ofNat 64 a = scr s₀ + BitVec.ofNat 64 (Align.pad (scr s₀) + a) := Offset.add_add _ _ _

/-- A part of the aligned scratch space, within `scratch`. -/
theorem sc_sub {a n : Nat} (h : a + n + 7 ≤ Wi) : Region.Sub ⟨sc s₀ + BitVec.ofNat 64 a, n⟩ (scR Wi s₀) := by
  rw [sc_add]; exact Offset.sub_base _ (by have := pad_le (scr s₀); omega_using [h, this])

theorem sc_contains (hz : Sizes P Wi) {a n : Nat} (h : a + n + 7 ≤ Wi) :
    (scR Wi s₀).Contains (sc s₀ + BitVec.ofNat 64 a) n := by
  rw [sc_add]
  exact Offset.contains_base _ (by have := pad_le (scr s₀); omega_using [h, this])
    (by have := pad_le (scr s₀); have := hz.W; omega_arith)

theorem sc_al : (sc s₀).toNat % 8 = 0 := Align.align_al _

/-- Two parts of the aligned scratch space. -/
theorem sc_disj (hz : Sizes P Wi) {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n ≤ Wi) (hb : b + k ≤ Wi) :
    Region.Disjoint ⟨sc s₀ + BitVec.ofNat 64 a, n⟩ ⟨sc s₀ + BitVec.ofNat 64 b, k⟩ :=
  Offset.disjoint _ h (by have := hz.W; omega_using [ha, this]) (by have := hz.W; omega_using [hb, this])

theorem sc0 (s₀ : State) : sc s₀ + BitVec.ofNat 64 0 = sc s₀ := BitVec.add_zero _

/-! ## Between the pieces of a step -/

/-- The callee-saved registers our code never writes. -/
abbrev nvRegs : List Reg := [.s0, .s7, .s8, .s9, .s10, .s11]

/-- What holds between the pieces of a step, with `c` in `s6`. -/
structure St (P : It) (Wi : Nat) (H : Md P.B P.N L) (s₀ : State) (c : BitVec 64) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  s1 : s.gpr .s1 = hv P s₀
  s2 : s.gpr .s2 = sc s₀
  s3 : s.gpr .s3 = blk P s₀
  s4 : s.gpr .s4 = key s₀
  s5 : s.gpr .s5 = tp s₀
  s6 : s.gpr .s6 = c
  nv : ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r
  fr : Frame [tR P s₀, scR Wi s₀] s₀.mem s.mem
  saved : Spill.Saved (sc s₀) s₀.gpr P.saved s.mem
  pad : bytesAt s.mem (blk P s₀ + BitVec.ofNat 64 P.D) (P.B - P.D) = H.tailPad P.D

section
variable (hp : Pre P Wi s₀) (hz : Sizes P Wi)
include hp hz

/-- The byte at `x` of a region within the scratch space or `T`. -/
theorem in_scr {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n + 7 ≤ Wi) {k : Nat} (hk : k < n) :
    InRegions s.wr (sc s₀ + BitVec.ofNat 64 a + BitVec.ofNat 64 k) 1 :=
  ⟨scR Wi s₀, by rw [hwr, hp.wr]; simp, by
    rw [Offset.add_add]; exact sc_contains hz (by omega_using [h, hk])⟩

theorem in_t {s : State} (hwr : s.wr = s₀.wr) {k : Nat} (hk : k < P.D) :
    InRegions s.wr (tp s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨tR P s₀, by rw [hwr, hp.wr]; simp, Offset.contains_base _ (by omega_using [hk]) (by have := hz.DN; have := hz.N64; omega_arith)⟩

theorem in_key {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {k : Nat} (hk : k < 2 * P.S) :
    InRegions (s.rd ++ s.wr) (key s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨keyR P s₀, by rw [hrd, hwr, hp.rd]; simp,
    Offset.contains_base _ (by omega_using [hk]) (by have := hz.N64; have := hz.B128; simp only [It.S] at hk; omega_arith)⟩

/-- What a step writes keeps `St`'s facts: the regions written are in the
scratch space before the saved registers, the hash value, the block's first
`D` bytes and `T`. -/
theorem St.frame {H : Md P.B P.N L} {c c' : BitVec 64} {s s' : State} (h : St P Wi H s₀ c s)
    (hrd : s'.rd = s₀.rd) (hwr : s'.wr = s₀.wr) (hsp : s'.sp = s₀.sp) (hc : s'.gpr .s6 = c')
    (hg : ∀ r ∈ [Reg.s1, .s2, .s3, .s4, .s5] ++ nvRegs, s'.gpr r = s.gpr r)
    {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hrs : ∀ r ∈ rs, r = ⟨sc s₀, P.CW⟩ ∨ r = ⟨hv P s₀, P.N⟩ ∨ r = ⟨blk P s₀, P.D⟩ ∨ r = tR P s₀) :
    St P Wi H s₀ c' s' := by
  have hN := hz.N64
  have hB := hz.B128
  have hW := hz.W
  have hf₁ := hz.fits
  have hDB := hz.DB
  have tsc : ∀ {a n : Nat}, a + n + 7 ≤ Wi → Region.Disjoint (tR P s₀) ⟨sc s₀ + BitVec.ofNat 64 a, n⟩ :=
    fun h => hp.t_s.sub_right (sc_sub h)
  -- What the step writes is within `T` and `scratch`.
  have hsub : ∀ r ∈ rs, ∃ r' ∈ [tR P s₀, scR Wi s₀], Region.Sub r r' := by
    intro r hr
    rcases hrs r hr with rfl | rfl | rfl | rfl
    · exact ⟨scR Wi s₀, by simp, by rw [← sc0 s₀]; exact sc_sub (by omega_using [hf₁])⟩
    · exact ⟨scR Wi s₀, by simp, sc_sub (by simp only [It.hvO]; omega_using [hf₁])⟩
    · exact ⟨scR Wi s₀, by simp, sc_sub (by simp only [It.blkO, It.hvO]; omega_using [hf₁, hDB])⟩
    · exact ⟨tR P s₀, by simp, fun _ h => h⟩
  -- The saved registers and the padding are outside it.
  have dsv : ∀ r ∈ rs, Region.Disjoint ⟨sc s₀ + BitVec.ofNat 64 P.CW, 56⟩ r := by
    intro r hr
    rcases hrs r hr with rfl | rfl | rfl | rfl
    · have := sc_disj (s₀ := s₀) hz (a := P.CW) (n := 56) (b := 0) (k := P.CW) (.inr (by omega_using []))
        (by omega_using [hf₁]) (by omega_using [hf₁])
      rwa [sc0] at this
    · exact sc_disj hz (.inl (by simp only [It.hvO]; omega_using [])) (by omega_using [hf₁]) (by simp only [It.hvO]; omega_using [hf₁])
    · exact sc_disj hz (.inl (by simp only [It.blkO, It.hvO]; omega_using [])) (by omega_using [hf₁])
        (by simp only [It.blkO, It.hvO]; omega_using [hf₁, hDB])
    · exact (tsc (by omega_using [hf₁])).symm
  have dpad : ∀ r ∈ rs, Region.Disjoint ⟨blk P s₀ + BitVec.ofNat 64 P.D, P.B - P.D⟩ r := by
    intro r hr
    have e : blk P s₀ + BitVec.ofNat 64 P.D = sc s₀ + BitVec.ofNat 64 (P.blkO + P.D) := Offset.add_add _ _ _
    rw [e]
    rcases hrs r hr with rfl | rfl | rfl | rfl
    · have := sc_disj (s₀ := s₀) hz (a := P.blkO + P.D) (n := P.B - P.D) (b := 0) (k := P.CW)
        (.inr (by simp only [It.blkO, It.hvO]; omega_using [])) (by simp only [It.blkO, It.hvO]; omega_using [hf₁, hDB]) (by omega_using [hf₁])
      rwa [sc0] at this
    · exact sc_disj hz (.inr (by simp only [It.blkO]; omega_using [])) (by simp only [It.blkO, It.hvO]; omega_using [hf₁, hDB])
        (by simp only [It.hvO]; omega_using [hf₁])
    · exact sc_disj hz (.inr (by omega_using [])) (by simp only [It.blkO, It.hvO]; omega_using [hf₁, hDB])
        (by simp only [It.blkO, It.hvO]; omega_using [hf₁, hDB])
    · exact (tsc (by simp only [It.blkO, It.hvO]; omega_using [hf₁, hDB])).symm
  refine ⟨hrd, hwr, hsp, by rw [hg _ (by simp)]; exact h.s1, by rw [hg _ (by simp)]; exact h.s2,
    by rw [hg _ (by simp)]; exact h.s3, by rw [hg _ (by simp)]; exact h.s4, by rw [hg _ (by simp)]; exact h.s5,
    hc, fun r hr => by rw [hg r (by simp only [List.mem_append]; exact .inr hr)]; exact h.nv r hr,
    h.fr.trans (hf.sub hsub), h.saved.frame_in (lo := P.CW) (n := 56) (fun q hq => by
      simp only [It.saved, It.so, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_using []) hf dsv, ?_⟩
  rw [← h.pad]
  exact VG.Proof.Pbkdf2.Memory.frame_bytesAt hf dpad (by omega_using [hB])

end

/-! ## The pieces of a step -/

theorem hv_eq (P : It) (s₀ : State) : hv P s₀ = sc s₀ + BitVec.ofNat 64 (P.CW + 56) := rfl
theorem blk_eq (P : It) (s₀ : State) : blk P s₀ = sc s₀ + BitVec.ofNat 64 (P.CW + 56 + P.N) := rfl

/-- The hash value and the block are disjoint. -/
theorem hv_blk (hz : Sizes P Wi) : Region.Disjoint ⟨hv P s₀, P.N⟩ ⟨blk P s₀, P.B⟩ := by
  rw [hv_eq, blk_eq]
  exact sc_disj hz (.inl (by omega_using [])) (by have := hz.fits; omega_using [this]) (by have := hz.fits; omega_using [this])

theorem hv_sc (hz : Sizes P Wi) : Region.Disjoint ⟨hv P s₀, P.N⟩ ⟨sc s₀, P.CW⟩ := by
  rw [hv_eq]
  have := sc_disj (s₀ := s₀) hz (a := P.CW + 56) (n := P.N) (b := 0) (k := P.CW) (.inr (by omega_using []))
    (by have := hz.fits; omega_using [this]) (by have := hz.fits; omega_using [this])
  rwa [sc0] at this

theorem blk_sc (hz : Sizes P Wi) : Region.Disjoint ⟨blk P s₀, P.B⟩ ⟨sc s₀, P.CW⟩ := by
  rw [blk_eq]
  have := sc_disj (s₀ := s₀) hz (a := P.CW + 56 + P.N) (n := P.B) (b := 0) (k := P.CW) (.inr (by omega_using []))
    (by have := hz.fits; omega_using [this]) (by have := hz.fits; omega_using [this])
  rwa [sc0] at this

section
variable (hp : Pre P Wi s₀) (hz : Sizes P Wi)
include hp hz

theorem t_hv : Region.Disjoint (tR P s₀) ⟨hv P s₀, P.N⟩ :=
  hp.t_s.sub_right (by rw [hv_eq]; exact sc_sub (by have := hz.fits; omega_using [this]))

theorem t_blk : Region.Disjoint (tR P s₀) ⟨blk P s₀, P.B⟩ :=
  hp.t_s.sub_right (by rw [blk_eq]; exact sc_sub (by have := hz.fits; omega_using [this]))

theorem t_blkD : Region.Disjoint (tR P s₀) ⟨blk P s₀, P.D⟩ :=
  (t_blk hp hz).sub_right (Region.sub_prefix (Nat.le_of_lt hz.DB))

theorem hv_in {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    InRegions (s.rd ++ s.wr) (hv P s₀) P.N :=
  ⟨scR Wi s₀, by rw [hrd, hwr, hp.rd, hp.wr]; simp, by rw [hv_eq]; exact sc_contains hz (by have := hz.fits; omega_using [this])⟩

theorem blk_in {s : State} (hwr : s.wr = s₀.wr) {n : Nat} (hn : n ≤ P.B) : InRegions s.wr (blk P s₀) n :=
  ⟨scR Wi s₀, by rw [hwr, hp.wr]; simp, by rw [blk_eq]; exact sc_contains hz (by have := hz.fits; omega_using [hn, this])⟩

omit hz in
/-- Regions of the aligned scratch space are within the writable regions. -/
theorem sc_covers {rs : List Region}
    (h : ∀ r ∈ rs, ∃ a, r.base = sc s₀ + BitVec.ofNat 64 a ∧ a + r.len + 7 ≤ Wi) : RISCV64.Covers rs s₀.wr := by
  have hpd := pad_le (scr s₀)
  have hc : VG.Covers rs s₀.wr := VG.Covers.of_sub fun r hr => by
    obtain ⟨a, ha, hl⟩ := h r hr
    exact ⟨scR Wi s₀, by rw [hp.wr]; simp, Align.pad (scr s₀) + a, by rw [ha, sc_add], by dsimp only; omega_using [hpd, hl]⟩
  exact hc

/-- The hash value at `key + o` into the scratch space. -/
theorem load_ok {H : Md P.B P.N L} (hR : H.Reloc) {c : BitVec 64} {s : State} (h : St P Wi H s₀ c s) {o : Nat}
    (ho : o + P.N ≤ 2 * P.S) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', St P Wi H s₀ c s' → H.stateAt s'.mem (hv P s₀) = H.stateAt s₀.mem (key s₀ + BitVec.ofNat 64 o) →
      bytesAt s'.mem (blk P s₀) P.D = bytesAt s.mem (blk P s₀) P.D →
      bytesAt s'.mem (tp s₀) P.D = bytesAt s.mem (tp s₀) P.D → WP isa (.block rest) s' Q) :
    WP isa (.block (It.cp .s4 .s1 o 0 P.N ++ rest)) s Q := by
  have hN := hz.N64
  have hB := hz.B128
  have hS : P.S = P.N + P.B := rfl
  have hD := hz.DN
  have kS : (keyR P s₀).Disjoint (scR Wi s₀) := hp.k_s
  have kv : Region.Disjoint ⟨key s₀ + BitVec.ofNat 64 o, P.N⟩ ⟨hv P s₀, P.N⟩ :=
    (kS.sub_left (Offset.sub_base _ ho)).sub_right (by rw [hv_eq]; exact sc_sub (by have := hz.fits; omega_using [this]))
  refine cp_ok (by decide) (by decide) o 0 P.N (by omega_using [ho, hN, hB, hS]) (by omega_using [hN]) rest s Q
    (fun j hj => by
      rw [h.s4, Offset.add_add]; exact in_key hp hz h.rd h.wr (by omega_using [ho, hj]))
    (fun j hj => by
      rw [h.s1, BitVec.add_zero, hv_eq]
      exact in_scr hp hz h.wr (by have := hz.fits; omega_using [this]) hj)
    (by
      rw [h.s4, h.s1, BitVec.add_zero]
      exact kv.sep (Region.contains_self _ _) (Region.contains_self _ _))
    fun s' g rd' wr' sp' m' => ?_
  rw [h.s4, h.s1, BitVec.add_zero] at m'
  have hf : Frame [⟨hv P s₀, P.N⟩] s.mem s'.mem := by
    rw [m']; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine k s' (h.frame hp hz (rd'.trans h.rd) (wr'.trans h.wr) (sp'.trans h.sp)
      (by rw [g _ (by decide)]; exact h.s6) (fun r hr => g r (by revert r; decide)) hf
      (by simp only [List.mem_singleton]; rintro r rfl; exact .inr (.inl rfl))) ?_ ?_ ?_
  · refine hR s₀.mem s'.mem _ _ fun i hi => ?_
    rw [m', writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega_using [hN]),
      bytesAt_getD' _ _ hi, Offset.add_add]
    refine h.fr.bytes (R := keyR P s₀) (fun r hr => ?_) (by simp only [hS]; omega_using [hN, hB])
      (show o + i < 2 * P.S by omega_using [ho, hi])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hp.k_t, kS]
  · exact VG.Proof.Pbkdf2.Memory.frame_bytesAt hf (by
      simp only [List.mem_singleton]; rintro r rfl
      exact ((hv_blk hz).sub_right (Region.sub_prefix (Nat.le_of_lt hz.DB))).symm) (by omega_using [hN, hD])
  · exact VG.Proof.Pbkdf2.Memory.frame_bytesAt hf (by
      simp only [List.mem_singleton]; rintro r rfl; exact t_hv hp hz) (by omega_using [hN, hD])

/-- `load_ok`, alone in its block. -/
theorem load_ok' {H : Md P.B P.N L} (hR : H.Reloc) {c : BitVec 64} {s : State} (h : St P Wi H s₀ c s) {o : Nat}
    (ho : o + P.N ≤ 2 * P.S) {Q : State → Prop}
    (k : ∀ s', St P Wi H s₀ c s' → H.stateAt s'.mem (hv P s₀) = H.stateAt s₀.mem (key s₀ + BitVec.ofNat 64 o) →
      bytesAt s'.mem (blk P s₀) P.D = bytesAt s.mem (blk P s₀) P.D →
      bytesAt s'.mem (tp s₀) P.D = bytesAt s.mem (tp s₀) P.D → Q s') :
    WP isa (.block (It.cp .s4 .s1 o 0 P.N)) s Q := by
  have := load_ok hp hz hR h ho (rest := []) (Q := Q) fun s' t e b tp => WP.block_nil (k s' t e b tp)
  rwa [List.append_nil] at this

/-- A call of the compression function on the block. -/
theorem cmp_ok {H : Md P.B P.N L} (hf : CalleeOk H P.CW P.cmpC) {c : BitVec 64} {s : State}
    (h : St P Wi H s₀ c s) {Q : State → Prop}
    (k : ∀ s', St P Wi H s₀ c s' →
      H.stateAt s'.mem (hv P s₀) =
        H.compress (H.stateAt s.mem (hv P s₀)) (H.tailBlock P.D (bytesAt s.mem (blk P s₀) P.D)) →
      bytesAt s'.mem (blk P s₀) P.D = bytesAt s.mem (blk P s₀) P.D →
      bytesAt s'.mem (tp s₀) P.D = bytesAt s.mem (tp s₀) P.D → Q s') :
    WP isa P.compressAt s Q := by
  have hN := hz.N64
  have hB := hz.B128
  have hfi := hz.fits
  have hDB := hz.DB
  have hD := hz.DN
  have hcv : RISCV64.Covers [⟨blk P s₀, P.B⟩, ⟨hv P s₀, P.N⟩, ⟨sc s₀, P.CW⟩] s₀.wr := by
    refine sc_covers hp fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, blk_eq P s₀, by dsimp only; omega_using [hfi]⟩
    · exact ⟨_, hv_eq P s₀, by dsimp only; omega_using [hfi]⟩
    · exact ⟨0, (sc0 s₀).symm, by dsimp only; omega_using [hfi]⟩
  have hcw : RISCV64.Covers [⟨hv P s₀, P.N⟩, ⟨sc s₀, P.CW⟩] s₀.wr := by
    refine sc_covers hp fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hv_eq P s₀, by dsimp only; omega_using [hfi]⟩
    · exact ⟨0, (sc0 s₀).symm, by dsimp only; omega_using [hfi]⟩
  refine compressAt_ok hf h.s1 h.s2 h.s3 (hv_sc hz) (hv_blk hz).symm (blk_sc hz) sc_al
    (by rw [h.rd, h.wr]; exact fun a n hi => (hcv a n hi).elim fun r ⟨hr, hc⟩ =>
      ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [h.wr]; exact hcw)
    fun s' rd' wr' cs' sp' f' e' => ?_
  have hblk : bytesAt s'.mem (blk P s₀) P.D = bytesAt s.mem (blk P s₀) P.D :=
    VG.Proof.Pbkdf2.Memory.frame_bytesAt f' (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact ((hv_blk hz).sub_right (Region.sub_prefix (Nat.le_of_lt hDB))).symm
      · exact (blk_sc hz).sub_left (Region.sub_prefix (Nat.le_of_lt hDB))) (by omega_using [hB, hDB])
  refine k s' (h.frame hp hz (rd'.trans h.rd) (wr'.trans h.wr) (sp'.trans h.sp)
      (by rw [cs' _ (by decide)]; exact h.s6) (fun r hr => cs' r (by revert r; decide)) f' (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        exacts [.inr (.inl rfl), .inl rfl])) ?_ hblk ?_
  · rw [e', Md.blockAt_eq H (Nat.le_of_lt hDB) h.pad]
  · exact VG.Proof.Pbkdf2.Memory.frame_bytesAt f' (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact t_hv hp hz
      · exact hp.t_s.sub_right (by rw [← sc0 s₀]; exact sc_sub (by omega_using [hfi]))) (by omega_using [hB, hDB])

/-- The digest of the hash value over the block's first `D` bytes. -/
theorem digest_ok {H : Md P.B P.N L} (hout : OutOk H P.D P.out) {c : BitVec 64} {s : State}
    (h : St P Wi H s₀ c s) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', St P Wi H s₀ c s' →
      bytesAt s'.mem (blk P s₀) P.D = (H.digest (H.stateAt s.mem (hv P s₀))).take P.D →
      bytesAt s'.mem (tp s₀) P.D = bytesAt s.mem (tp s₀) P.D → WP isa (.block rest) s' Q) :
    WP isa (.block (P.out ++ rest)) s Q := by
  have hDB := hz.DB
  have hD := hz.DN
  have hN := hz.N64
  have hl : ((H.digest (H.stateAt s.mem (hv P s₀))).take P.D).length = P.D := by
    rw [List.length_take, H.digest_length]; omega_using [hD]
  refine WP.block_append_iff.mpr (WP.mono (hout s (by rw [h.s1]; exact hv_in hp hz h.rd h.wr)
    (by rw [h.s3]; exact blk_in hp hz h.wr (Nat.le_of_lt hDB))
    (by rw [h.s1, h.s3]; exact (hv_blk hz).sub_right (Region.sub_prefix (Nat.le_of_lt hDB))))
    fun s' ⟨g, rd', wr', sp', m'⟩ => ?_)
  rw [h.s1, h.s3] at m'
  have hf : Frame [⟨blk P s₀, P.D⟩] s.mem s'.mem := by
    rw [m']; exact writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  refine k s' (h.frame hp hz (rd'.trans h.rd) (wr'.trans h.wr) (sp'.trans h.sp)
      (by rw [g _ (by decide) (by decide) (by decide)]; exact h.s6)
      (fun r hr => g r (by revert r; decide) (by revert r; decide) (by revert r; decide)) hf
      (by simp only [List.mem_singleton]; rintro r rfl; exact .inr (.inr (.inl rfl)))) ?_ ?_
  · rw [m']
    have := bytesAt_writeBytes_self s.mem (blk P s₀) ((H.digest (H.stateAt s.mem (hv P s₀))).take P.D)
      (by rw [hl]; omega_using [hD, hN])
    rwa [hl] at this
  · exact VG.Proof.Pbkdf2.Memory.frame_bytesAt hf (by
      simp only [List.mem_singleton]; rintro r rfl; exact t_blkD hp hz) (by omega_using [hD, hN])

/-- `T ← T ⊕ U` and the count. -/
theorem tail_ok {H : Md P.B P.N L} {c : BitVec 64} {s : State} (h : St P Wi H s₀ c s) {Q : State → Prop}
    (k : ∀ s', St P Wi H s₀ (c - 1) s' →
      bytesAt s'.mem (tp s₀) P.D = xorBytes (bytesAt s.mem (tp s₀) P.D) (bytesAt s.mem (blk P s₀) P.D) →
      bytesAt s'.mem (blk P s₀) P.D = bytesAt s.mem (blk P s₀) P.D → Q s') :
    WP isa (.block (P.xorT ++ ([.addi .s6 .s6 (-1)] : List Instr))) s Q := by
  have hDB := hz.DB
  have hD := hz.DN
  have hN := hz.N64
  have hfi := hz.fits
  rw [xorT_eq]
  refine xor_ok P.D (by omega_using [hD, hN]) _ s Q
    (fun j hj => by
      rw [h.s3, blk_eq]
      have := in_scr hp hz h.wr (a := P.CW + 56 + P.N) (n := P.B) (by omega_using [hfi]) (Nat.lt_trans hj hDB)
      exact ⟨_, List.mem_append_right _ this.choose_spec.1, this.choose_spec.2⟩)
    (fun j hj => by rw [h.s5]; exact in_t hp hz h.wr hj)
    (by rw [h.s5, h.s3]; exact (t_blkD hp hz).sep (Region.contains_self _ _) (Region.contains_self _ _))
    fun s' g rd' wr' sp' m' => ?_
  rw [h.s5, h.s3] at m'
  refine wp_subi (imm := 1) (by decide) fun s'' u => WP.block_nil ?_
  have hl : (xorBytes (bytesAt s.mem (tp s₀) P.D) (bytesAt s.mem (blk P s₀) P.D)).length = P.D := by
    simp [xorBytes, bytesAt_length]
  have hf : Frame [tR P s₀] s.mem s''.mem := by
    rw [u.mem, m']; exact writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  refine k s'' (h.frame hp hz (by rw [u.rd, rd', h.rd]) (by rw [u.wr, wr', h.wr]) (by rw [u.sp, sp', h.sp])
      (by rw [u.gpr, g _ (by decide) (by decide), h.s6]; rfl)
      (fun r hr => by
        rw [u.other r (by revert r; decide), g r (by revert r; decide) (by revert r; decide)]) hf
      (by simp only [List.mem_singleton]; rintro r rfl; exact .inr (.inr (.inr rfl)))) ?_ ?_
  · rw [u.mem, m']
    have := bytesAt_writeBytes_self s.mem (tp s₀)
      (xorBytes (bytesAt s.mem (tp s₀) P.D) (bytesAt s.mem (blk P s₀) P.D)) (by rw [hl]; omega_using [hD, hN])
    rwa [hl] at this
  · exact VG.Proof.Pbkdf2.Memory.frame_bytesAt hf (by
      simp only [List.mem_singleton]; rintro r rfl; exact (t_blkD hp hz).symm) (by omega_using [hD, hN])

end

/-! ## The loop -/

/-- A step, as the code computes it, from the key's inner and outer hash values. -/
abbrev stepM (P : It) (H : Md P.B P.N L) (s₀ : State) : List Byte → List Byte :=
  H.step P.D (H.stateAt s₀.mem (key s₀)) (H.stateAt s₀.mem (key s₀ + BitVec.ofNat 64 P.S))

/-- The loop invariant, with `r` steps left. -/
structure Inv (P : It) (Wi : Nat) (H : Md P.B P.N L) (s₀ : State) (r : Nat) (s : State) : Prop
    extends St P Wi H s₀ (BitVec.ofNat 64 r) s where
  le : r ≤ nn s₀
  val : Spec.Pbkdf2.iterate (stepM P H s₀) (nn s₀) (bytesAt s₀.mem (up s₀) P.D) (bytesAt s₀.mem (tp s₀) P.D) =
    Spec.Pbkdf2.iterate (stepM P H s₀) r (bytesAt s.mem (blk P s₀) P.D) (bytesAt s.mem (tp s₀) P.D)

theorem ofNat_pred {r : Nat} (hr : 0 < r) : BitVec.ofNat 64 r - 1 = BitVec.ofNat 64 (r - 1) := by
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat hr]

section
variable (hp : Pre P Wi s₀) (hz : Sizes P Wi)
include hp hz

theorem body_ok {H : Md P.B P.N L} (hR : H.Reloc) (hf : CalleeOk H P.CW P.cmpC) (hout : OutOk H P.D P.out)
    {r : Nat} (hr : 0 < r) {s : State} (h : Inv P Wi H s₀ r s) :
    WP isa P.body s (Inv P Wi H s₀ (r - 1)) := by
  have hS : P.S = P.N + P.B := rfl
  unfold It.body
  refine WP.seq (load_ok' hp hz hR h.toSt (o := 0) (by omega_using [hS]) fun s₁ t₁ e₁ b₁ tp₁ => ?_)
  refine WP.seq (cmp_ok hp hz hf t₁ fun s₂ t₂ e₂ b₂ tp₂ => ?_)
  refine WP.seq (digest_ok hp hz hout t₂ fun s₃ t₃ b₃ tp₃ =>
    load_ok' hp hz hR t₃ (o := P.S) (by omega_using [hS]) fun s₄ t₄ e₄ b₄ tp₄ => ?_)
  refine WP.seq (cmp_ok hp hz hf t₄ fun s₅ t₅ e₅ b₅ tp₅ => ?_)
  rw [List.append_assoc]
  refine digest_ok hp hz hout t₅ fun s₆ t₆ b₆ tp₆ => tail_ok hp hz t₆ fun s₇ t₇ tp₇ b₇ => ?_
  -- The new `U` and `T`.
  have hu : bytesAt s₇.mem (blk P s₀) P.D = stepM P H s₀ (bytesAt s.mem (blk P s₀) P.D) := by
    rw [b₇, b₆, e₅, e₄, b₄, b₃, e₂, e₁, b₁, BitVec.add_zero]
    rfl
  have ht : bytesAt s₇.mem (tp s₀) P.D =
      xorBytes (bytesAt s.mem (tp s₀) P.D) (stepM P H s₀ (bytesAt s.mem (blk P s₀) P.D)) := by
    rw [tp₇, tp₆, tp₅, tp₄, tp₃, tp₂, tp₁, ← hu, b₇, b₆]
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega_using [hr]⟩
  have e := ofNat_pred (Nat.succ_pos r')
  rw [Nat.succ_sub_one] at e
  refine ⟨by rw [Nat.add_sub_cancel, ← e]; exact t₇, by have := h.le; omega_using [this], ?_⟩
  rw [h.val, Nat.add_sub_cancel, hu, ht]
  rfl

end

end VG.Proof.Pbkdf2.RISCV64

end

end


/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on RISC-V

The prologue aligns `scratch`, saves our caller's `ra` and `s1`–`s6` there,
sets up our registers, zero-extends `n`, and lays out the block: `U`, then
the padding (`prologue_ok`, which establishes the loop invariant with `n`
steps left); the loop runs the steps (`loop_ok`, `Iterate.lean`); the
epilogue restores the registers, and `Md.iterate_hmac` turns the iteration
of two compressions per step into PBKDF2's (`epilogue_ok`). `correct`
composes them, for any hash function and compression function `HashOk`
describes.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_li wp_mv wp_addi wp_subi wp_andi wp_srl wp_sll eval_zero eval_nonzero
  ofNat_beq_zero)
open VG.Impl.Pbkdf2.RISCV64 (It mov)
open VG.Proof.MdStream (Md)
open VG.WriteBytes (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Pbkdf2 (xorBytes)
open Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_writeBytes_self)

variable {P : It} {Wi : Nat} {s₀ : State} {L : Nat}

/-- `(x << 32) >> 32` is the low 32 bits of `x`. -/
theorem zext32 (x : BitVec 64) : x <<< 32 >>> 32 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega_using []

theorem nn_lt (s₀ : State) : nn s₀ < 2 ^ 32 := ((s₀.gpr .a2).setWidth 32).isLt

section
variable (hp : Pre P Wi s₀) (hz : Sizes P Wi)
include hp hz

theorem loop_ok {H : Md P.B P.N L} (hR : H.Reloc) (hf : CalleeOk H P.CW P.cmpC) (hout : OutOk H P.D P.out)
    {n : Nat} {s : State} (h : Inv P Wi H s₀ n s) :
    WP isa (.ite (.zero .s6) (.block []) (.loop P.body (.nonzero .s6))) s (Inv P Wi H s₀ 0) := by
  have hlt : n < 2 ^ 64 := by have := h.le; have := nn_lt s₀; omega_arith
  refine WP.ite (decide (n = 0)) (by rw [eval_zero, h.s6, ofNat_beq_zero hlt]) (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega_using [hb]⟩
    refine WP.loop (M := isa) (fun m s => Inv P Wi H s₀ (m + 1) s)
      (fun m s hs' => WP.mono (body_ok hp hz hR hf hout (Nat.succ_pos m) hs') fun s' hi => ?_) m s h
    have hlt' : m < 2 ^ 64 := by have := hi.le; have := nn_lt s₀; omega_arith
    have hz' : isa.eval (.nonzero .s6) s' = some (decide (m ≠ 0)) := by
      rw [eval_nonzero, hi.s6, Nat.succ_sub_one, bne, ofNat_beq_zero hlt']; simp
    cases m with
    | zero => exact .inl ⟨by rw [hz']; rfl, hi⟩
    | succ m => exact .inr ⟨by rw [hz']; simp, m, by omega_using [], hi⟩

end

theorem saved_fits (hz : Sizes P Wi) : Spill.Fits P.saved := by
  have := hz.CW8
  have := hz.CWle
  refine ⟨fun q hq => ?_, ?_⟩
  · simp only [It.saved, It.so, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith
  · simp only [It.saved, It.so, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, List.nodup_nil, and_true, not_false_eq_true]
    omega_using []

theorem saved_in : ∀ q ∈ P.saved, P.CW ≤ q.2 ∧ q.2 + 8 ≤ P.CW + 56 := by
  intro q hq
  simp only [It.saved, It.so, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_using []

theorem ofInt7 : BitVec.ofNat 64 7 = BitVec.ofInt 64 7 := rfl

/-- After the entry block: `n` zero-extended in `a2`. -/
structure Entry (s₀ s : State) : Prop where
  a2 : s.gpr .a2 = BitVec.ofNat 64 (nn s₀)
  other : ∀ r, r ≠ .a2 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem entry_ok (s₀ : State) : WP isa (.block It.entry) s₀ (Entry s₀) :=
  wp_sll (by decide) fun s₁ u₁ => wp_srl (by decide) fun s₂ u₂ => WP.block_nil
    ⟨by rw [u₂.gpr, u₁.gpr, zext32], fun r h => by rw [u₂.other r h, u₁.other r h],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩

section
variable (hp : Pre P Wi s₀) (hz : Sizes P Wi)
include hp hz

/-- The prologue: the loop invariant with `n` steps left. -/
theorem prologue_ok {H : Md P.B P.N L} (hpad : P.pad.map (BitVec.ofNat 8) = H.tailPad P.D) {e : State}
    (he : Entry s₀ e) :
    WP isa (.block P.prologue) e (Inv P Wi H s₀ (nn s₀)) := by
  have hN := hz.N64
  have hB := hz.B128
  have hDB := hz.DB
  have hD := hz.DN
  have hfi := hz.fits
  have hW := hz.W
  have hCW := hz.CWle
  have hpd := pad_le (scr s₀)
  simp only [It.prologue, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_addi (imm := 7) (by decide) fun s₁ u₁ => wp_andi (by decide) fun s₂ u₂ => ?_
  have a4₂ : s₂.gpr .a4 = sc s₀ := by rw [u₂.gpr, u₁.gpr, he.other _ (by decide), ofInt7, Align.align_eq]
  have g₂ : ∀ r, r ≠ .a4 → r ≠ .a2 → s₂.gpr r = s₀.gpr r := fun r h h' => by
    rw [u₂.other r h, u₁.other r h, he.other r h']
  show WP isa (.block (Spill.saveCode .a4 P.saved ++ _)) s₂ _
  refine Spill.save_ok (by rw [a4₂]; exact sc_al) (saved_fits hz).1
    (fun q hq => ⟨scR Wi s₀, by rw [u₂.wr, u₁.wr, he.wr, hp.wr]; simp, by
      rw [a4₂]; exact sc_contains hz (by have := saved_in q hq; omega_using [hfi, this])⟩) ?_
  refine wp_mv fun s₄ u₄ => wp_addi (by simp only [It.hvO]; omega_using [hCW]) fun s₅ u₅ =>
    wp_addi (by simp only [It.blkO, It.hvO]; omega_using [hN, hCW]) fun s₆ u₆ => wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ =>
    wp_mv fun s₁₀ u₁₀ => ?_
  -- The registers.
  have G6 : ∀ r, r ≠ .a4 → r ≠ .s2 → r ≠ .s1 → r ≠ .s3 → r ≠ .a2 → s₆.gpr r = s₀.gpr r :=
    fun r h0 h1 h2 h3 ha => (u₆.other r h3).trans ((u₅.other r h2).trans ((u₄.other r h1).trans (g₂ r h0 ha)))
  have G8 : ∀ r, r ≠ .a4 → r ≠ .s2 → r ≠ .s1 → r ≠ .s3 → r ≠ .s4 → r ≠ .s5 → r ≠ .a2 →
      s₈.gpr r = s₀.gpr r :=
    fun r h0 h1 h2 h3 h4 h5 ha => (u₈.other r h5).trans ((u₇.other r h4).trans (G6 r h0 h1 h2 h3 ha))
  have G : ∀ r, r ≠ .a4 → r ≠ .s2 → r ≠ .s1 → r ≠ .s3 → r ≠ .s4 → r ≠ .s5 → r ≠ .s6 → r ≠ .a2 →
      s₁₀.gpr r = s₀.gpr r := fun r h0 h1 h2 h3 h4 h5 h6 ha =>
    (u₁₀.other r h6).trans (G8 r h0 h1 h2 h3 h4 h5 ha)
  have a4₄ : s₄.gpr .a4 = sc s₀ := (u₄.other _ (by decide)).trans a4₂
  have T : ∀ r, r ≠ .s4 → r ≠ .s5 → r ≠ .s6 → s₁₀.gpr r = s₆.gpr r := fun r h4 h5 h6 =>
    (u₁₀.other r h6).trans ((u₈.other r h5).trans (u₇.other r h4))
  have e2 : s₁₀.gpr .s2 = sc s₀ := by
    rw [T _ (by decide) (by decide) (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
    exact a4₂
  have e1 : s₁₀.gpr .s1 = hv P s₀ := by
    rw [T _ (by decide) (by decide) (by decide), u₆.other _ (by decide), u₅.gpr, a4₄]
  have e3 : s₁₀.gpr .s3 = blk P s₀ := by
    rw [T _ (by decide) (by decide) (by decide), u₆.gpr, u₅.other _ (by decide), a4₄]
  have e4 : s₁₀.gpr .s4 = key s₀ := by
    rw [u₁₀.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      G6 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  have e5 : s₁₀.gpr .s5 = tp s₀ := by
    rw [u₁₀.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      G6 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  have e6 : s₁₀.gpr .s6 = BitVec.ofNat 64 (nn s₀) := by
    rw [u₁₀.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide)]
    exact (u₂.other _ (by decide)).trans ((u₁.other _ (by decide)).trans he.a2)
  have ea1 : s₁₀.gpr .a1 = up s₀ :=
    G _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- The memory and regions.
  have m₁₀ : s₁₀.mem = Spill.saveMem s₀.mem (sc s₀) s₂.gpr P.saved := by
    rw [u₁₀.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
    show Spill.saveMem s₂.mem (s₂.gpr .a4) s₂.gpr P.saved = _
    rw [u₂.mem, u₁.mem, he.mem, a4₂]
  have rd₁₀ : s₁₀.rd = s₀.rd := by
    rw [u₁₀.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd]; exact u₂.rd.trans (u₁.rd.trans he.rd)
  have wr₁₀ : s₁₀.wr = s₀.wr := by
    rw [u₁₀.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr]; exact u₂.wr.trans (u₁.wr.trans he.wr)
  have sp₁₀ : s₁₀.sp = s₀.sp := by
    rw [u₁₀.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp]; exact u₂.sp.trans (u₁.sp.trans he.sp)
  have eD : blk P s₀ + BitVec.ofNat 64 P.D = sc s₀ + BitVec.ofNat 64 (P.blkO + P.D) := Offset.add_add _ _ _
  have S1 : Region.Sub ⟨sc s₀ + BitVec.ofNat 64 P.CW, 56⟩ (scR Wi s₀) := sc_sub (by omega_using [hfi])
  have S2 : Region.Sub ⟨blk P s₀, P.D⟩ (scR Wi s₀) := by
    rw [blk_eq]; exact sc_sub (by omega_using [hDB, hfi])
  have S3 : Region.Sub ⟨blk P s₀ + BitVec.ofNat 64 P.D, P.B - P.D⟩ (scR Wi s₀) := by
    rw [eD]; exact sc_sub (by simp only [It.blkO, It.hvO]; omega_using [hDB, hfi])
  have uB : Region.Disjoint ⟨up s₀, P.D⟩ ⟨blk P s₀, P.D⟩ := hp.u_s.sub_right S2
  -- `U` into the block, then the padding.
  rw [padCode_eq, ← List.append_nil (bytesCode P.pad P.D P.pad.length)]
  refine cp_ok (src := .a1) (dst := .s3) (by decide) (by decide) 0 0 P.D (by omega_using [hB, hDB]) (by omega_using [hB, hDB]) _ s₁₀ _
    (fun k hk => by
      rw [ea1, BitVec.add_zero, rd₁₀, wr₁₀, hp.rd]
      exact ⟨uR P s₀, by simp, Offset.contains_base _ hk (by omega_using [hB, hDB, hk])⟩)
    (fun k hk => by
      rw [e3, BitVec.add_zero, blk_eq]
      exact in_scr hp hz wr₁₀ (a := P.CW + 56 + P.N) (n := P.B) (by omega_using [hfi]) (by omega_using [hDB, hk]))
    (by rw [ea1, e3, BitVec.add_zero, BitVec.add_zero]
        exact uB.sep (Region.contains_self _ _) (Region.contains_self _ _))
    fun s' g' rd' wr' sp' m' => ?_
  rw [e3, ea1, BitVec.add_zero, BitVec.add_zero, m₁₀] at m'
  refine bytes_ok P.pad (fun i hi => by have := hz.padV i hi; omega_using [this]) P.D P.pad.length (Nat.le_refl _)
    (by rw [hz.padL]; omega_using [hB, hDB]) [] s' _
    (fun k hk => by
      rw [g' _ (by decide), e3, blk_eq, Offset.add_add]
      exact in_scr hp hz (wr'.trans wr₁₀) (a := P.CW + 56 + P.N) (n := P.B) (by omega_using [hfi])
        (by rw [hz.padL] at hk; omega_using [hk]))
    fun s'' g'' rd'' wr'' sp'' m'' => WP.block_nil ?_
  rw [g' _ (by decide), e3, List.take_length, m'] at m''
  generalize hM₁ : Spill.saveMem s₀.mem (sc s₀) s₂.gpr P.saved = M₁ at m''
  generalize hM₂ : writeBytes M₁ (blk P s₀) (bytesAt M₁ (up s₀) P.D) = M₂ at m''
  have hl : (P.pad.map (BitVec.ofNat 8)).length = P.B - P.D := by rw [List.length_map, hz.padL]
  have f₁ : Frame [⟨sc s₀ + BitVec.ofNat 64 P.CW, 56⟩] s₀.mem M₁ := by
    rw [← hM₁]; exact Spill.saveMem_frame saved_in (by omega_using [hCW]) _ _ _
  have f₂ : Frame [⟨blk P s₀, P.D⟩] M₁ M₂ := by
    rw [← hM₂]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have f₃ : Frame [⟨blk P s₀ + BitVec.ofNat 64 P.D, P.B - P.D⟩] M₂ s''.mem := by
    rw [m'']; exact writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have sub : ∀ {R : Region}, Region.Sub R (scR Wi s₀) → ∀ r ∈ [R], ∃ r' ∈ [tR P s₀, scR Wi s₀], Region.Sub r r' :=
    fun hR r hr => ⟨scR Wi s₀, by simp, by rw [List.mem_singleton.mp hr]; exact hR⟩
  have one : ∀ {R R' : Region}, Region.Disjoint R' R → ∀ r ∈ [R], Region.Disjoint R' r :=
    fun h r hr => by rw [List.mem_singleton.mp hr]; exact h
  have dsv₂ : Region.Disjoint ⟨sc s₀ + BitVec.ofNat 64 P.CW, 56⟩ ⟨blk P s₀, P.D⟩ :=
    sc_disj hz (.inl (by simp only [It.blkO, It.hvO]; omega_using [])) (by omega_using [hfi]) (by simp only [It.blkO, It.hvO]; omega_using [hDB, hfi])
  have dsv₃ : Region.Disjoint ⟨sc s₀ + BitVec.ofNat 64 P.CW, 56⟩ ⟨blk P s₀ + BitVec.ofNat 64 P.D, P.B - P.D⟩ := by
    rw [eD]; exact sc_disj hz (.inl (by simp only [It.blkO, It.hvO]; omega_using [])) (by omega_using [hfi])
      (by simp only [It.blkO, It.hvO]; omega_using [hDB, hfi])
  have d₂₃ : Region.Disjoint ⟨blk P s₀, P.D⟩ ⟨blk P s₀ + BitVec.ofNat 64 P.D, P.B - P.D⟩ := by
    rw [eD]; exact sc_disj hz (.inl (by simp only [It.blkO]; omega_using [])) (by simp only [It.blkO, It.hvO]; omega_using [hDB, hfi])
      (by simp only [It.blkO, It.hvO]; omega_using [hDB, hfi])
  have tB : ∀ {M M' : Mem} {R : Region}, Frame [R] M M' → Region.Sub R (scR Wi s₀) →
      bytesAt M' (tp s₀) P.D = bytesAt M (tp s₀) P.D := fun hf hR =>
    VG.Proof.Pbkdf2.Memory.frame_bytesAt hf (one (hp.t_s.sub_right hR)) (by omega_using [hB, hDB])
  have saved₁ : Spill.Saved (sc s₀) s₀.gpr P.saved M₁ := by
    rw [← hM₁]
    intro q hq
    rw [Spill.saveMem_saved (saved_fits hz) s₀.mem (sc s₀) s₂.gpr q hq]
    simp only [It.saved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact g₂ _ (by simp) (by simp)
  have blkU : bytesAt s''.mem (blk P s₀) P.D = bytesAt s₀.mem (up s₀) P.D := by
    rw [VG.Proof.Pbkdf2.Memory.frame_bytesAt f₃ (one d₂₃) (by omega_using [hB, hDB])]
    have := bytesAt_writeBytes_self M₁ (blk P s₀) (bytesAt M₁ (up s₀) P.D) (by rw [bytesAt_length]; omega_using [hB, hDB])
    rw [bytesAt_length, hM₂] at this
    rw [this]
    exact VG.Proof.Pbkdf2.Memory.frame_bytesAt f₁ (one (hp.u_s.sub_right S1)) (by omega_using [hB, hDB])
  exact {
    rd := rd''.trans (rd'.trans rd₁₀)
    wr := wr''.trans (wr'.trans wr₁₀)
    sp := sp''.trans (sp'.trans sp₁₀)
    s1 := by rw [g'' _ (by decide), g' _ (by decide), e1]
    s2 := by rw [g'' _ (by decide), g' _ (by decide), e2]
    s3 := by rw [g'' _ (by decide), g' _ (by decide), e3]
    s4 := by rw [g'' _ (by decide), g' _ (by decide), e4]
    s5 := by rw [g'' _ (by decide), g' _ (by decide), e5]
    s6 := by rw [g'' _ (by decide), g' _ (by decide), e6]
    nv := fun r hr => by
      rw [g'' r (by revert r; decide), g' r (by revert r; decide)]
      exact G r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
    fr := (f₁.sub (sub S1)).trans ((f₂.sub (sub S2)).trans (f₃.sub (sub S3)))
    saved := (saved₁.frame_in saved_in f₂ (one dsv₂)).frame_in saved_in f₃ (one dsv₃)
    pad := by
      rw [m'']
      have := bytesAt_writeBytes_self M₂ (blk P s₀ + BitVec.ofNat 64 P.D) (P.pad.map (BitVec.ofNat 8))
        (by rw [hl]; omega_using [hB])
      rw [hl] at this
      rw [this, hpad]
    le := Nat.le_refl _
    val := by rw [blkU, tB f₃ S3, tB f₂ S2, tB f₁ S1] }

end

/-- The final `T` is PBKDF2's, for a key as the contract requires. -/
theorem post_eq {H : Md P.B P.N L} {S : StreamingHash} {iv : H.HV} (hl : H.Link S iv P.D) {m : Mem}
    (hT : bytesAt m (tp s₀) P.D =
      Spec.Pbkdf2.iterate (stepM P H s₀) (nn s₀) (bytesAt s₀.mem (up s₀) P.D) (bytesAt s₀.mem (tp s₀) P.D))
    {k0 : List Byte} (hk : k0.length = S.H.blockSize) (hi : S.Repr s₀.mem (key s₀) (xorPad k0 ipad))
    (ho : S.Repr s₀.mem (key s₀ + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad)) :
    bytesAt m (tp s₀) S.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) (nn s₀) (bytesAt s₀.mem (up s₀) S.digestBytes)
        (bytesAt s₀.mem (tp s₀) S.digestBytes) := by
  have hB : 0 < P.B := by have hl_DL := hl.DL; omega_using [hl_DL]
  rw [hl.hB] at hk
  rw [hl.hS] at ho
  have li : (xorPad k0 ipad).length = P.B := by simp [xorPad, hk]
  have lo : (xorPad k0 opad).length = P.B := by simp [xorPad, hk]
  have ei := Md.stateAt_of_repr hB li (hl.repr _ _ _ hi)
  have eo := Md.stateAt_of_repr hB lo (hl.repr _ _ _ ho)
  rw [hl.hD]
  refine hT.trans (Md.iterate_congr (fun u hu => ?_) (fun u => Md.step_length H hl.DN _ _ u) _ _ _
    (bytesAt_length _ _ _)).symm
  rw [Md.hmac_step hl hk hu, ei, eo]

theorem restList_ok (hz : Sizes P Wi) : ∀ q ∈ P.restList, q.2 % 8 = 0 ∧ q.2 < 2048 := by
  have := hz.CW8
  have := hz.CWle
  intro q hq
  simp only [It.restList, It.so, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith

theorem restList_sub : ∀ q ∈ P.restList, q ∈ P.saved := by
  intro q hq
  simp only [It.restList, It.saved, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem restorable : Spill.Restorable .s2 P.restList := by
  simp [Spill.Restorable, It.restList]

section
variable (hp : Pre P Wi s₀) (hz : Sizes P Wi)
include hp hz

theorem epilogue_ok {H : Md P.B P.N L} {S : StreamingHash} {iv : H.HV} (hl : H.Link S iv P.D) {s : State}
    (h : Inv P Wi H s₀ 0 s) :
    WP isa (.block P.restore) s fun s' => abiPreserved s₀ s' ∧ (iterK S Wi).post s₀ s' := by
  have hCW := hz.CWle
  have hfi := hz.fits
  refine WP.mono (Spill.restore_wp (b := .s2) (l := P.restList) sc_al h.s2 (restList_ok hz) restorable
    (fun q hq => ⟨scR Wi s₀, by rw [h.rd, h.wr, hp.rd, hp.wr]; simp,
      sc_contains hz (by
        have := saved_in q (restList_sub q hq); omega_using [hfi, this])⟩)
    (h.saved.sub restList_sub)) fun s' hr => ?_
  have keep : ∀ r, r ∈ P.restList.map Prod.fst ∨ s.gpr r = s₀.gpr r → s'.gpr r = s₀.gpr r :=
    fun r h' => hr.gpr_of h'
  refine ⟨⟨fun r hr' => keep r ?_, hr.sp.trans h.sp, keep _ (.inl (by simp [It.restList]))⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [.inr (h.nv _ (by simp)), .inl (by simp [It.restList]), .inl (by simp [It.restList]),
      .inl (by simp [It.restList]), .inl (by simp [It.restList]), .inl (by simp [It.restList]),
      .inl (by simp [It.restList]), .inr (h.nv _ (by simp)), .inr (h.nv _ (by simp)), .inr (h.nv _ (by simp)),
      .inr (h.nv _ (by simp)), .inr (h.nv _ (by simp))]
  · intro k0 hk hi ho
    rw [hr.mem]
    refine post_eq hl ?_ hk hi ho
    rw [h.val]; rfl

end

/-- What the iteration needs of a hash function: the sizes of the code, that
the padding is the hash function's, and that it is the hash function `S` of
the specification. -/
structure HashOk (P : It) (Wi : Nat) (S : StreamingHash) (H : Md P.B P.N L) (iv : H.HV) : Prop where
  sizes : Sizes P Wi
  pad : P.pad.map (BitVec.ofNat 8) = H.tailPad P.D
  reloc : H.Reloc
  out : OutOk H P.D P.out
  link : H.Link S iv P.D

theorem correct {P : It} {Wi : Nat} {S : StreamingHash} {H : Md P.B P.N L} {iv : H.HV}
    (ho : HashOk P Wi S H iv) (hf : CalleeOk H P.CW P.cmpC) {s₀ : State} (hp : Pre P Wi s₀) :
    WP isa P.iterate s₀ fun s' => abiPreserved s₀ s' ∧ (iterK S Wi).post s₀ s' := by
  unfold It.iterate It.main
  refine WP.seq (WP.mono (entry_ok s₀) fun e he => ?_)
  refine WP.seq (WP.mono (prologue_ok hp ho.sizes ho.pad he) fun s₁ h => ?_)
  exact WP.seq (WP.mono (loop_ok hp ho.sizes ho.reloc hf ho.out h) fun s₂ h₂ =>
    epilogue_ok hp ho.sizes ho.link h₂)

end VG.Proof.Pbkdf2.RISCV64
