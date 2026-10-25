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
  rw [sc_add]; exact Offset.sub_base _ (by have := pad_le (scr s₀); omega)

theorem sc_contains (hz : Sizes P Wi) {a n : Nat} (h : a + n + 7 ≤ Wi) :
    (scR Wi s₀).Contains (sc s₀ + BitVec.ofNat 64 a) n := by
  rw [sc_add]
  exact Offset.contains_base _ (by have := pad_le (scr s₀); omega)
    (by have := pad_le (scr s₀); have := hz.W; omega)

theorem sc_al : (sc s₀).toNat % 8 = 0 := Align.align_al _

/-- Two parts of the aligned scratch space. -/
theorem sc_disj (hz : Sizes P Wi) {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n ≤ Wi) (hb : b + k ≤ Wi) :
    Region.Disjoint ⟨sc s₀ + BitVec.ofNat 64 a, n⟩ ⟨sc s₀ + BitVec.ofNat 64 b, k⟩ :=
  Offset.disjoint _ h (by have := hz.W; omega) (by have := hz.W; omega)

theorem sc0 (s₀ : State) : sc s₀ + BitVec.ofNat 64 0 = sc s₀ := BitVec.add_zero _

/-! ## Between the pieces of a step -/

/-- The callee-saved registers our code never writes. -/
abbrev nvRegs : List Reg := [.s0, .s7, .s8, .s9, .s10, .s11]

theorem nv_pres : ∀ r ∈ nvRegs, r ∈ preserved := by decide

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
    rw [Offset.add_add]; exact sc_contains hz (by omega)⟩

theorem in_t {s : State} (hwr : s.wr = s₀.wr) {k : Nat} (hk : k < P.D) :
    InRegions s.wr (tp s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨tR P s₀, by rw [hwr, hp.wr]; simp, Offset.contains_base _ (by omega) (by have := hz.DN; have := hz.N64; omega)⟩

theorem in_key {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {k : Nat} (hk : k < 2 * P.S) :
    InRegions (s.rd ++ s.wr) (key s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨keyR P s₀, by rw [hrd, hwr, hp.rd]; simp,
    Offset.contains_base _ (by omega) (by have := hz.N64; have := hz.B128; simp only [It.S] at hk; omega)⟩

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
    · exact ⟨scR Wi s₀, by simp, by rw [← sc0 s₀]; exact sc_sub (by omega)⟩
    · exact ⟨scR Wi s₀, by simp, sc_sub (by simp only [It.hvO]; omega)⟩
    · exact ⟨scR Wi s₀, by simp, sc_sub (by simp only [It.blkO, It.hvO]; omega)⟩
    · exact ⟨tR P s₀, by simp, fun _ h => h⟩
  -- The saved registers and the padding are outside it.
  have dsv : ∀ r ∈ rs, Region.Disjoint ⟨sc s₀ + BitVec.ofNat 64 P.CW, 56⟩ r := by
    intro r hr
    rcases hrs r hr with rfl | rfl | rfl | rfl
    · have := sc_disj (s₀ := s₀) hz (a := P.CW) (n := 56) (b := 0) (k := P.CW) (.inr (by omega))
        (by omega) (by omega)
      rwa [sc0] at this
    · exact sc_disj hz (.inl (by simp only [It.hvO]; omega)) (by omega) (by simp only [It.hvO]; omega)
    · exact sc_disj hz (.inl (by simp only [It.blkO, It.hvO]; omega)) (by omega)
        (by simp only [It.blkO, It.hvO]; omega)
    · exact (tsc (by omega)).symm
  have dpad : ∀ r ∈ rs, Region.Disjoint ⟨blk P s₀ + BitVec.ofNat 64 P.D, P.B - P.D⟩ r := by
    intro r hr
    have e : blk P s₀ + BitVec.ofNat 64 P.D = sc s₀ + BitVec.ofNat 64 (P.blkO + P.D) := Offset.add_add _ _ _
    rw [e]
    rcases hrs r hr with rfl | rfl | rfl | rfl
    · have := sc_disj (s₀ := s₀) hz (a := P.blkO + P.D) (n := P.B - P.D) (b := 0) (k := P.CW)
        (.inr (by simp only [It.blkO, It.hvO]; omega)) (by simp only [It.blkO, It.hvO]; omega) (by omega)
      rwa [sc0] at this
    · exact sc_disj hz (.inr (by simp only [It.blkO]; omega)) (by simp only [It.blkO, It.hvO]; omega)
        (by simp only [It.hvO]; omega)
    · exact sc_disj hz (.inr (by omega)) (by simp only [It.blkO, It.hvO]; omega)
        (by simp only [It.blkO, It.hvO]; omega)
    · exact (tsc (by simp only [It.blkO, It.hvO]; omega)).symm
  refine ⟨hrd, hwr, hsp, by rw [hg _ (by simp)]; exact h.s1, by rw [hg _ (by simp)]; exact h.s2,
    by rw [hg _ (by simp)]; exact h.s3, by rw [hg _ (by simp)]; exact h.s4, by rw [hg _ (by simp)]; exact h.s5,
    hc, fun r hr => by rw [hg r (by simp only [List.mem_append]; exact .inr hr)]; exact h.nv r hr,
    h.fr.trans (hf.sub hsub), h.saved.frame_in (lo := P.CW) (n := 56) (fun q hq => by
      simp only [It.saved, It.so, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega) hf dsv, ?_⟩
  rw [← h.pad]
  exact VG.Proof.Pbkdf2.Memory.frame_bytesAt hf dpad (by omega)

end

/-! ## The pieces of a step -/

theorem hv_eq (P : It) (s₀ : State) : hv P s₀ = sc s₀ + BitVec.ofNat 64 (P.CW + 56) := rfl
theorem blk_eq (P : It) (s₀ : State) : blk P s₀ = sc s₀ + BitVec.ofNat 64 (P.CW + 56 + P.N) := rfl

/-- The hash value and the block are disjoint. -/
theorem hv_blk (hz : Sizes P Wi) : Region.Disjoint ⟨hv P s₀, P.N⟩ ⟨blk P s₀, P.B⟩ := by
  rw [hv_eq, blk_eq]
  exact sc_disj hz (.inl (by omega)) (by have := hz.fits; omega) (by have := hz.fits; omega)

theorem hv_sc (hz : Sizes P Wi) : Region.Disjoint ⟨hv P s₀, P.N⟩ ⟨sc s₀, P.CW⟩ := by
  rw [hv_eq]
  have := sc_disj (s₀ := s₀) hz (a := P.CW + 56) (n := P.N) (b := 0) (k := P.CW) (.inr (by omega))
    (by have := hz.fits; omega) (by have := hz.fits; omega)
  rwa [sc0] at this

theorem blk_sc (hz : Sizes P Wi) : Region.Disjoint ⟨blk P s₀, P.B⟩ ⟨sc s₀, P.CW⟩ := by
  rw [blk_eq]
  have := sc_disj (s₀ := s₀) hz (a := P.CW + 56 + P.N) (n := P.B) (b := 0) (k := P.CW) (.inr (by omega))
    (by have := hz.fits; omega) (by have := hz.fits; omega)
  rwa [sc0] at this

section
variable (hp : Pre P Wi s₀) (hz : Sizes P Wi)
include hp hz

theorem t_hv : Region.Disjoint (tR P s₀) ⟨hv P s₀, P.N⟩ :=
  hp.t_s.sub_right (by rw [hv_eq]; exact sc_sub (by have := hz.fits; omega))

theorem t_blk : Region.Disjoint (tR P s₀) ⟨blk P s₀, P.B⟩ :=
  hp.t_s.sub_right (by rw [blk_eq]; exact sc_sub (by have := hz.fits; omega))

theorem t_blkD : Region.Disjoint (tR P s₀) ⟨blk P s₀, P.D⟩ :=
  (t_blk hp hz).sub_right (Region.sub_prefix (Nat.le_of_lt hz.DB))

theorem hv_in {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    InRegions (s.rd ++ s.wr) (hv P s₀) P.N :=
  ⟨scR Wi s₀, by rw [hrd, hwr, hp.rd, hp.wr]; simp, by rw [hv_eq]; exact sc_contains hz (by have := hz.fits; omega)⟩

theorem blk_in {s : State} (hwr : s.wr = s₀.wr) {n : Nat} (hn : n ≤ P.B) : InRegions s.wr (blk P s₀) n :=
  ⟨scR Wi s₀, by rw [hwr, hp.wr]; simp, by rw [blk_eq]; exact sc_contains hz (by have := hz.fits; omega)⟩


omit hz in
/-- Regions of the aligned scratch space are within the writable regions. -/
theorem sc_covers {rs : List Region}
    (h : ∀ r ∈ rs, ∃ a, r.base = sc s₀ + BitVec.ofNat 64 a ∧ a + r.len + 7 ≤ Wi) : RISCV64.Covers rs s₀.wr := by
  have hpd := pad_le (scr s₀)
  have hc : VG.Covers rs s₀.wr := VG.Covers.of_sub fun r hr => by
    obtain ⟨a, ha, hl⟩ := h r hr
    exact ⟨scR Wi s₀, by rw [hp.wr]; simp, Align.pad (scr s₀) + a, by rw [ha, sc_add], by dsimp only; omega⟩
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
    (kS.sub_left (Offset.sub_base _ ho)).sub_right (by rw [hv_eq]; exact sc_sub (by have := hz.fits; omega))
  refine cp_ok (by decide) (by decide) o 0 P.N (by omega) (by omega) rest s Q
    (fun j hj => by
      rw [h.s4, Offset.add_add]; exact in_key hp hz h.rd h.wr (by omega))
    (fun j hj => by
      rw [h.s1, BitVec.add_zero, hv_eq]
      exact in_scr hp hz h.wr (by have := hz.fits; omega) hj)
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
    rw [m', writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
      bytesAt_getD' _ _ hi, Offset.add_add]
    refine h.fr.bytes (R := keyR P s₀) (fun r hr => ?_) (by simp only [hS]; omega)
      (show o + i < 2 * P.S by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hp.k_t, kS]
  · exact VG.Proof.Pbkdf2.Memory.frame_bytesAt hf (by
      simp only [List.mem_singleton]; rintro r rfl
      exact ((hv_blk hz).sub_right (Region.sub_prefix (Nat.le_of_lt hz.DB))).symm) (by omega)
  · exact VG.Proof.Pbkdf2.Memory.frame_bytesAt hf (by
      simp only [List.mem_singleton]; rintro r rfl; exact t_hv hp hz) (by omega)

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
    · exact ⟨_, blk_eq P s₀, by dsimp only; omega⟩
    · exact ⟨_, hv_eq P s₀, by dsimp only; omega⟩
    · exact ⟨0, (sc0 s₀).symm, by dsimp only; omega⟩
  have hcw : RISCV64.Covers [⟨hv P s₀, P.N⟩, ⟨sc s₀, P.CW⟩] s₀.wr := by
    refine sc_covers hp fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hv_eq P s₀, by dsimp only; omega⟩
    · exact ⟨0, (sc0 s₀).symm, by dsimp only; omega⟩
  refine compressAt_ok hf h.s1 h.s2 h.s3 (hv_sc hz) (hv_blk hz).symm (blk_sc hz)
    (by rw [h.rd, h.wr]; exact fun a n hi => (hcv a n hi).elim fun r ⟨hr, hc⟩ =>
      ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [h.wr]; exact hcw)
    fun s' rd' wr' cs' sp' f' e' => ?_
  have hblk : bytesAt s'.mem (blk P s₀) P.D = bytesAt s.mem (blk P s₀) P.D :=
    VG.Proof.Pbkdf2.Memory.frame_bytesAt f' (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact ((hv_blk hz).sub_right (Region.sub_prefix (Nat.le_of_lt hDB))).symm
      · exact (blk_sc hz).sub_left (Region.sub_prefix (Nat.le_of_lt hDB))) (by omega)
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
      · exact hp.t_s.sub_right (by rw [← sc0 s₀]; exact sc_sub (by omega))) (by omega)

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
    rw [List.length_take, H.digest_length]; omega
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
      (by rw [hl]; omega)
    rwa [hl] at this
  · exact VG.Proof.Pbkdf2.Memory.frame_bytesAt hf (by
      simp only [List.mem_singleton]; rintro r rfl; exact t_blkD hp hz) (by omega)

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
  refine xor_ok P.D (by omega) _ s Q
    (fun j hj => by
      rw [h.s3, blk_eq]
      have := in_scr hp hz h.wr (a := P.CW + 56 + P.N) (n := P.B) (by omega) (Nat.lt_trans hj hDB)
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
      (xorBytes (bytesAt s.mem (tp s₀) P.D) (bytesAt s.mem (blk P s₀) P.D)) (by rw [hl]; omega)
    rwa [hl] at this
  · exact VG.Proof.Pbkdf2.Memory.frame_bytesAt hf (by
      simp only [List.mem_singleton]; rintro r rfl; exact (t_blkD hp hz).symm) (by omega)

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
  refine WP.seq (load_ok' hp hz hR h.toSt (o := 0) (by omega) fun s₁ t₁ e₁ b₁ tp₁ => ?_)
  refine WP.seq (cmp_ok hp hz hf t₁ fun s₂ t₂ e₂ b₂ tp₂ => ?_)
  refine WP.seq (digest_ok hp hz hout t₂ fun s₃ t₃ b₃ tp₃ =>
    load_ok' hp hz hR t₃ (o := P.S) (by omega) fun s₄ t₄ e₄ b₄ tp₄ => ?_)
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
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have e := ofNat_pred (Nat.succ_pos r')
  rw [Nat.succ_sub_one] at e
  refine ⟨by rw [Nat.add_sub_cancel, ← e]; exact t₇, by have := h.le; omega, ?_⟩
  rw [h.val, Nat.add_sub_cancel, hu, ht]
  rfl

end

end VG.Proof.Pbkdf2.RISCV64
