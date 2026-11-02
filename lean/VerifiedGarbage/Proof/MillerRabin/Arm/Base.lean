module

public import VerifiedGarbage.Impl.MillerRabin.Arm.Round
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.KeyArrs
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.ByteWords

/-! # The Miller–Rabin round on ARMv7: the public parameters and the stages

`MP`: what two runs share (the working space, its length, `w` and the
frame). `In P σ`: the state `σ` the body starts from, after the push, with
the regions narrowed to the frame, the working space (`rS`) and the key
working space's view of it (`rK`, from `B = ws + 96`). `KS P σ A live V ls s`:
a stage of the body: what it keeps of `σ` (the stack pointer, the regions,
and all of memory but the arrays and header words the round may write,
`wJs` and `wDs`), the arrays `live` (read with `W = 2 w + 2` words) holding
`A` and the header words `ls` holding `V`. Montgomery multiplication is
ready at every stage (`KS.ready`), and the numbers of its working space are
the low `2 w` words of the key arrays (`numAt_val32`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout)

structure MP where
  ws : BitVec 32
  len : Nat
  w : Nat
  sp : BitVec 32

namespace MP

/-- The key working space's base, its words and its size. -/
abbrev B (P : MP) : BitVec 32 := P.ws + BitVec.ofNat 32 kOff
abbrev W (P : MP) : Nat := 2 * P.w + 2
abbrev Z (P : MP) : Nat := 8 * P.len - kOff
abbrev R (P : MP) : Nat := 2 ^ (64 * P.w)

abbrev rS (P : MP) : Region := ⟨State.addr P.ws, 8 * P.len⟩
abbrev rK (P : MP) : Region := ⟨State.addr P.B, P.Z⟩
abbrev rF (P : MP) : Region := ⟨State.addr P.sp, 56⟩

end MP

/-- The arrays of the key view. -/
abbrev nArr : Nat := 28

/-- The arrays and header words the round writes: Montgomery
multiplication's own, `x`, `y`, `−1` and the table. -/
abbrev wJs : List Nat := [2, 3, aX, aY, aM1, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
abbrev wDs : List Nat := [sE1, sE2, sT, sV, sF, sK, sQ, sR]

theorem wJs_lt : ∀ j ∈ wJs, 2 ≤ j ∧ j < nArr := by decide
theorem wDs_ok : ∀ d ∈ wDs, 88 ≤ d ∧ d + 4 ≤ 152 := by decide

/-- The candidate, the witness and the constants, from memory. -/
abbrev cOf (P : MP) (m : Mem) : Nat := numAt m (State.addr P.ws) P.w 0

structure In (P : MP) (σ : State) : Prop where
  sp : σ.sp = P.sp
  wr : σ.wr = [P.rF, P.rS, P.rK]
  fit : P.ws.toNat + 8 * P.len ≤ 2 ^ 32
  spFit : P.sp.toNat + 56 ≤ 2 ^ 32
  sep : P.rF.Disjoint P.rS
  w4 : 4 ≤ P.w
  w128 : P.w ≤ 128
  fits : arrAt P.w nArr ≤ 8 * P.len
  layout : Proof.Rsa.Mont.Layout σ.mem (State.addr P.ws) P.len
  width : wOf σ.mem (State.addr P.ws) = P.w
  inverse : ((word σ.mem (State.addr P.ws) (arrAt P.w 0)).toNat *
    (wordAt σ.mem (State.addr P.ws) Proof.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0
  c3 : 3 ≤ cOf P σ.mem
  codd : cOf P σ.mem % 2 = 1
  x5 : numAt σ.mem (State.addr P.ws) P.w 5 < cOf P σ.mem
  one : numAt σ.mem (State.addr P.ws) P.w 9 = P.R % cOf P σ.mem
  m1 : numAt σ.mem (State.addr P.ws) P.w 10 = cOf P σ.mem - P.R % cOf P σ.mem
  exp : numAt σ.mem (State.addr P.ws) P.w aE = Proof.MillerRabin.Round.exponent (cOf P σ.mem)
  low : σ.mem.readW (State.addr P.ws + BitVec.ofNat 64 (arrAt P.w aE + 8 * P.w)) 64 =
    BitVec.twoPow 64 ((Spec.Rsa.splitTwos (cOf P σ.mem - 1)).1 % 64)
  saved : σ.mem.readW (State.addr P.sp) 32 = P.ws

/-! ## Sizes -/

section
variable {P : MP} {σ : State}

theorem In.S_eq (_ : In P σ) : S P.W = 8 * (P.w + 2) := by simp only [S, MP.W]; omega_arith

theorem In.len (h : In P σ) : 256 + 28 * (8 * (P.w + 2)) ≤ 8 * P.len := by
  have := h.fits; simp only [arrAt, Proof.Rsa.Mont.hdrBytes, nArr] at this; omega_arith

theorem In.Z_le (h : In P σ) : P.Z ≤ 2 ^ 32 := by have := h.fit; have := h.len; simp only [MP.Z, kOff]; omega_arith

theorem In.B_toNat (h : In P σ) : P.B.toNat = P.ws.toNat + kOff := by
  have := h.fit; have := h.len
  simp only [MP.B, BitVec.toNat_add, BitVec.toNat_ofNat, kOff]; omega_arith

theorem In.addrB (h : In P σ) : State.addr P.B = State.addr P.ws + BitVec.ofNat 64 kOff :=
  addr_add (by have := h.fit; have := h.len; simp only [kOff]; omega_arith)

theorem In.nowrapB (h : In P σ) : P.B.toNat + P.Z ≤ 2 ^ 32 := by
  have := h.fit; have := h.len; rw [h.B_toNat]; simp only [MP.Z, kOff]; omega_arith

/-- The key view's arrays are the working space's. -/
theorem In.arr_eq (h : In P σ) (j : Nat) : kOff + arr P.W j = arrAt P.w j := by
  have := h.S_eq; simp only [arr, arrAt, hdr, kOff, Proof.Rsa.Mont.hdrBytes] at *; rw [this]; omega_arith

/-- Offsets from `B` of addresses at least 96 bytes past `ws`. -/
theorem In.ofsB (h : In P σ) {x : Addr} (hx : kOff ≤ ofs (State.addr P.ws) x) :
    ofs (State.addr P.B) x = ofs (State.addr P.ws) x - kOff := by
  rw [h.addrB]; simp only [ofs, kOff] at hx ⊢; bv_omega

/-- Offsets from `B` of the first 96 bytes past `ws`. -/
theorem In.ofsB_lo (h : In P σ) {d : Nat} (hd : d < kOff) : P.Z ≤ ofs (State.addr P.B) (off (State.addr P.ws) d) := by
  have := h.fit; have := h.len
  rw [h.addrB]; simp only [ofs, off, MP.Z, kOff] at hd ⊢
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := (State.addr P.ws).isLt
  omega_arith

theorem In.fitsK (h : In P σ) : arr P.W nArr ≤ P.Z := by
  have := h.arr_eq nArr; have := h.fits; simp only [MP.Z, kOff] at *; omega_arith

theorem In.off_eq (h : In P σ) (d : Nat) : off (State.addr P.B) d = off (State.addr P.ws) (kOff + d) := by
  simp only [off]; rw [h.addrB, Offset.add_add]

/-- Montgomery multiplication's number of array `j` is the low `2 w` words of the key array. -/
theorem In.numAt_val32 (h : In P σ) (m : Mem) (j : Nat) :
    numAt m (State.addr P.ws) P.w j = val32 m (State.addr P.B) (arr P.W j) (2 * P.w) := by
  unfold numAt
  rw [show State.addr P.ws + BitVec.ofNat 64 (arrAt P.w j) = off (State.addr P.ws) (arrAt P.w j) from rfl,
    ← h.arr_eq j, ← h.off_eq, show 8 * P.w = 4 * (2 * P.w) by omega_arith, read_eq_val32]

/-- A key number whose top words are zero is Montgomery multiplication's number. -/
theorem In.numAt_eq (h : In P σ) {m : Mem} {j : Nat} (hl : num m P.B P.W j < P.R) :
    numAt m (State.addr P.ws) P.w j = num m P.B P.W j := by
  rw [h.numAt_val32]
  have e : num m P.B P.W j = val32 m (State.addr P.B) (arr P.W j) (2 * P.w) +
      2 ^ (32 * (2 * P.w)) * val32 m (State.addr P.B) (arr P.W j + 4 * (2 * P.w)) 2 := by
    simp only [num, MP.W]; rw [val32_append]
  have hR : 2 ^ (32 * (2 * P.w)) = P.R := by simp only [MP.R]; rw [← Nat.mul_assoc]
  rw [hR] at e
  rw [e] at hl ⊢
  rcases Nat.eq_zero_or_pos (val32 m (State.addr P.B) (arr P.W j + 4 * (2 * P.w)) 2) with z | z
  · rw [z, Nat.mul_zero, Nat.add_zero]
  · have := Nat.le_mul_of_pos_right P.R z; omega_arith

theorem In.c_lt (h : In P σ) : cOf P σ.mem < P.R := by
  have := val32_lt σ.mem (State.addr P.B) (arr P.W 0) (2 * P.w)
  rw [← h.numAt_val32, show 32 * (2 * P.w) = 64 * P.w by omega_arith] at this
  exact this

end

/-! ## Stages -/

structure KS (P : MP) (σ : State) (A : Nat → Nat) (live : List Nat) (V : Nat → Nat) (ls : List Nat)
    (s : State) : Prop where
  pre : In P σ
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  keep : Keep P.B P.W wJs wDs σ.mem s.mem
  arrs : Arrs s.mem P.B P.W A live
  sl : ∀ d ∈ ls, slot s.mem P.B d = V d
  live_lt : ∀ j ∈ live, j < nArr
  ls_ok : ∀ d ∈ ls, d ∈ wDs

section
variable {P : MP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem In.ks (h : In P σ) : KS P σ (fun _ => 0) [] (fun _ => 0) [] σ :=
  ⟨h, rfl, rfl, rfl, Keep.refl _ _ _ _ _, Arrs.nil _ _ _ _, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

/-- The key view's context. -/
theorem KS.ws (h : KS P σ A live V ls s) (r7 : s.gpr .r7 = BitVec.ofNat 32 (S P.W)) (r8 : s.gpr .r8 = P.B)
    (r9 : s.gpr .r9 = BitVec.ofNat 32 P.W) : Ws s P.B P.Z P.W nArr :=
  ⟨h.pre.nowrapB, by rw [h.wr, h.pre.wr]; simp, h.pre.fitsK, by simp only [MP.W]; omega_arith,
    by have := h.pre.w128; simp only [MP.W]; omega_arith, r7, r8, r9⟩

/-- The same memory, other registers. -/
theorem KS.of_rest (h : KS P σ A live V ls s) {rs : List Reg} (r : Rest rs s t) (m : t.mem = s.mem) :
    KS P σ A live V ls t :=
  ⟨h.pre, r.sp.trans h.sp, r.rd.trans h.rd, r.wr.trans h.wr, m ▸ h.keep, m ▸ h.arrs, m ▸ h.sl, h.live_lt,
    h.ls_ok⟩

theorem KS.mono (h : KS P σ A live V ls s) {A' : Nat → Nat} {live' : List Nat} {V' : Nat → Nat}
    {ls' : List Nat} (hl : ∀ j ∈ live', j ∈ live ∧ A j = A' j) (hls : ∀ d ∈ ls', d ∈ ls ∧ V d = V' d) :
    KS P σ A' live' V' ls' s :=
  ⟨h.pre, h.sp, h.rd, h.wr, h.keep, fun j hj => (h.arrs j (hl j hj).1).trans (hl j hj).2,
    fun d hd => (h.sl d (hls d hd).1).trans (hls d hd).2, fun j hj => h.live_lt j (hl j hj).1,
    fun d hd => h.ls_ok d (hls d hd).1⟩

/-- Memory past the key view's start, and before it, keeps its value. -/
theorem KS.mem_out (h : KS P σ A live V ls s) {x : Addr} (hx : P.Z ≤ ofs (State.addr P.B) x) :
    s.mem x = σ.mem x := by
  have pre := h.pre
  have hS := pre.S_eq
  have hZ := pre.fitsK
  refine h.keep.out (Z := P.Z) (fun j hj => ?_) (fun d hd => ?_) hx
  · have := arr_end (w := P.W) (wJs_lt j hj).2
    omega_arith
  · have := wDs_ok d hd
    have : hdr ≤ arr P.W nArr := Nat.le_add_right _ _
    simp only [hdr] at this; omega_arith

/-- The frame's words keep their values. -/
theorem KS.frameWord (h : KS P σ A live V ls s) {o : Nat} (ho : o + 4 ≤ 56) :
    s.mem.readW (off (State.addr P.sp) o) 32 = σ.mem.readW (off (State.addr P.sp) o) 32 := by
  have pre := h.pre
  have spf := pre.spFit
  refine Mem.readW_congr fun i hi => h.mem_out ?_
  have hin : (P.rF).Contains (off (State.addr P.sp) o + BitVec.ofNat 64 i) 1 := by
    simp only [Region.Contains, off]
    rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    omega_arith
  have hout := pre.sep _ hin
  simp only [Region.Contains] at hout
  have len := pre.len
  rw [pre.ofsB (by simp only [ofs, kOff]; omega_arith)]
  simp only [ofs, MP.Z, kOff]; omega_arith

/-- The candidate keeps its value. -/
theorem KS.c_eq (h : KS P σ A live V ls s) : cOf P s.mem = cOf P σ.mem := by
  have pre := h.pre
  have hS := pre.S_eq
  have hZ := pre.Z_le
  have hK := pre.fitsK
  have h0 := arr_end (w := P.W) (show 0 < nArr by decide)
  rw [cOf, cOf, pre.numAt_val32, pre.numAt_val32]
  refine h.keep.val32 (fun r hr => ?_) (by omega_arith)
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨d', hd', rfl⟩
  · have := arr_end (w := P.W) (show 0 < j by have := (wJs_lt j hj).1; omega_arith)
    dsimp only; omega_arith
  · have := wDs_ok d' hd'
    have : hdr ≤ arr P.W 0 := Nat.le_add_right _ _
    simp only [hdr] at this; dsimp only; omega_arith

/-- Bytes of the header but words 23 to 31, and of array 0, keep their values. -/
theorem KS.mem_hdr (h : KS P σ A live V ls s) {d : Nat} (hd : d + 1 ≤ arrAt P.w 1) (hd2 : d < 184 ∨ 256 ≤ d) :
    s.mem (off (State.addr P.ws) d) = σ.mem (off (State.addr P.ws) d) := by
  have pre := h.pre
  have hS := pre.S_eq
  have len := pre.len
  have fit := pre.fit
  by_cases hlo : d < kOff
  · exact h.mem_out (pre.ofsB_lo hlo)
  · obtain ⟨e, rfl⟩ : ∃ e, d = kOff + e := ⟨d - kOff, by omega_arith⟩
    rw [← pre.off_eq]
    refine h.keep _ fun r hr => ?_
    rw [ofs_off0 _ (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes, kOff] at hd; omega_arith)]
    simp only [ranges, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨j, hj, rfl⟩ | ⟨d', hd', rfl⟩
    · have := pre.arr_eq 1
      have := arr_mono (w := P.W) (show 1 ≤ j by have := (wJs_lt j hj).1; omega_arith)
      dsimp only; omega_arith
    · have := wDs_ok d' hd'
      simp only [arrAt, Proof.Rsa.Mont.hdrBytes, kOff] at hd hd2
      dsimp only; omega_arith

/-- Reads of the header but words 23 to 31, and of array 0. -/
theorem KS.read_hdr (h : KS P σ A live V ls s) {d n : Nat} (hdn : d + n ≤ arrAt P.w 1) (hdn2 : d + n ≤ 184 ∨ 256 ≤ d) :
    s.mem.read (off (State.addr P.ws) d) n = σ.mem.read (off (State.addr P.ws) d) n := by
  refine Mem.read_congr fun i hi => ?_
  rw [show off (State.addr P.ws) d + BitVec.ofNat 64 i = off (State.addr P.ws) (d + i) by
    simp only [off]; rw [Offset.add_add]]
  exact h.mem_hdr (by omega_arith) (by omega_arith)

/-- `w`, from the header. -/
theorem KS.width (h : KS P σ A live V ls s) : wOf s.mem (State.addr P.ws) = P.w := by
  have e : s.mem.readW (off (State.addr P.ws) 48) 64 = σ.mem.readW (off (State.addr P.ws) 48) 64 := by
    simp only [Mem.readW, h.read_hdr (d := 48) (n := 8) (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_arith) (.inl (by decide))]
  exact (congrArg BitVec.toNat e).trans h.pre.width

/-- Montgomery multiplication is ready. -/
theorem KS.ready (h : KS P σ A live V ls s) (r0 : s.gpr .r0 = P.ws) : ArithmeticReady P.ws P.len P.w s := by
  have pre := h.pre
  have hS := pre.S_eq
  have len := pre.len
  have fit := pre.fit
  have a0 : arrAt P.w 0 = 256 := by simp [arrAt, Proof.Rsa.Mont.hdrBytes]
  have a1 : arrAt P.w 1 = 256 + 8 * (P.w + 2) := by simp [arrAt, Proof.Rsa.Mont.hdrBytes]
  have hr : ∀ d n, d + n ≤ arrAt P.w 1 → (d + n ≤ 184 ∨ 256 ≤ d) →
      s.mem.read (off (State.addr P.ws) d) n = σ.mem.read (off (State.addr P.ws) d) n :=
    fun d n h1 h2 => h.read_hdr h1 h2
  have hw : ∀ d, d + 8 ≤ 184 →
      s.mem.readW (off (State.addr P.ws) d) 64 = σ.mem.readW (off (State.addr P.ws) d) 64 :=
    fun d hd' => by simp only [Mem.readW, hr d 8 (by omega_arith) (.inl hd')]
  have width : wOf s.mem (State.addr P.ws) = wOf σ.mem (State.addr P.ws) :=
    congrArg BitVec.toNat (hw 48 (by omega_arith))
  refine ⟨⟨fit, by rw [h.wr, pre.wr]; simp⟩, ?_, width.trans pre.width, r0, ?_, ?_, ?_, ?_, ?_⟩
  · have layout := pre.layout
    unfold Proof.Rsa.Mont.Layout at layout ⊢
    rw [width]
    refine ⟨layout.1, layout.2.1, layout.2.2.1, fun j hj => ?_⟩
    unfold wordAt
    rw [hw _ (by simp only [Proof.Rsa.Mont.arrWord]; omega_arith)]
    exact layout.2.2.2 j hj
  · change ((s.mem.readW (off (State.addr P.ws) (arrAt P.w 0)) 64).toNat *
      (s.mem.readW (off (State.addr P.ws) 56) 64).toNat + 1) % 2 ^ 64 = 0
    rw [show s.mem.readW (off (State.addr P.ws) (arrAt P.w 0)) 64 =
      σ.mem.readW (off (State.addr P.ws) (arrAt P.w 0)) 64 by
        simp only [Mem.readW, hr (arrAt P.w 0) 8 (by omega_arith) (.inr (Nat.le_of_eq a0.symm))],
      hw 56 (by omega_arith)]
    exact pre.inverse
  · rw [show numAt s.mem (State.addr P.ws) P.w 0 = cOf P s.mem from rfl, h.c_eq]
    have := pre.c3; omega_arith
  · refine ⟨P.rF, List.mem_append_right _ (by rw [h.wr, pre.wr]; simp), ?_⟩
    rw [h.sp, pre.sp]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  · rw [h.sp, pre.sp]
    exact pre.sep.sub_left (Offset.sub_base (State.addr P.sp) (d := 0) (n := 4) (k := 56) (by decide) |>
      fun d => by simpa using d)
  · rw [h.sp, pre.sp]
    have := h.frameWord (o := 0) (by decide)
    simp only [off, BitVec.add_zero] at this
    rw [this, pre.saved]

/-- A step that writes the arrays `js` and the header words `ds` of the round's. -/
theorem KS.core {js ds : List Nat} (h : KS P σ A live V ls s) (k : Keep P.B P.W js ds s.mem t.mem)
    (hjs : ∀ j ∈ js, j ∈ wJs) (hds : ∀ d ∈ ds, d ∈ wDs) (sp : t.sp = s.sp) (rd : t.rd = s.rd)
    (wr : t.wr = s.wr) {A' : Nat → Nat} {live' : List Nat} {V' : Nat → Nat} {ls' : List Nat}
    (ha : Arrs t.mem P.B P.W A' live') (hsl : ∀ d ∈ ls', slot t.mem P.B d = V' d)
    (hl : ∀ j ∈ live', j < nArr) (hls : ∀ d ∈ ls', d ∈ wDs) :
    KS P σ A' live' V' ls' t :=
  ⟨h.pre, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, h.keep.trans (k.mono hjs hds), ha, hsl, hl, hls⟩

end

end VG.Proof.MillerRabin.Arm
