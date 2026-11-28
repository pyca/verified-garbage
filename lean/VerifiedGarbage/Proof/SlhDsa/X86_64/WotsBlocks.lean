module

public import VerifiedGarbage.Proof.SlhDsa.Internal
public import VerifiedGarbage.Proof.SlhDsa.Fld
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.SlhDsa.Lemmas
public import VerifiedGarbage.Proof.Framework.X86_64.Steps
public import VerifiedGarbage.Spec.SlhDsa
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Wots
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA on x86-64: the blocks of `wotsLeaves4`

The steps of the x86-64 instructions the
blocks use, and the blocks over the lanes: setting an address field,
copying and selecting words, and multiplying by `n`.
-/

@[expose] public section

/-! ## the instructions of the WOTS⁺ code, one at a time

The weakest-precondition rules of the instructions `wotsLeaves4` uses that
`Proof/Framework/X86_64/Steps.lean` lacks, in its style (`Upd`, `Mupd`), and
what `bswap32` does to the bytes of a 32-bit value: a field the code writes
with `mov32`, `bswap32` and `store32` holds its value's bytes most
significant first (`bswap32_byte`), as `toByte` does.
-/

namespace VG.X86_64.Steps

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `mov r32, r32`, which zero-extends. -/
theorem wp_mov32r {d r : Reg} (k : ∀ s', Upd s s' d (((s.gpr r).setWidth 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

/-- `bswap r32`, which zero-extends. -/
theorem wp_bswap32 {d : Reg}
    (k : ∀ s', Upd s s' d ((bswap32 ((s.gpr d).setWidth 32)).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.bswap32 d :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

/-- `mov dword [m], r32`. -/
theorem wp_store32 {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr r).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store32 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r).setWidth 32) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store32, ha, hout]

/-- `xor d, r`. -/
theorem wp_xor {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- `or d, r`. -/
theorem wp_or {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d ||| s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- `and d, r`. -/
theorem wp_and {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d &&& s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- `sub d, imm32`. -/
theorem wp_subi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d - v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem Upd.setFlagsReg (s : State) (cf o zf sf : Option Bool) (d : Reg) (v : BitVec 64) :
    Upd s ((s.setFlags cf o zf sf).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl, rfl, rfl⟩

/-- `shr d, n` for `1 ≤ n ≤ 63`. -/
theorem wp_shr {d : Reg} {n : Nat} (h₁ : 1 ≤ n) (h₂ : n ≤ 63)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q := by
  have e : exec (.shift .shr d n) s = some ((s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
      (if n = 1 then some (s.gpr d).msb else none) (some (s.gpr d >>> n == 0))
      (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) := by
    simp only [exec, execShift, h₁, h₂, and_self, ite_true]
  exact WP.cons e (k _ (Upd.setFlagsReg _ _ _ _ _ _ _))

/-- `shl d, n` for `1 ≤ n ≤ 63`. -/
theorem wp_shl {d : Reg} {n : Nat} (h₁ : 1 ≤ n) (h₂ : n ≤ 63)
    (k : ∀ s', Upd s s' d (s.gpr d <<< n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shl d n :: is)) s Q := by
  have e : exec (.shift .shl d n) s = some ((s.setFlags (some ((s.gpr d).getLsbD (64 - n)))
      (if n = 1 then some ((s.gpr d <<< n).msb ^^ (s.gpr d).getLsbD (64 - n)) else none) (some (s.gpr d <<< n == 0))
      (some (s.gpr d <<< n).msb)).setReg d (s.gpr d <<< n)) := by
    simp only [exec, execShift, h₁, h₂, and_self, ite_true]
  exact WP.cons e (k _ (Upd.setFlagsReg _ _ _ _ _ _ _))

/-- `cmp d, imm32`: ZF is `d = imm` (sign-extended). -/
theorem wp_cmpi {d : Reg} {v : BitVec 32}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

end

end VG.X86_64.Steps

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64

/-- Byte `d` of a 32-bit value after `bswap32` is its byte `3 - d`. -/
theorem bswap32_byte (x : BitVec 32) : ∀ d < 4, (bswap32 x).extractLsb' (8 * d) 8 = x.extractLsb' (8 * (3 - d)) 8 := by
  intro d hd
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega_using [hd]
  rcases this with rfl | rfl | rfl | rfl <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [bswap32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi]
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega_using [hi]
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- Byte `k` of a 32-bit value, as `toByte` writes byte `3 - k` of it. -/
theorem toByte4_getD (x : BitVec 32) {d : Nat} (hd : d < 4) :
    (Spec.SlhDsa.toByte x.toNat 4).getD d 0 = x.extractLsb' (8 * (3 - d)) 8 := by
  simp only [Spec.SlhDsa.toByte, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hd,
    Option.map_some, Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show (256 : Nat) ^ (4 - 1 - d) = 2 ^ (8 * (3 - d)) by rw [Nat.pow_mul]]

end VG.Proof.SlhDsa.X86_64

/-! ## the blocks of the WOTS⁺ code

What each straight-line piece of `wotsLeaves4` does, as the bytes it writes
(`bytesAt`) and the range it changes (`Frame`): a field of an address
(`setField`, `setFieldR`: its value's four bytes big-endian, `toByte`), a
copy of words (`copyWords`), and the multiplication by `n` (`mulN`).
-/

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64 VG.X86_64.Steps
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64

/-! ## Bytes of memory -/

theorem bytesAt_length' (m : Mem) (a : Addr) (n : Nat) : (bytesAt m a n).length = n := by simp [bytesAt]

theorem bytesAt_getD (m : Mem) (a : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m a n).getD i 0 = m (a + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

theorem bytesAt_ext {m m' : Mem} {a a' : Addr} {n : Nat}
    (h : ∀ i < n, m' (a' + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i)) : bytesAt m' a' n = bytesAt m a n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem bytesAt_eq_of {m : Mem} {a : Addr} {n : Nat} {L : List Byte} (hl : L.length = n)
    (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = L.getD i 0) : bytesAt m a n = L := by
  apply List.ext_getElem (by rw [bytesAt_length', hl])
  intro i h₁ h₂
  rw [bytesAt_length'] at h₁
  have e := h i h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some]

/-- Bytes a frame does not meet are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' a n = bytesAt m a n :=
  bytesAt_ext fun _ hi => hf.bytes (R := ⟨a, n⟩) hd hn hi

/-- The bytes a write of `w` bits writes. -/
theorem bytesAt_writeW {m : Mem} {a : Addr} {w : Nat} (v : BitVec w) (hw : w % 8 = 0) (hw' : w < 2 ^ 64) :
    bytesAt (m.writeW a v) a (w / 8) = (List.range (w / 8)).map fun d => v.extractLsb' (8 * d) 8 := by
  simp only [bytesAt]
  refine List.map_congr_left fun d hd => ?_
  exact writeW_byte _ _ _ (by have := List.mem_range.mp hd; omega_using [this, hw]) hw'

/-- A write's frame. -/
theorem frame_writeW (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) : Frame [⟨a, w / 8⟩] m (m.writeW a v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith)

/-! ## Addresses of operands -/

theorem ofInt_nat (d : Nat) : BitVec.ofInt 64 (d : Int) = BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (VG.Impl.Sha3.X86_64.at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, VG.Impl.Sha3.X86_64.at_, ofInt_nat]

theorem ofNat_add' (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## Fields of an address -/

theorem bswap_bytes (v : Nat) (hv : v < 2 ^ 32) :
    ((List.range (32 / 8)).map fun d => (bswap32 (BitVec.ofNat 32 v)).extractLsb' (8 * d) 8) = Spec.SlhDsa.toByte v 4 := by
  apply List.ext_getElem (by simp [Spec.SlhDsa.toByte])
  intro d h₁ _
  simp only [List.length_map, List.length_range] at h₁
  have e := toByte4_getD (BitVec.ofNat 32 v) (d := d) (by omega_using [h₁])
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv] at e
  rw [List.getElem_map, List.getElem_range, bswap32_byte _ _ (by omega_using [h₁]), ← e,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [Spec.SlhDsa.toByte]; omega_using [h₁]),
    Option.getD_some]

/-- What a store of `bswap32 x` (as `setField` and `setFieldR` make it) does. -/
structure FieldPost (s s' : State) (a : Addr) (v : Nat) : Prop where
  gpr : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bytes : bytesAt s'.mem a 4 = Spec.SlhDsa.toByte v 4
  frame : Frame [⟨a, 4⟩] s.mem s'.mem

theorem setWidth_32_64_32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq; simp

variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `setField b d v`: the field at `b + d` set to `v` (below `2³¹`). -/
theorem setField_ok {b : Reg} (hb : b ≠ .rax) {d v : Nat} (hv : v < 2 ^ 31)
    (hin : InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 4)
    (k : ∀ s', FieldPost s s' (s.gpr b + BitVec.ofNat 64 d) v → WP isa (.block is) s' Q) :
    WP isa (.block (setField b d v ++ is)) s Q := by
  simp only [setField, List.cons_append, List.nil_append]
  refine wp_mov32i fun s₁ u₁ => wp_bswap32 fun s₂ u₂ => ?_
  refine wp_store32 (a := s.gpr b + BitVec.ofNat 64 d) (by rw [ea_at, u₂.other _ hb, u₁.other _ hb])
    (by rw [u₂.wr, u₁.wr]; exact hin) fun s₃ u₃ => k s₃ ?_
  have hx : (s₂.gpr .rax).setWidth 32 = bswap32 (BitVec.ofNat 32 v) := by
    rw [u₂.gpr, u₁.gpr, setWidth_32_64_32, setWidth_32_64_32]
  refine ⟨fun r h => by rw [u₃.gpr, u₂.other _ h, u₁.other _ h], by rw [u₃.rd, u₂.rd, u₁.rd],
    by rw [u₃.wr, u₂.wr, u₁.wr], ?_, ?_⟩
  · rw [u₃.mem, hx, u₂.mem, u₁.mem, bytesAt_writeW _ (by decide) (by decide), bswap_bytes v (by omega_using [hv])]
  · rw [u₃.mem, u₂.mem, u₁.mem]; exact frame_writeW (w := 32) _ _ _

/-- `setFieldR b d r`: the field at `b + d` set to the register `r`, whose
value is below `2³²`. -/
theorem setFieldR_ok {b r : Reg} (hb : b ≠ .rax) {d : Nat} (hr : (s.gpr r).toNat < 2 ^ 32)
    (hin : InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 4)
    (k : ∀ s', FieldPost s s' (s.gpr b + BitVec.ofNat 64 d) (s.gpr r).toNat → WP isa (.block is) s' Q) :
    WP isa (.block (setFieldR b d r ++ is)) s Q := by
  simp only [setFieldR, List.cons_append, List.nil_append]
  refine wp_mov32r fun s₁ u₁ => wp_bswap32 fun s₂ u₂ => ?_
  refine wp_store32 (a := s.gpr b + BitVec.ofNat 64 d) (by rw [ea_at, u₂.other _ hb, u₁.other _ hb])
    (by rw [u₂.wr, u₁.wr]; exact hin) fun s₃ u₃ => k s₃ ?_
  have hx : (s₂.gpr .rax).setWidth 32 = bswap32 (BitVec.ofNat 32 (s.gpr r).toNat) := by
    rw [u₂.gpr, u₁.gpr, setWidth_32_64_32, setWidth_32_64_32, BitVec.ofNat_toNat]
  refine ⟨fun r h => by rw [u₃.gpr, u₂.other _ h, u₁.other _ h], by rw [u₃.rd, u₂.rd, u₁.rd],
    by rw [u₃.wr, u₂.wr, u₁.wr], ?_, ?_⟩
  · rw [u₃.mem, hx, u₂.mem, u₁.mem, bytesAt_writeW _ (by decide) (by decide), bswap_bytes _ hr]
  · rw [u₃.mem, u₂.mem, u₁.mem]; exact frame_writeW (w := 32) _ _ _

/-! ## Copies -/

/-- What `copyWords` from `src` to `dst` does, for `8 w` bytes. -/
structure CopyPost (s s' : State) (dst src : Addr) (len : Nat) : Prop where
  gpr : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bytes : ∀ q < len, s'.mem (dst + BitVec.ofNat 64 q) = s.mem (src + BitVec.ofNat 64 q)
  frame : Frame [⟨dst, len⟩] s.mem s'.mem

theorem copyWords_succ (t : Reg) (d₂ : Nat) (src : Reg) (d₁ j : Nat) :
    copyWords t d₂ src d₁ (j + 1) = copyWords t d₂ src d₁ j ++
      ([.mov .rax (.mem (VG.Impl.Sha3.X86_64.at_ src (d₁ + 8 * j))),
        .store (VG.Impl.Sha3.X86_64.at_ t (d₂ + 8 * j)) .rax] : List Instr) := by
  simp [copyWords, List.range_succ, List.flatMap_append]

/-- `copyWords t d₂ src d₁ w`: the `8 w` bytes at `src + d₁` copied to `t + d₂`. -/
theorem copyWords_ok {t src : Reg} (ht : t ≠ .rax) (hs : src ≠ .rax) {d₂ d₁ w : Nat}
    (hdst : ∀ j < w, InRegions s.wr (s.gpr t + BitVec.ofNat 64 (d₂ + 8 * j)) 8)
    (hsrc : ∀ j < w, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 (d₁ + 8 * j)) 8)
    (hdis : Region.Disjoint ⟨s.gpr t + BitVec.ofNat 64 d₂, 8 * w⟩ ⟨s.gpr src + BitVec.ofNat 64 d₁, 8 * w⟩)
    (hfit₁ : 8 * w ≤ 2 ^ 32) (hd₂ : d₂ + 8 * w ≤ 2 ^ 32) :
    WP isa (.block (copyWords t d₂ src d₁ w)) s
      (fun s' => CopyPost s s' (s.gpr t + BitVec.ofNat 64 d₂) (s.gpr src + BitVec.ofNat 64 d₁) (8 * w)) := by
  suffices h : ∀ j ≤ w, WP isa (.block (copyWords t d₂ src d₁ j)) s
      (fun s' => CopyPost s s' (s.gpr t + BitVec.ofNat 64 d₂) (s.gpr src + BitVec.ofNat 64 d₁) (8 * j)) from
    h w (Nat.le_refl _)
  intro j
  induction j with
  | zero =>
    intro _
    exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, fun q hq => absurd hq (by omega_using []), by
      simpa using Frame.refl [⟨s.gpr t + BitVec.ofNat 64 d₂, 0⟩] s.mem⟩
  | succ j ih =>
    intro hj
    rw [copyWords_succ]
    refine WP.block_append (WP.mono (ih (by omega_using [hj])) fun s₁ c₁ => ?_)
    have hs₁ : s₁.gpr src = s.gpr src := c₁.gpr _ hs
    have ht₁ : s₁.gpr t = s.gpr t := c₁.gpr _ ht
    refine wp_movm (a := s.gpr src + BitVec.ofNat 64 (d₁ + 8 * j)) (by rw [ea_at, hs₁])
      (by rw [c₁.rd, c₁.wr]; exact hsrc j (by omega_using [hj])) fun s₂ u₂ => ?_
    refine wp_store (a := s.gpr t + BitVec.ofNat 64 (d₂ + 8 * j)) (by rw [ea_at, u₂.other _ ht, ht₁])
      (by rw [u₂.wr, c₁.wr]; exact hdst j (by omega_using [hj])) fun s₃ u₃ => WP.block_nil ?_
    have hsrcb : ∀ q < 8 * (j + 1), s₁.mem (s.gpr src + BitVec.ofNat 64 d₁ + BitVec.ofNat 64 q) =
        s.mem (s.gpr src + BitVec.ofNat 64 d₁ + BitVec.ofNat 64 q) := fun q hq =>
      c₁.frame.bytes (R := ⟨s.gpr src + BitVec.ofNat 64 d₁, 8 * w⟩) (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact (hdis.symm).sub_right (Region.sub_prefix (by omega_using [hj]))) (by show 8 * w ≤ 2 ^ 64; omega_using [hfit₁])
        (by show q < 8 * w; omega_using [hq, hj])
    refine ⟨fun r h => by rw [u₃.gpr, u₂.other _ h, c₁.gpr _ h], by rw [u₃.rd, u₂.rd, c₁.rd],
      by rw [u₃.wr, u₂.wr, c₁.wr], fun q hq => ?_, ?_⟩
    · rw [u₃.mem, u₂.gpr, u₂.mem]
      by_cases c : q < 8 * j
      · rw [writeW_byte_off _ _ _ _ (by
            rw [show s.gpr t + BitVec.ofNat 64 d₂ + BitVec.ofNat 64 q = s.gpr t + BitVec.ofNat 64 (d₂ + q) from
              ofNat_add' .., Offset.sub_toNat' _ (by omega_using [hfit₁, hj, hd₂]) (by omega_using [hfit₁, hj, c, hd₂, hq])]
            split <;> rename_i hh <;> omega_using [c, hh, hfit₁, hj, hd₂, hq]), c₁.bytes q c]
      · rw [show s.gpr t + BitVec.ofNat 64 d₂ + BitVec.ofNat 64 q =
            s.gpr t + BitVec.ofNat 64 (d₂ + 8 * j) + BitVec.ofNat 64 (q - 8 * j) by
            rw [ofNat_add', ofNat_add', show d₂ + 8 * j + (q - 8 * j) = d₂ + q by omega_using [c]],
          writeW_byte _ _ _ (by omega_using [hq, c]) (by decide), byte_readW _ _ (by omega_using [hq, c]),
          ofNat_add', show s.gpr src + BitVec.ofNat 64 (d₁ + 8 * j + (q - 8 * j)) =
            s.gpr src + BitVec.ofNat 64 d₁ + BitVec.ofNat 64 q by
            rw [ofNat_add', show d₁ + 8 * j + (q - 8 * j) = d₁ + q by omega_using [c]], hsrcb q hq]
    · rw [u₃.mem, u₂.mem]
      refine Frame.writeW (c₁.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_using [])⟩)
        (List.mem_singleton_self _) _ ?_
      rw [show s.gpr t + BitVec.ofNat 64 (d₂ + 8 * j) = s.gpr t + BitVec.ofNat 64 d₂ + BitVec.ofNat 64 (8 * j) from
        (ofNat_add' ..).symm]
      exact Offset.contains_base _ (by omega_using []) (by omega_using [hfit₁, hj])

/-! ## Masked copies -/

/-- The mask selects. -/
theorem sel (b : Bool) (lw sw : BitVec 64) :
    sw ^^^ ((lw ^^^ sw) &&& (if b then BitVec.allOnes 64 else 0)) = if b then lw else sw := by
  cases b
  · simp
  · simp only [ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm lw sw, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- What the masked copy from `src` to `dst` does, for `len` bytes: the
bytes of `src` if `b`, and `dst`'s own otherwise. -/
structure SelPost (s s' : State) (b : Bool) (dst src : Addr) (len : Nat) : Prop where
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bytes : ∀ q < len, s'.mem (dst + BitVec.ofNat 64 q) =
    if b then s.mem (src + BitVec.ofNat 64 q) else s.mem (dst + BitVec.ofNat 64 q)
  frame : Frame [⟨dst, len⟩] s.mem s'.mem

/-- The masked copy of word `w`, with the mask in `rdi`. -/
def selWord (dst : Reg) (src : Reg) (d₁ w : Nat) : List Instr :=
  [.mov .rax (.mem (VG.Impl.Sha3.X86_64.at_ dst (8 * w))), .mov .rcx (.mem (VG.Impl.Sha3.X86_64.at_ src (d₁ + 8 * w))),
    .alu .xor .rcx (.reg .rax), .alu .and .rcx (.reg .rdi), .alu .xor .rax (.reg .rcx),
    .store (VG.Impl.Sha3.X86_64.at_ dst (8 * w)) .rax]

theorem selWords_ok {dst src : Reg} (hd : dst ≠ .rax ∧ dst ≠ .rcx) (hs : src ≠ .rax ∧ src ≠ .rcx)
    {b : Bool} (hm : s.gpr .rdi = if b then BitVec.allOnes 64 else 0) {d₁ w : Nat}
    (hdst : ∀ j < w, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 (8 * j)) 8)
    (hsrc : ∀ j < w, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 (d₁ + 8 * j)) 8)
    (hdis : Region.Disjoint ⟨s.gpr dst, 8 * w⟩ ⟨s.gpr src + BitVec.ofNat 64 d₁, 8 * w⟩)
    (hfit₁ : 8 * w ≤ 2 ^ 32) (hfit : (s.gpr dst).toNat + 8 * w ≤ 2 ^ 64) :
    WP isa (.block ((List.range w).flatMap (selWord dst src d₁))) s
      (fun s' => SelPost s s' b (s.gpr dst) (s.gpr src + BitVec.ofNat 64 d₁) (8 * w)) := by
  suffices h : ∀ j ≤ w, WP isa (.block ((List.range j).flatMap (selWord dst src d₁))) s
      (fun s' => SelPost s s' b (s.gpr dst) (s.gpr src + BitVec.ofNat 64 d₁) (8 * j)) from
    h w (Nat.le_refl _)
  intro j
  induction j with
  | zero =>
    intro _
    exact WP.block_nil ⟨fun _ _ _ => rfl, rfl, rfl, fun q hq => absurd hq (by omega_using []), by
      simpa using Frame.refl [⟨s.gpr dst, 0⟩] s.mem⟩
  | succ j ih =>
    intro hj
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ih (by omega_using [hj])) fun s₁ c₁ => ?_)
    have hs₁ : s₁.gpr src = s.gpr src := c₁.gpr _ hs.1 hs.2
    have ht₁ : s₁.gpr dst = s.gpr dst := c₁.gpr _ hd.1 hd.2
    have hm₁ : s₁.gpr .rdi = s.gpr .rdi := c₁.gpr _ (by decide) (by decide)
    simp only [selWord]
    refine wp_movm (a := s.gpr dst + BitVec.ofNat 64 (8 * j)) (by rw [ea_at, ht₁])
      (by rw [c₁.rd, c₁.wr]; obtain ⟨r, h₁, h₂⟩ := hdst j (by omega_using [hj])
          exact ⟨r, List.mem_append_right _ h₁, h₂⟩) fun s₂ u₂ => ?_
    refine wp_movm (a := s.gpr src + BitVec.ofNat 64 (d₁ + 8 * j)) (by rw [ea_at, u₂.other _ hs.1, hs₁])
      (by rw [u₂.rd, u₂.wr, c₁.rd, c₁.wr]; exact hsrc j (by omega_using [hj])) fun s₃ u₃ => ?_
    refine wp_xor fun s₄ u₄ => wp_and fun s₅ u₅ => wp_xor fun s₆ u₆ => ?_
    refine wp_store (a := s.gpr dst + BitVec.ofNat 64 (8 * j))
      (by rw [ea_at, u₆.other _ hd.1, u₅.other _ hd.2, u₄.other _ hd.2, u₃.other _ hd.2, u₂.other _ hd.1, ht₁])
      (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, c₁.wr]; exact hdst j (by omega_using [hj])) fun s₇ u₇ => WP.block_nil ?_
    have hv : s₆.gpr .rax = if b then s₁.mem.readW (s.gpr src + BitVec.ofNat 64 (d₁ + 8 * j)) 64
        else s₁.mem.readW (s.gpr dst + BitVec.ofNat 64 (8 * j)) 64 := by
      have a3 : s₃.gpr .rax = s₁.mem.readW (s.gpr dst + BitVec.ofNat 64 (8 * j)) 64 := by
        rw [u₃.other _ (by decide), u₂.gpr]
      have c3 : s₃.gpr .rcx = s₁.mem.readW (s.gpr src + BitVec.ofNat 64 (d₁ + 8 * j)) 64 := by rw [u₃.gpr, u₂.mem]
      have d3 : s₃.gpr .rdi = if b then BitVec.allOnes 64 else 0 := by
        rw [u₃.other _ (by decide), u₂.other _ (by decide), hm₁, hm]
      have c4 : s₄.gpr .rcx = s₃.gpr .rcx ^^^ s₃.gpr .rax := u₄.gpr
      have a4 : s₄.gpr .rax = s₃.gpr .rax := u₄.other _ (by decide)
      have d4 : s₄.gpr .rdi = s₃.gpr .rdi := u₄.other _ (by decide)
      have c5 : s₅.gpr .rcx = s₄.gpr .rcx &&& s₄.gpr .rdi := u₅.gpr
      have a5 : s₅.gpr .rax = s₄.gpr .rax := u₅.other _ (by decide)
      rw [u₆.gpr, c5, a5, c4, a4, d4, a3, c3, d3, sel]
    -- Bytes of `src` and of the new word of `dst` before the store.
    have hsrcb : ∀ q < 8 * (j + 1), s₁.mem (s.gpr src + BitVec.ofNat 64 d₁ + BitVec.ofNat 64 q) =
        s.mem (s.gpr src + BitVec.ofNat 64 d₁ + BitVec.ofNat 64 q) := fun q hq =>
      c₁.frame.bytes (R := ⟨s.gpr src + BitVec.ofNat 64 d₁, 8 * w⟩) (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact (hdis.symm).sub_right (Region.sub_prefix (by omega_using [hj]))) (by show 8 * w ≤ 2 ^ 64; omega_using [hfit₁])
        (by show q < 8 * w; omega_using [hq, hj])
    have hdstb : ∀ q, 8 * j ≤ q → q < 8 * (j + 1) → s₁.mem (s.gpr dst + BitVec.ofNat 64 q) = s.mem (s.gpr dst + BitVec.ofNat 64 q) := by
      intro q h₁ h₂
      have e := c₁.frame.bytes (R := ⟨s.gpr dst + BitVec.ofNat 64 (8 * j), 8⟩) (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by omega_using []) (by omega_using [hfit, hj])) (by show 8 ≤ 2 ^ 64; decide) (i := q - 8 * j)
        (by show q - 8 * j < 8; omega_using [h₂])
      rwa [ofNat_add', show 8 * j + (q - 8 * j) = q by omega_using [h₁]] at e
    refine ⟨fun r h₁ h₂ => by
        rw [u₇.gpr, u₆.other _ h₁, u₅.other _ h₂, u₄.other _ h₂, u₃.other _ h₂, u₂.other _ h₁, c₁.gpr _ h₁ h₂],
      by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, c₁.rd],
      by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, c₁.wr], fun q hq => ?_, ?_⟩
    · have hm₆ : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
      rw [u₇.mem, hm₆]
      by_cases c : q < 8 * j
      · rw [writeW_byte_off _ _ _ _ (by
            rw [Offset.sub_toNat' _ (by omega_using [hfit₁, hj]) (by omega_using [hfit₁, hj, c, hq])]
            split <;> rename_i hh <;> omega_using [c, hh, hfit₁, hj, hq]), c₁.bytes q c]
      · rw [show s.gpr dst + BitVec.ofNat 64 q = s.gpr dst + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 (q - 8 * j) by
            rw [ofNat_add', show 8 * j + (q - 8 * j) = q by omega_using [c]],
          writeW_byte _ _ _ (by omega_using [hq, c]) (by decide), hv]
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [byte_readW _ _ (by omega_using [hq, c]), ofNat_add',
            show 8 * j + (q - 8 * j) = q by omega_using [c], hdstb q (by omega_using [c]) hq]
        · simp only [↓reduceIte]
          rw [byte_readW _ _ (by omega_using [hq, c]), ofNat_add',
            show d₁ + 8 * j + (q - 8 * j) = d₁ + q by omega_using [c], ← ofNat_add', hsrcb q hq]
    · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
      refine Frame.writeW (c₁.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_using [])⟩)
        (List.mem_singleton_self _) _ ?_
      exact Offset.contains_base _ (by omega_using []) (by omega_using [hfit₁, hj])

/-- The mask of `captureLane`: all ones exactly if `A = B` and `C = E`. -/
theorem mask_eq {A B C E : BitVec 64} (hA : A.toNat < 2 ^ 32) (hB : B.toNat < 2 ^ 32) (hC : C.toNat < 2 ^ 32)
    (hE : E.toNat < 2 ^ 32) :
    (0 : BitVec 64) - ((((A ^^^ B) ||| (C ^^^ E)) - 1) >>> 63) = if A = B ∧ C = E then BitVec.allOnes 64 else 0 := by
  by_cases h : A = B ∧ C = E
  · rw [h.1, h.2, BitVec.xor_self, BitVec.xor_self, BitVec.or_self]; simp only [and_self, ↓reduceIte]; decide
  · simp only [h, ↓reduceIte]
    have hx : ((A ^^^ B) ||| (C ^^^ E)).toNat < 2 ^ 32 := by
      rw [BitVec.toNat_or, BitVec.toNat_xor, BitVec.toNat_xor]
      exact Nat.or_lt_two_pow (Nat.xor_lt_two_pow hA hB) (Nat.xor_lt_two_pow hC hE)
    have h0 : ((A ^^^ B) ||| (C ^^^ E)) ≠ 0#64 := fun e => h (by
      rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff] at e; exact e)
    have h1 : (1 : BitVec 64) ≤ ((A ^^^ B) ||| (C ^^^ E)) := by
      rw [BitVec.le_def]
      have : ((A ^^^ B) ||| (C ^^^ E)).toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
      show 1 ≤ _; omega_using [this]
    have hs : (((A ^^^ B) ||| (C ^^^ E)) - 1) >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub_of_le h1, Nat.shiftRight_eq_div_pow]
      show _ = 0
      exact Nat.div_eq_of_lt (by have : (1 : BitVec 64).toNat = 1 := rfl; omega_using [hx, this])
    rw [hs]; decide

/-! ## The multiplication by `n` -/

theorem shl_ofNat (x k : Nat) : BitVec.ofNat 64 x <<< k = BitVec.ofNat 64 (x * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- `mulN n r tmp`: `r ← r·n`, for `n` 16, 24 or 32 and `tmp ≠ r`; it writes
only `r` and `tmp`. -/
theorem mulN_ok {n : Nat} (hn : n = 16 ∨ n = 24 ∨ n = 32) {r tmp : Reg} (hrt : r ≠ tmp) {x : Nat}
    (hx : s.gpr r = BitVec.ofNat 64 x)
    (k : ∀ s', s'.gpr r = BitVec.ofNat 64 (x * n) → (∀ g, g ≠ r → g ≠ tmp → s'.gpr g = s.gpr g) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (Wots.mulN n r tmp ++ is)) s Q := by
  rcases hn with rfl | rfl | rfl
  · simp only [Wots.mulN, show (16 : Nat) ≠ 24 by decide, ite_false, ite_true, List.cons_append, List.nil_append]
    refine wp_shl (by decide) (by decide) fun s₁ u₁ => k s₁ ?_ (fun g h _ => u₁.other _ h) u₁.mem u₁.rd u₁.wr
    rw [u₁.gpr, hx, shl_ofNat]
  · simp only [Wots.mulN, ite_true, List.cons_append, List.nil_append]
    refine wp_mov fun s₁ u₁ => wp_shl (by decide) (by decide) fun s₂ u₂ => wp_shl (by decide) (by decide)
      fun s₃ u₃ => wp_add fun s₄ u₄ => k s₄ ?_ (fun g h₁ h₂ => ?_) ?_ ?_ ?_
    · rw [u₄.gpr, u₃.other _ hrt, u₂.gpr, u₃.gpr, u₂.other _ hrt.symm, u₁.gpr, u₁.other _ hrt, hx, shl_ofNat,
        shl_ofNat, ← BitVec.ofNat_add]
      congr 1; omega_arith
    · rw [u₄.other _ h₁, u₃.other _ h₂, u₂.other _ h₁, u₁.other _ h₂]
    · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · simp only [Wots.mulN, show (32 : Nat) ≠ 24 by decide, show (32 : Nat) ≠ 16 by decide, ite_false,
      List.cons_append, List.nil_append]
    refine wp_shl (by decide) (by decide) fun s₁ u₁ => k s₁ ?_ (fun g h _ => u₁.other _ h) u₁.mem u₁.rd u₁.wr
    rw [u₁.gpr, hx, shl_ofNat]

end VG.Proof.SlhDsa.X86_64
