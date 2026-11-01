module

public import VerifiedGarbage.Impl.MlKem1024.X86_64.CompressAvx2
public import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompressAvx2
public import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim
public import VerifiedGarbage.Proof.MlKem1024.X86_64.Contracts
import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.MlKem1024.X86_64.CompressAvx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompressAvx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.Contracts
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncode
meta import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM-1024 on x86-64: `Decompress_d ∘ ByteDecode_d` with AVX2, which the K-PKE functions inline

As ML-KEM-768's (`Proof/MlKem/X86_64/DecodeDecompressAvx2.lean`): value `e`
of a group of width `d` is extracted from the bytes that hold it, from byte
`⌊d e / 8⌋`, in a doubleword of a lane (`Sel`, `dword_valsW`), decompressed
by sums of shifts (`dword_ddM`), and is the coefficient of the specification
by `DD.seg` (`valW`).
-/

@[expose] public section

namespace VG.Proof.MlKem1024.X86_64.DDW

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.Sha3.X86_64 (WP.cons)
open VG.Proof.MlKem.X86_64.S4 (LUpd wp_vbin wp_vvar wp_vbcast128 wp_vst256 GUpd wp_addi' itT itF ext_app2
  toNat_dword_ofBytes)
open VG.Proof.MlKem.X86_64.D12Y (wp_vsh wp_subi' wp_vzu wp_mov32i yconst4_ok yconst_ok')
open VG.Proof.MlKem.X86_64.DDY (mk rc dword_mk dword_rc toNat_and_mk lane4 vals ddM Hi Kp ddMul_ok dig1 dig2)

/-! ## The masks of `vpshufb` and the shifts -/

/-- The masks of `d = 11` (each lane, of a group from byte 0 and from byte 5), and its shifts. -/
def m11a : BitVec 128 := 0x80800504800403028080020180800100#128
def m11b : BitVec 128 := 0x80800a09808009088008070680800605#128
def m11c : BitVec 128 := 0x80800a09800908078080070680800605#128
def m11d : BitVec 128 := 0x80800f0e80800e0d800d0c0b80800b0a#128
def sh11a : BitVec 128 := 0x00000001000000060000000300000000#128
def sh11b : BitVec 128 := 0x00000005000000020000000700000004#128
/-- The masks of `d = 5` (each lane, of a group from bytes 0, 5, 6 and 11), and its shifts. -/
def m5a0 : BitVec 128 := 0x80800201808080018080010080808000#128
def m5b0 : BitVec 128 := 0x80808004808004038080800380800302#128
def m5a1 : BitVec 128 := 0x80800706808080068080060580808005#128
def m5b1 : BitVec 128 := 0x80808009808009088080800880800807#128
def m5a2 : BitVec 128 := 0x80800807808080078080070680808006#128
def m5b2 : BitVec 128 := 0x8080800a80800a098080800980800908#128
def m5a3 : BitVec 128 := 0x80800d0c8080800c80800c0b8080800b#128
def m5b3 : BitVec 128 := 0x8080800f80800f0e8080800e80800e0d#128
def sh5a : BitVec 128 := 0x00000007000000020000000500000000#128
def sh5b : BitVec 128 := 0x00000003000000060000000100000004#128

/-- What the mask `M` selects for lane `l` of a group of width `d` whose bytes
are from byte `o`: in doubleword `j`, the bytes that hold value `e = 4 l + j`,
from byte `o + ⌊d e / 8⌋`, the others zero. -/
def Sel (d : Nat) (M : BitVec 128) (o l : Nat) : Prop :=
  ∀ a : BitVec 128, XBinOp.eval .pshufb a M = ofBytes fun i =>
    if i % 4 < (d * (4 * l + i / 4) % 8 + d + 7) / 8 then byte a (o + d * (4 * l + i / 4) / 8 + i % 4) else 0

theorem hM11 : ∀ l < 2, Sel 11 (if l = 0 then m11a else m11b) 0 l := fun l hl => by
  rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> exact fun a => by simp only [XBinOp.eval, ofBytes]; rfl

theorem hM11' : ∀ l < 2, Sel 11 (if l = 0 then m11c else m11d) 5 l := fun l hl => by
  rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> exact fun a => by simp only [XBinOp.eval, ofBytes]; rfl

theorem hM5 : ∀ l < 2, Sel 5 (if l = 0 then m5a0 else m5b0) 0 l := fun l hl => by
  rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> exact fun a => by simp only [XBinOp.eval, ofBytes]; rfl

theorem hM5' : ∀ l < 2, Sel 5 (if l = 0 then m5a1 else m5b1) 5 l := fun l hl => by
  rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> exact fun a => by simp only [XBinOp.eval, ofBytes]; rfl

theorem hM5'' : ∀ l < 2, Sel 5 (if l = 0 then m5a2 else m5b2) 6 l := fun l hl => by
  rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> exact fun a => by simp only [XBinOp.eval, ofBytes]; rfl

theorem hM5''' : ∀ l < 2, Sel 5 (if l = 0 then m5a3 else m5b3) 11 l := fun l hl => by
  rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> exact fun a => by simp only [XBinOp.eval, ofBytes]; rfl

theorem hS11 : ∀ l < 2, ∀ j < 4, (dword (if l = 0 then sh11a else sh11b) j).toNat = 11 * (4 * l + j) % 8 :=
  fun l hl j hj => by
    rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> rcases cases4 hj with rfl | rfl | rfl | rfl <;> rfl

theorem hS5 : ∀ l < 2, ∀ j < 4, (dword (if l = 0 then sh5a else sh5b) j).toNat = 5 * (4 * l + j) % 8 :=
  fun l hl j hj => by
    rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> rcases cases4 hj with rfl | rfl | rfl | rfl <;> rfl

/-! ## The values -/

theorem dig3 (f : Nat → Nat) : digits 8 ((List.range 3).map f) = f 0 + 256 * f 1 + 65536 * f 2 := by
  simp [List.range_succ, digits_cons, digits_nil]
  omega_arith

/-- Value `4 l + j` of a lane of the 16 bytes `a`: the number of the bytes that hold it, shifted. -/
theorem dword_valsW {d : Nat} (hd : d = 5 ∨ d = 11) (a : BitVec 128) {M S : BitVec 128} {o l : Nat} (hl : l < 2)
    (hM : Sel d M o l) (hS : ∀ j < 4, (dword S j).toNat = d * (4 * l + j) % 8) {j : Nat} (hj : j < 4) :
    (dword (vals a M S d) j).toNat =
      digits 8 ((List.range ((d * (4 * l + j) % 8 + d + 7) / 8)).map fun t =>
        (byte a (o + d * (4 * l + j) / 8 + t)).toNat) / 2 ^ 0 / 2 ^ (d * (4 * l + j) % 8) % 2 ^ d := by
  have h0 := hS 0 (by decide); have h1 := hS 1 (by decide); have h2 := hS 2 (by decide)
  have h3 := hS 3 (by decide)
  rw [dword_pand, dword_mk hj, toNat_and_mk (by omega_arith), hM]
  rcases hd with rfl | rfl <;> rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;>
    rcases cases4 hj with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv] at h0 h1 h2 h3 ⊢ <;>
    simp only [VVarOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, h0, h1, h2, h3,
      Nat.reduceLT, ↓reduceIte, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      toNat_dword_ofBytes _ (show 0 < 4 by decide), toNat_dword_ofBytes _ (show 1 < 4 by decide),
      toNat_dword_ofBytes _ (show 2 < 4 by decide), toNat_dword_ofBytes _ (show 3 < 4 by decide),
      Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.add_zero, Nat.add_assoc,
      show (0 : BitVec 8).toNat = 0 from rfl, Nat.mul_zero, dig1, dig2, dig3, Nat.pow_zero, Nat.div_one] <;>
    omega_arith

/-! ## Decompression -/

theorem dword_ddM (x R : BitVec 128) {d : Nat} (hd : d ≤ 11) {j : Nat} (hj : j < 4)
    (hy : (dword x j).toNat < 2 ^ 11) (hr : (dword R j).toNat < 2 ^ 11) :
    (dword (ddM x R d) j).toNat = (3329 * (dword x j).toNat + (dword R j).toNat) / 2 ^ d := by
  have h8 : BitVec.toNat (8 : BitVec 8) = 8 := rfl
  have h10 : BitVec.toNat (10 : BitVec 8) = 10 := rfl
  have h12 : BitVec.toNat (12 : BitVec 8) = 12 := rfl
  have hdn : (BitVec.ofNat 8 d).toNat = d := by rw [BitVec.toNat_ofNat]; omega_arith
  rw [dword_psrld _ _ (by omega_arith) hj, hdn, dword_paddd _ _ hj, dword_paddd _ _ hj, dword_paddd _ _ hj,
    dword_psubd _ _ hj, dword_pslld _ _ (by decide) hj, dword_pslld _ _ (by decide) hj,
    dword_pslld _ _ (by decide) hj, h8, h10, h12]
  generalize dword x j = y at hy ⊢
  generalize dword R j = r at hr ⊢
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  congr 1
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega_arith

/-- Value `j` of lane `l` of group `g` of width `d`, of the bytes `L` that hold the group's from `ob`. -/
theorem valW {d : Nat} (hd : d = 5 ∨ d = 11) {B : List Byte} (hB : B.length = 32 * d) {g : Nat} (hg : g < 32)
    {L : BitVec 128} {ob : Nat} (hL : ∀ t < d, byte L (ob + t) = B.getD (d * g + t) 0) {M S : BitVec 128}
    {l : Nat} (hl : l < 2) (hM : Sel d M ob l) (hS : ∀ j < 4, (dword S j).toNat = d * (4 * l + j) % 8)
    {r : Nat} (hr : r = 2 ^ (d - 1)) {j : Nat} (hj : j < 4) :
    (dword (ddM (vals L M S d) (rc r) d) j).toNat = ((decodeDecompress d B)[8 * g + (4 * l + j)]!).val := by
  have hv := dword_valsW hd L hl hM hS hj
  have hd11 : d ≤ 11 := by omega_arith
  have hr32 : r < 2 ^ 11 := by rw [hr]; rcases hd with rfl | rfl <;> decide
  rw [dword_ddM _ _ hd11 hj (by
      rw [hv]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos d)) (Nat.pow_le_pow_right (by decide) hd11))
    (by rw [dword_rc hj, BitVec.toNat_ofNat]; omega_arith), hv, dword_rc hj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show r < 2 ^ 32 by omega_arith), hr]
  rw [show (List.range ((d * (4 * l + j) % 8 + d + 7) / 8)).map (fun t => (byte L (ob + d * (4 * l + j) / 8 + t)).toNat) =
      (List.range ((d * (4 * l + j) % 8 + d + 7) / 8)).map
        (fun t => (B.getD (d * g + (d * (4 * l + j) / 8 + t)) 0).toNat) from List.map_congr_left fun t ht => by
      have := List.mem_range.mp ht
      rw [Nat.add_assoc, hL _ (by rcases hd with rfl | rfl <;> omega_arith)]]
  exact DD.seg (d := d) (c := 8) (b := d) (o := d * (4 * l + j) / 8) (l := (d * (4 * l + j) % 8 + d + 7) / 8) (s := 0)
    (p := d * (4 * l + j) % 8) (by omega_arith) hd11 (by omega_arith) B (by rw [hB]; rcases hd with rfl | rfl <;> omega_arith) (by omega_arith)
    (by omega_arith) (by rcases hd with rfl | rfl <;> omega_arith)

/-! ## The constants -/

/-- The constants of `d = 11`. -/
structure C11 (s : State) : Prop where
  c8 : ∀ l < 2, s.lane .xmm8 l = if l = 0 then m11a else m11b
  c12 : ∀ l < 2, s.lane .xmm12 l = if l = 0 then m11c else m11d
  c9 : ∀ l < 2, s.lane .xmm9 l = if l = 0 then sh11a else sh11b
  c10 : ∀ l < 2, s.lane .xmm10 l = mk 11
  c11 : ∀ l < 2, s.lane .xmm11 l = rc 1024

theorem C11.pres {s s' : State} (h : C11 s) (hk : Hi s s') : C11 s' :=
  ⟨fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c8 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c12 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c9 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c10 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c11 l hl]⟩

/-- The constants of `d = 5`. -/
structure C5 (s : State) : Prop where
  c8 : ∀ l < 2, s.lane .xmm8 l = if l = 0 then m5a0 else m5b0
  c9 : ∀ l < 2, s.lane .xmm9 l = if l = 0 then m5a1 else m5b1
  c10 : ∀ l < 2, s.lane .xmm10 l = if l = 0 then m5a2 else m5b2
  c11 : ∀ l < 2, s.lane .xmm11 l = if l = 0 then m5a3 else m5b3
  c12 : ∀ l < 2, s.lane .xmm12 l = if l = 0 then sh5a else sh5b
  c13 : ∀ l < 2, s.lane .xmm13 l = mk 5
  c14 : ∀ l < 2, s.lane .xmm14 l = rc 16

theorem C5.pres {s s' : State} (h : C5 s) (hk : Hi s s') : C5 s' :=
  ⟨fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c8 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c9 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c10 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c11 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c12 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c13 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c14 l hl]⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem consts11_ok
    (k : ∀ s', C11 s' → (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (dd11Consts ++ is)) s Q := by
  simp only [dd11Consts, List.append_assoc]
  refine yconst4_ok (by decide) (by decide) _ _ _ _ fun s1 a1 b1 o1 g1 m1 r1 w1 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s2 a2 b2 o2 g2 m2 r2 w2 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s3 a3 b3 o3 g3 m3 r3 w3 =>
    yconst_ok' _ _ fun s4 a4 o4 g4 m4 r4 w4 => yconst_ok' _ _ fun s5 a5 o5 g5 m5 r5 w5 =>
    k s5 ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩ (fun g hg => ?_) ?_ ?_ ?_
  · rw [o5 _ (by decide) l hl, o4 _ (by decide) l hl, o3 _ (by decide) (by decide) (by decide) l hl,
      o2 _ (by decide) (by decide) (by decide) l hl]
    exact lane4 a1 b1 rfl rfl l hl
  · rw [o5 _ (by decide) l hl, o4 _ (by decide) l hl, o3 _ (by decide) (by decide) (by decide) l hl]
    exact lane4 a2 b2 rfl rfl l hl
  · rw [o5 _ (by decide) l hl, o4 _ (by decide) l hl]
    exact lane4 a3 b3 rfl rfl l hl
  · rw [o5 _ (by decide) l hl, a4 l hl]; rfl
  · rw [a5 l hl]; rfl
  · rw [g5 g hg, g4 g hg, g3 g hg, g2 g hg, g1 g hg]
  · rw [m5, m4, m3, m2, m1]
  · rw [r5, r4, r3, r2, r1]
  · rw [w5, w4, w3, w2, w1]

theorem consts5_ok
    (k : ∀ s', C5 s' → (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (dd5Consts ++ is)) s Q := by
  simp only [dd5Consts, List.append_assoc]
  refine yconst4_ok (by decide) (by decide) _ _ _ _ fun s1 a1 b1 o1 g1 m1 r1 w1 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s2 a2 b2 o2 g2 m2 r2 w2 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s3 a3 b3 o3 g3 m3 r3 w3 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s4 a4 b4 o4 g4 m4 r4 w4 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s5 a5 b5 o5 g5 m5 r5 w5 =>
    yconst_ok' _ _ fun s6 a6 o6 g6 m6 r6 w6 => yconst_ok' _ _ fun s7 a7 o7 g7 m7 r7 w7 =>
    k s7 ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_,
      fun l hl => ?_⟩ (fun g hg => ?_) ?_ ?_ ?_
  · rw [o7 _ (by decide) l hl, o6 _ (by decide) l hl, o5 _ (by decide) (by decide) (by decide) l hl,
      o4 _ (by decide) (by decide) (by decide) l hl, o3 _ (by decide) (by decide) (by decide) l hl,
      o2 _ (by decide) (by decide) (by decide) l hl]
    exact lane4 a1 b1 rfl rfl l hl
  · rw [o7 _ (by decide) l hl, o6 _ (by decide) l hl, o5 _ (by decide) (by decide) (by decide) l hl,
      o4 _ (by decide) (by decide) (by decide) l hl, o3 _ (by decide) (by decide) (by decide) l hl]
    exact lane4 a2 b2 rfl rfl l hl
  · rw [o7 _ (by decide) l hl, o6 _ (by decide) l hl, o5 _ (by decide) (by decide) (by decide) l hl,
      o4 _ (by decide) (by decide) (by decide) l hl]
    exact lane4 a3 b3 rfl rfl l hl
  · rw [o7 _ (by decide) l hl, o6 _ (by decide) l hl, o5 _ (by decide) (by decide) (by decide) l hl]
    exact lane4 a4 b4 rfl rfl l hl
  · rw [o7 _ (by decide) l hl, o6 _ (by decide) l hl]
    exact lane4 a5 b5 rfl rfl l hl
  · rw [o7 _ (by decide) l hl, a6 l hl]; rfl
  · rw [a7 l hl]; rfl
  · rw [g7 g hg, g6 g hg, g5 g hg, g4 g hg, g3 g hg, g2 g hg, g1 g hg]
  · rw [m7, m6, m5, m4, m3, m2, m1]
  · rw [r7, r6, r5, r4, r3, r2, r1]
  · rw [w7, w6, w5, w4, w3, w2, w1]

/-! ## A group -/

/-- A group of `d = 11`: the eight values of the 16 bytes at `rdi` that the masks `M` select, decompressed,
stored to `rsi`. -/
theorem body11_ok {m : XReg} {M : Nat → BitVec 128} (hm : ∀ l < 2, s.lane m l = M l) (hm0 : m ≠ .xmm0)
    (hc : C11 s) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 16) (hout : InRegions s.wr (s.gpr .rsi) 32)
    (k : ∀ s', Hi s s' → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∃ V : BitVec 256, s'.mem = s.mem.writeW (s.gpr .rsi) V ∧ ∀ i < 8, V.extractLsb' (32 * i) 32 =
        dword (ddM (vals (s.mem.readW (s.gpr .rdi) 128) (M (i / 4)) (if i / 4 = 0 then sh11a else sh11b) 11)
          (rc 1024) 11) (i % 4)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (dd11Grp m ++ is)) s Q := by
  simp only [dd11Grp, yb, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_vbcast128 (a := s.gpr .rdi) (by rw [ea_at, add_ofNat_zero]) hin fun s1 u1 => ?_
  refine wp_vbin fun s2 u2 => wp_vvar fun s3 u3 => wp_vbin fun s4 u4 => ddMul_ok (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) fun s5 v5 o5 g5 m5 r5 w5 => ?_
  have hg : s5.gpr = s.gpr := by rw [g5, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  refine wp_vst256 (a := s.gpr .rsi) (by rw [ea_at, add_ofNat_zero, hg])
    (by rw [w5, u4.wr, u3.wr, u2.wr, u1.wr]; exact hout) fun s6 g6 l6 m6 r6 w6 => ?_
  generalize hL : s.mem.readW (s.gpr .rdi) 128 = L at u1
  have h4 : ∀ l < 2, s4.lane .xmm0 l = vals L (M l) (if l = 0 then sh11a else sh11b) 11 := fun l hl => by
    rw [u4.val l hl, u3.other .xmm10 (by decide) l hl, u3.val l hl, u2.other .xmm9 (by decide) l hl,
      u2.other .xmm10 (by decide) l hl, u2.val l hl, u1.other .xmm9 (by decide) l hl,
      u1.other .xmm10 (by decide) l hl, u1.other m hm0 l hl, u1.val l hl, hm l hl, hc.c9 l hl, hc.c10 l hl]; rfl
  have r4 : ∀ l < 2, s4.lane .xmm11 l = rc 1024 := fun l hl => by
    rw [u4.other _ (by decide) l hl, u3.other _ (by decide) l hl, u2.other _ (by decide) l hl,
      u1.other _ (by decide) l hl, hc.c11 l hl]
  refine k s6 (fun r a b c d _ l hl => ?_) (by rw [g6, hg]) (by rw [r6, r5, u4.rd, u3.rd, u2.rd, u1.rd])
    (by rw [w6, w5, u4.wr, u3.wr, u2.wr, u1.wr]) ⟨s5.ymm .xmm1, by rw [m6, m5, u4.mem, u3.mem, u2.mem, u1.mem],
      fun i hi => ?_⟩
  · rw [l6, o5 r b c d l hl, u4.other r a l hl, u3.other r a l hl, u2.other r a l hl, u1.other r a l hl]
  · rw [State.ymm_eq, ext_app2 _ _ hi, hL]
    by_cases h : i < 4
    · rw [itT h, v5 0 (by decide), h4 0 (by decide), r4 0 (by decide), show i / 4 = 0 by omega_arith]
    · rw [itF h, v5 1 (by decide), h4 1 (by decide), r4 1 (by decide), show i / 4 = 1 by omega_arith]

/-- A group of `d = 5`: the eight values of the bytes of `ymm0` that the masks `M` select, decompressed,
stored to `rsi + 32 k`. -/
theorem body5_ok {m : XReg} {k : Nat} {M : Nat → BitVec 128} {L : BitVec 128}
    (hm : ∀ l < 2, s.lane m l = M l) (h0 : ∀ l < 2, s.lane .xmm0 l = L) (hc : C5 s)
    (hout : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (32 * k)) 32)
    (k' : ∀ s', Kp s s' → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∃ V : BitVec 256, s'.mem = s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (32 * k)) V ∧ ∀ i < 8,
        V.extractLsb' (32 * i) 32 = dword (ddM (vals L (M (i / 4)) (if i / 4 = 0 then sh5a else sh5b) 5) (rc 16) 5)
          (i % 4)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (dd5Grp m k ++ is)) s Q := by
  simp only [dd5Grp, yb, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_vbin fun s1 u1 => wp_vvar fun s2 u2 => wp_vbin fun s3 u3 => ddMul_ok (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) fun s4 v4 o4 g4 m4 r4 w4 => ?_
  have hg : s4.gpr = s.gpr := by rw [g4, u3.gpr, u2.gpr, u1.gpr]
  refine wp_vst256 (a := s.gpr .rsi + BitVec.ofNat 64 (32 * k)) (by rw [ea_at, hg])
    (by rw [w4, u3.wr, u2.wr, u1.wr]; exact hout) fun s5 g5 l5 m5 r5 w5 => ?_
  have h3 : ∀ l < 2, s3.lane .xmm1 l = vals L (M l) (if l = 0 then sh5a else sh5b) 5 := fun l hl => by
    rw [u3.val l hl, u2.other .xmm13 (by decide) l hl, u2.val l hl, u1.other .xmm12 (by decide) l hl,
      u1.other .xmm13 (by decide) l hl, u1.val l hl, h0 l hl, hm l hl, hc.c12 l hl, hc.c13 l hl]; rfl
  have r3 : ∀ l < 2, s3.lane .xmm14 l = rc 16 := fun l hl => by
    rw [u3.other _ (by decide) l hl, u2.other _ (by decide) l hl, u1.other _ (by decide) l hl, hc.c14 l hl]
  refine k' s5 (fun r a b c d l hl => ?_) (by rw [g5, hg]) (by rw [r5, r4, u3.rd, u2.rd, u1.rd])
    (by rw [w5, w4, u3.wr, u2.wr, u1.wr]) ⟨s4.ymm .xmm2, by rw [m5, m4, u3.mem, u2.mem, u1.mem], fun i hi => ?_⟩
  · rw [l5, o4 r b c d l hl, u3.other r a l hl, u2.other r a l hl, u1.other r a l hl]
  · rw [State.ymm_eq, ext_app2 _ _ hi]
    by_cases h : i < 4
    · rw [itT h, v4 0 (by decide), h3 0 (by decide), r3 0 (by decide), show i / 4 = 0 by omega_arith]
    · rw [itF h, v4 1 (by decide), h3 1 (by decide), r3 1 (by decide), show i / 4 = 1 by omega_arith]

end

/-! ## The loops -/

/-- After `i` groups of `d = 11`. -/
structure Inv11 (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = DD.bP s₀ + BitVec.ofNat 64 (11 * i)
  rsi : s.gpr .rsi = coeffAddr (DD.fP s₀) (8 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : C11 s
  frame : Frame [pR (DD.fP s₀)] s₀.mem s.mem
  done : ∀ k < 8 * i, (coeffAt s.mem (DD.fP s₀) k).toNat = ((decodeDecompress 11 (DD.B s₀ 11))[k]!).val

/-- After `i` pairs of groups of `d = 5`. -/
structure Inv5 (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = DD.bP s₀ + BitVec.ofNat 64 (10 * i)
  rsi : s.gpr .rsi = coeffAddr (DD.fP s₀) (16 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : C5 s
  frame : Frame [pR (DD.fP s₀)] s₀.mem s.mem
  done : ∀ k < 16 * i, (coeffAt s.mem (DD.fP s₀) k).toNat = ((decodeDecompress 5 (DD.B s₀ 5))[k]!).val

section
variable {s₀ : State} (hp : decodeDecompress1024K.pre s₀)
include hp

theorem regs {d : Nat} (hdd : dArg s₀ .rdx = d) : s₀.rd ++ s₀.wr = [⟨DD.bP s₀, 32 * d⟩, pR (DD.fP s₀)] := by
  rw [hp.1, hp.2.1, DD.lenEq hp hdd]; rfl

/-- Group `g` of `d = 11`, from the 16 bytes at `bP + ob'`, the group's from `ob`. -/
theorem group11 (hdd : dArg s₀ .rdx = 11) {g ob' ob : Nat} (hg : g < 32) (hob : ob' + ob = 11 * g)
    (ho : ob' + 16 ≤ 352) (ho' : ob + 11 ≤ 16) {m : XReg} {M : Nat → BitVec 128} {is : List Instr} {s : State}
    {Q : State → Prop} (hm : ∀ l < 2, s.lane m l = M l) (hm0 : m ≠ .xmm0) (hM : ∀ l < 2, Sel 11 (M l) ob l)
    (hdi : s.gpr .rdi = DD.bP s₀ + BitVec.ofNat 64 ob') (hsi : s.gpr .rsi = coeffAddr (DD.fP s₀) (8 * g))
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hc : C11 s) (hf : Frame [pR (DD.fP s₀)] s₀.mem s.mem)
    (hd : ∀ k < 8 * g, (coeffAt s.mem (DD.fP s₀) k).toNat = ((decodeDecompress 11 (DD.B s₀ 11))[k]!).val)
    (k : ∀ s', C11 s' → s'.gpr = s.gpr → s'.rd = s₀.rd → s'.wr = s₀.wr → Frame [pR (DD.fP s₀)] s₀.mem s'.mem →
      (∀ k < 8 * (g + 1), (coeffAt s'.mem (DD.fP s₀) k).toNat = ((decodeDecompress 11 (DD.B s₀ 11))[k]!).val) →
      WP isa (.block is) s' Q) :
    WP isa (.block (dd11Grp m ++ is)) s Q := by
  have hrw : s.rd ++ s.wr = [⟨DD.bP s₀, 32 * 11⟩, pR (DD.fP s₀)] := by rw [hrd, hwr, regs hp hdd]
  refine body11_ok hm hm0 hc (by rw [hrw, hdi]; exact ⟨_, by simp, Offset.contains_base _ ho (by omega_arith)⟩)
    (by rw [hwr, hp.2.1, hsi]; exact ⟨_, List.mem_singleton_self _,
      Offset.contains_base _ (show 4 * (8 * g) + 32 ≤ 1024 by omega_arith) (by omega_arith)⟩)
    fun s' hk' hg' hrd' hwr' ⟨V, hmem, hV⟩ => k s' (hc.pres hk') hg' (by rw [hrd', hrd]) (by rw [hwr', hwr]) ?_ ?_
  · rw [hmem, hsi]
    exact hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (show 4 * (8 * g) + 256 / 8 ≤ 1024 by omega_arith) (by omega_arith))
  · intro c hcl
    have hL : ∀ t < 11, byte (s.mem.readW (s.gpr .rdi) 128) (ob + t) = (DD.B s₀ 11).getD (11 * g + t) 0 :=
      fun t ht => by
        rw [byte, byte_readW _ _ (by omega_arith), hdi, Offset.add_add, DD.byte hp (by decide) hdd hf (by omega_arith),
          show ob' + (ob + t) = 11 * g + t by omega_arith]
    rw [hmem, hsi, D12Y.coeffAt_write8 _ _ _ hg (by omega_arith)]
    split
    · rename_i hin
      rw [hV _ (by omega_arith), valW (.inr rfl) (bytesAt_length _ _ _) hg hL (show (c - 8 * g) / 4 < 2 by omega_arith)
        (hM _ (by omega_arith)) (hS11 _ (by omega_arith)) (by decide) (by omega_arith),
        show 8 * g + (4 * ((c - 8 * g) / 4) + (c - 8 * g) % 4) = c by omega_arith]
    · exact hd c (by omega_arith)

/-- Group `k` of pair `p` of `d = 5`, of the 16 bytes `L` in `ymm0`, the group's from `ob`. -/
theorem group5 {p k ob : Nat} (hp16 : p < 16) (hk : k < 2) {m : XReg}
    {M : Nat → BitVec 128} {L : BitVec 128} {is : List Instr} {s : State} {Q : State → Prop}
    (hm : ∀ l < 2, s.lane m l = M l) (hM : ∀ l < 2, Sel 5 (M l) ob l) (h0 : ∀ l < 2, s.lane .xmm0 l = L)
    (hL : ∀ t < 5, byte L (ob + t) = (DD.B s₀ 5).getD (5 * (2 * p + k) + t) 0)
    (hsi : s.gpr .rsi = coeffAddr (DD.fP s₀) (16 * p)) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hc : C5 s)
    (hf : Frame [pR (DD.fP s₀)] s₀.mem s.mem)
    (hd : ∀ c < 16 * p + 8 * k, (coeffAt s.mem (DD.fP s₀) c).toNat = ((decodeDecompress 5 (DD.B s₀ 5))[c]!).val)
    (k' : ∀ s', C5 s' → (∀ l < 2, s'.lane .xmm0 l = L) → s'.gpr = s.gpr → s'.rd = s₀.rd → s'.wr = s₀.wr →
      Frame [pR (DD.fP s₀)] s₀.mem s'.mem →
      (∀ c < 16 * p + 8 * (k + 1), (coeffAt s'.mem (DD.fP s₀) c).toNat =
        ((decodeDecompress 5 (DD.B s₀ 5))[c]!).val) →
      WP isa (.block is) s' Q) :
    WP isa (.block (dd5Grp m k ++ is)) s Q := by
  have ha : s.gpr .rsi + BitVec.ofNat 64 (32 * k) = coeffAddr (DD.fP s₀) (8 * (2 * p + k)) := by
    rw [hsi, coeffAddr, coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 4 * (16 * p) + 32 * k = 4 * (8 * (2 * p + k)) by omega_arith]
  refine body5_ok hm h0 hc (by rw [hwr, hp.2.1, ha]; exact ⟨_, List.mem_singleton_self _,
      Offset.contains_base _ (show 4 * (8 * (2 * p + k)) + 32 ≤ 1024 by omega_arith) (by omega_arith)⟩)
    fun s' hk' hg' hrd' hwr' ⟨V, hmem, hV⟩ => k' s' (hc.pres fun r _ a b c d l hl => hk' r a b c d l hl)
      (fun l hl => by rw [hk' _ (by decide) (by decide) (by decide) (by decide) l hl, h0 l hl]) hg'
      (by rw [hrd', hrd]) (by rw [hwr', hwr]) ?_ ?_
  · rw [hmem, ha]
    exact hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (show 4 * (8 * (2 * p + k)) + 256 / 8 ≤ 1024 by omega_arith) (by omega_arith))
  · intro c hcl
    rw [hmem, ha, D12Y.coeffAt_write8 _ _ _ (show 2 * p + k < 32 by omega_arith) (by omega_arith)]
    split
    · rename_i hin
      rw [hV _ (by omega_arith), valW (.inl rfl) (bytesAt_length _ _ _) (show 2 * p + k < 32 by omega_arith) hL
        (show (c - 8 * (2 * p + k)) / 4 < 2 by omega_arith) (hM _ (by omega_arith)) (hS5 _ (by omega_arith)) (by decide) (by omega_arith),
        show 8 * (2 * p + k) + (4 * ((c - 8 * (2 * p + k)) / 4) + (c - 8 * (2 * p + k)) % 4) = c by omega_arith]
    · exact hd c (by omega_arith)

theorem step11 (hdd : dArg s₀ .rdx = 11) {i : Nat} (hi : i < 31) {s : State} (hI : Inv11 s₀ i s) :
    WP isa (.block (dd11Grp .xmm8 ++
        ([.alu .add .rdi (.imm 11), .alu .add .rsi (.imm 32), .alu .sub .rcx (.imm 1)] : List Instr)))
      s fun s' => Inv11 s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  refine group11 hp hdd (g := i) (ob' := 11 * i) (ob := 0) (by omega_arith) (by omega_arith) (by omega_arith) (by decide) hI.c.c8
    (by decide) hM11 hI.rdi hI.rsi hI.rd hI.wr hI.c hI.frame hI.done fun s1 hc1 hg1 hrd1 hwr1 hf1 hd1 => ?_
  refine wp_addi' fun s2 u2 => wp_addi' fun s3 u3 => wp_subi' fun s4 u4 hz => WP.block_nil ?_
  have c4 := ((hc1.pres (Hi.of_lane u2.lane)).pres (Hi.of_lane u3.lane)).pres (Hi.of_lane u4.lane)
  refine ⟨⟨?_, ?_, by rw [u4.rd, u3.rd, u2.rd, hrd1], by rw [u4.wr, u3.wr, u2.wr, hwr1], c4,
    by rw [u4.mem, u3.mem, u2.mem]; exact hf1, fun k hk => by rw [u4.mem, u3.mem, u2.mem]; exact hd1 k hk⟩, ?_, ?_⟩
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, hg1, hI.rdi,
      show BitVec.signExtend 64 (11 : BitVec 32) = BitVec.ofNat 64 11 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 11 * i + 11 = 11 * (i + 1) by omega_arith]
  · rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), hg1, hI.rsi, coeffAddr, coeffAddr,
      show BitVec.signExtend 64 (32 : BitVec 32) = BitVec.ofNat 64 32 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 4 * (8 * i) + 32 = 4 * (8 * (i + 1)) by omega_arith]
  · rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), hg1]; rfl
  · rw [hz, u3.other _ (by decide), u2.other _ (by decide), hg1]; rfl

theorem step5 (hdd : dArg s₀ .rdx = 5) {i : Nat} (hi : i < 15) {s : State} (hI : Inv5 s₀ i s) :
    WP isa (.block (.vbroadcasti128 .xmm0 (at_ .rdi 0) :: dd5Grp .xmm8 0 ++ dd5Grp .xmm9 1 ++
        ([.alu .add .rdi (.imm 10), .alu .add .rsi (.imm 64), .alu .sub .rcx (.imm 1)] : List Instr))) s
      fun s' => Inv5 s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  simp only [List.cons_append, List.append_assoc]
  have hrw : s.rd ++ s.wr = [⟨DD.bP s₀, 32 * 5⟩, pR (DD.fP s₀)] := by rw [hI.rd, hI.wr, regs hp hdd]
  refine wp_vbcast128 (a := s.gpr .rdi) (by rw [ea_at, add_ofNat_zero]) (by
    rw [hrw, hI.rdi]; exact ⟨_, by simp, Offset.contains_base _ (show 10 * i + 16 ≤ 32 * 5 by omega_arith) (by omega_arith)⟩)
    fun s1 u1 => ?_
  have hL : ∀ t < 16, byte (s.mem.readW (s.gpr .rdi) 128) t = (DD.B s₀ 5).getD (10 * i + t) 0 := fun t ht => by
    rw [byte, byte_readW _ _ (by omega_arith), hI.rdi, Offset.add_add, DD.byte hp (by decide) hdd hI.frame (by omega_arith)]
  have c1 := hI.c.pres fun r a _ _ _ _ l hl => u1.other r a l hl
  refine group5 hp (p := i) (k := 0) (ob := 0) (by omega_arith) (by decide) c1.c8 hM5 u1.val
    (fun t ht => by rw [hL _ (by omega_arith), show 0 + t = t by omega_arith, show 5 * (2 * i + 0) + t = 10 * i + t by omega_arith])
    (by rw [u1.gpr, hI.rsi]) (by rw [u1.rd, hI.rd]) (by rw [u1.wr, hI.wr]) c1 (by rw [u1.mem]; exact hI.frame)
    (fun c hc => by rw [u1.mem]; exact hI.done c (by omega_arith)) fun s2 c2 x2 g2 r2 w2 f2 d2 => ?_
  refine group5 hp (p := i) (k := 1) (ob := 5) (by omega_arith) (by decide) c2.c9 hM5' x2
    (fun t ht => by rw [hL _ (by omega_arith), show 5 * (2 * i + 1) + t = 10 * i + (5 + t) by omega_arith])
    (by rw [g2, u1.gpr, hI.rsi]) r2 w2 c2 f2 d2 fun s3 c3 _ g3 r3 w3 f3 d3 => ?_
  have hg3 : s3.gpr = s.gpr := by rw [g3, g2, u1.gpr]
  refine wp_addi' fun s4 u4 => wp_addi' fun s5 u5 => wp_subi' fun s6 u6 hz => WP.block_nil ?_
  have c6 := ((c3.pres (Hi.of_lane u4.lane)).pres (Hi.of_lane u5.lane)).pres (Hi.of_lane u6.lane)
  refine ⟨⟨?_, ?_, by rw [u6.rd, u5.rd, u4.rd, r3], by rw [u6.wr, u5.wr, u4.wr, w3], c6,
    by rw [u6.mem, u5.mem, u4.mem]; exact f3, fun c hc => by rw [u6.mem, u5.mem, u4.mem]; exact d3 c (by omega_arith)⟩,
    ?_, ?_⟩
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, hg3, hI.rdi,
      show BitVec.signExtend 64 (10 : BitVec 32) = BitVec.ofNat 64 10 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 10 * i + 10 = 10 * (i + 1) by omega_arith]
  · rw [u6.other _ (by decide), u5.gpr, u4.other _ (by decide), hg3, hI.rsi, coeffAddr, coeffAddr,
      show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 4 * (16 * i) + 64 = 4 * (16 * (i + 1)) by omega_arith]
  · rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), hg3]; rfl
  · rw [hz, u5.other _ (by decide), u4.other _ (by decide), hg3]; rfl

/-- The postcondition of the loops. -/
abbrev Done (d : Nat) (s : State) : Prop := Frame [pR (DD.fP s₀)] s₀.mem s.mem ∧
  ∀ k < 256, (coeffAt s.mem (DD.fP s₀) k).toNat = ((decodeDecompress d (DD.B s₀ d))[k]!).val

theorem main11 (hdd : dArg s₀ .rdx = 11) {s : State} (hdi : s.gpr .rdi = DD.bP s₀)
    (hsi : s.gpr .rsi = DD.fP s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa dd11V s (Done (s₀ := s₀) 11) := by
  unfold dd11V
  refine WP.seq (consts11_ok fun s1 hc1 hg1 hm1 hr1 hw1 => wp_mov32i fun s2 u2 => WP.block_nil ?_)
  refine WP.seq (wp_countdown (cnt := .rcx) (N := 31) (by decide) (by decide) (Inv11 s₀)
    (fun i hi s hI _ => step11 hp hdd hi hI) (fun s hI => ?_) (s := s2) ⟨?_, ?_, by rw [u2.rd, hr1, hrd],
      by rw [u2.wr, hw1, hwr], hc1.pres (Hi.of_lane u2.lane), by rw [u2.mem, hm1, hm]; exact Frame.refl _ _,
      fun k hk => absurd hk (by omega_arith)⟩ (by rw [u2.gpr]; rfl))
  · refine wp_subi' fun s3 u3 _ => group11 hp hdd (g := 31) (ob' := 336) (ob := 5) (by decide) (by decide)
      (by decide) (by decide) (fun l hl => by rw [u3.lane, hI.c.c12 l hl]) (by decide) hM11' ?_
      (by rw [u3.other _ (by decide), hI.rsi]) (by rw [u3.rd, hI.rd]) (by rw [u3.wr, hI.wr])
      (hI.c.pres (Hi.of_lane u3.lane)) (by rw [u3.mem]; exact hI.frame) (fun k hk => by rw [u3.mem]; exact hI.done k hk)
      fun s4 _ _ _ _ hf4 hd4 => wp_vzu fun s5 _ hm5 _ _ => WP.block_nil ⟨by rw [hm5]; exact hf4,
        fun k hk => by rw [hm5]; exact hd4 k hk⟩
    rw [u3.gpr, hI.rdi, show BitVec.signExtend 64 (5 : BitVec 32) = BitVec.ofNat 64 5 by decide,
      Offset.add_ofNat_sub _ (by decide)]
  · rw [u2.other _ (by decide), hg1 _ (by decide), hdi]; simp
  · rw [u2.other _ (by decide), hg1 _ (by decide), hsi]; simp

theorem main5 (hdd : dArg s₀ .rdx = 5) {s : State} (hdi : s.gpr .rdi = DD.bP s₀)
    (hsi : s.gpr .rsi = DD.fP s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa dd5V s (Done (s₀ := s₀) 5) := by
  unfold dd5V
  refine WP.seq (consts5_ok fun s1 hc1 hg1 hm1 hr1 hw1 => wp_mov32i fun s2 u2 => WP.block_nil ?_)
  refine WP.seq (wp_countdown (cnt := .rcx) (N := 15) (by decide) (by decide) (Inv5 s₀)
    (fun i hi s hI _ => step5 hp hdd hi hI) (fun s hI => ?_) (s := s2) ⟨?_, ?_, by rw [u2.rd, hr1, hrd],
      by rw [u2.wr, hw1, hwr], hc1.pres (Hi.of_lane u2.lane), by rw [u2.mem, hm1, hm]; exact Frame.refl _ _,
      fun k hk => absurd hk (by omega_arith)⟩ (by rw [u2.gpr]; rfl))
  · refine wp_subi' fun s3 u3 _ => ?_
    have hdi3 : s3.gpr .rdi = DD.bP s₀ + BitVec.ofNat 64 144 := by
      rw [u3.gpr, hI.rdi, show BitVec.signExtend 64 (6 : BitVec 32) = BitVec.ofNat 64 6 by decide,
        Offset.add_ofNat_sub _ (by decide)]
    have hrw : s3.rd ++ s3.wr = [⟨DD.bP s₀, 32 * 5⟩, pR (DD.fP s₀)] := by rw [u3.rd, u3.wr, hI.rd, hI.wr, regs hp hdd]
    refine wp_vbcast128 (a := s3.gpr .rdi) (by rw [ea_at, add_ofNat_zero]) (by
      rw [hrw, hdi3]; exact ⟨_, by simp, Offset.contains_base _ (show 144 + 16 ≤ 32 * 5 by omega_arith) (by omega_arith)⟩)
      fun s4 u4 => ?_
    have hL : ∀ t < 16, byte (s3.mem.readW (s3.gpr .rdi) 128) t = (DD.B s₀ 5).getD (144 + t) 0 := fun t ht => by
      rw [byte, byte_readW _ _ (by omega_arith), hdi3, Offset.add_add, u3.mem,
        DD.byte hp (by decide) hdd hI.frame (by omega_arith)]
    have c4 := (hI.c.pres (Hi.of_lane u3.lane)).pres fun r a _ _ _ _ l hl => u4.other r a l hl
    refine group5 hp (p := 15) (k := 0) (ob := 6) (by decide) (by decide) c4.c10 hM5'' u4.val
      (fun t ht => by rw [hL _ (by omega_arith), show 5 * (2 * 15 + 0) + t = 144 + (6 + t) by omega_arith])
      (by rw [u4.gpr, u3.other _ (by decide), hI.rsi]) (by rw [u4.rd, u3.rd, hI.rd]) (by rw [u4.wr, u3.wr, hI.wr]) c4
      (by rw [u4.mem, u3.mem]; exact hI.frame) (fun c hc => by rw [u4.mem, u3.mem]; exact hI.done c (by omega_arith))
      fun s5 c5 x5 g5 r5 w5 f5 d5 => ?_
    refine group5 hp (p := 15) (k := 1) (ob := 11) (by decide) (by decide) c5.c11 hM5''' x5
      (fun t ht => by rw [hL _ (by omega_arith), show 5 * (2 * 15 + 1) + t = 144 + (11 + t) by omega_arith])
      (by rw [g5, u4.gpr, u3.other _ (by decide), hI.rsi]) r5 w5 c5 f5 d5 fun s6 _ _ _ _ _ f6 d6 => ?_
    exact wp_vzu fun s7 _ hm7 _ _ => WP.block_nil ⟨by rw [hm7]; exact f6, fun k hk => by rw [hm7]; exact d6 k hk⟩
  · rw [u2.other _ (by decide), hg1 _ (by decide), hdi]; simp
  · rw [u2.other _ (by decide), hg1 _ (by decide), hsi]; simp

end

theorem wp {s₀ : State} (hp : decodeDecompress1024K.pre s₀) :
    WP isa decodeDecompress1024Avx2 s₀ fun s' =>
      PolyIs s'.mem (s₀.gpr .rcx) (decodeDecompress (dArg s₀ .rdx) (bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat)) ∧
        Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem := by
  have hd := hp.2.2.2.2.2.1
  rw [DD.lenEq hp rfl]
  unfold decodeDecompress1024Avx2
  refine WP.seq (WP.mono (MlKem1024.X86_64.ddPrologue_ok s₀) fun s₁ ⟨⟨_, si₁, z₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  have fin : ∀ {d : Nat}, dArg s₀ .rdx = d → ∀ s : State, Done (s₀ := s₀) d s →
      PolyIs s.mem (s₀.gpr .rcx) (decodeDecompress (dArg s₀ .rdx) (bytesAt s₀.mem (s₀.gpr .rdi)
        (32 * dArg s₀ .rdx))) ∧ Frame [pR (s₀.gpr .rcx)] s₀.mem s.mem := by
    intro d hdd s ⟨hf, hk⟩
    rw [hdd]
    exact ⟨polyIs_of_toNat hk, hf⟩
  refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from z₁) (fun h => ?_) (fun h => ?_)
  · rw [sub_beq_zero32, decide_eq_true_eq] at h
    have h5 : dArg s₀ .rdx = 5 := by simp only [dArg, h]; rfl
    exact WP.mono (main5 hp h5 di₁ si₁ k₁.2.1 k₁.2.2 m₁) (fin h5)
  · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
    have h11 : dArg s₀ .rdx = 11 := by
      rcases MlKem1024.X86_64.widths1024 hd with e | e
      · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h
      · exact e
    exact WP.mono (main11 hp h11 di₁ si₁ k₁.2.1 k₁.2.2 m₁) (fin h11)

theorem correct (s : State) (hs : decodeDecompress1024K.pre s) :
    ∃ t s', Exec isa decodeDecompress1024Avx2 s t s' ∧ abiPreserved s s' ∧ decodeDecompress1024K.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := decodeDecompress1024Avx2)
    [.rax, .rcx, .rdx, .rsi, .rdi, .r9, .r10] (wp hs) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

end VG.Proof.MlKem1024.X86_64.DDW

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem1024.X86_64 VG.Proof.MlKem.X86_64

theorem decodeDecompress1024Y_ct :
    ConstantTime isa decodeDecompress1024K.pre decodeDecompress1024K.pub decodeDecompress1024Avx2 :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rsi, .rcx, .rsp] [.rdx])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

/-- `vg_mlkem1024_decode_decompress_avx2`, for the calls of the top-level functions. -/
theorem ddImpl1024Y : DDImpl "vg_mlkem1024_decode_decompress_avx2" decodeDecompress1024Avx2
    Proof.MlKem1024.compressWidths :=
  ⟨fun _ hd => by rcases widths1024 hd with rfl | rfl <;> decide, DDW.correct, decodeDecompress1024Y_ct,
    nosp_of (by decide +kernel), by decide +kernel⟩

end VG.Proof.MlKem1024.X86_64
