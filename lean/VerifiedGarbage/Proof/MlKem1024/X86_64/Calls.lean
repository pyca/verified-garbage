module

public import VerifiedGarbage.Proof.MlKem.X86_64.EncBase
public import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress
public import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Proof.MlKem.Compress1024
public import VerifiedGarbage.Impl.MlKem1024.X86_64.CompressAvx2
public import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncodeAvx2
public import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim
import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.MlKem1024.X86_64.CompressAvx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncodeAvx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncode
meta import VerifiedGarbage.Proof.MlKem.Compress1024
meta import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompressAvx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompressAvx2
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress

/-! ### `MlKem1024.X86_64.DecodeDecompressAvx2`, which only this module used -/

section

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

end

end

/-! ### `MlKem1024.X86_64.CompressEncodeAvx2`, which only this module used -/

section

/-!
# ML-KEM-1024 on x86-64: `ByteEncode_d ∘ Compress_d` with AVX2, which the K-PKE functions inline

As ML-KEM-768's (`Proof/MlKem/X86_64/CompressEncodeAvx2.lean`): the
doublewords of a group are compressed by sums of shifts (`dword_mul11`,
`dword_mul5`), and a lane of four values is packed into the number whose
base-`2ᵈ` digits they are, times `2⁴` in the high lane (`pk_q0`); `vpshufb`
places each lane's bytes (`shufA11`, …), and the two lanes, which share a
byte, are merged by `vpor` into the group's number (`pack11`, `pack5`).
-/

@[expose] public section

namespace VG.Proof.MlKem1024.X86_64.CEW

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.Sha3.X86_64 (WP.cons)
open VG.Proof.MlKem.X86_64.S4 (LUpd wp_vbin wp_vvar wp_vld256 GUpd wp_addi' itT itF ext_app2)
open VG.Proof.MlKem.X86_64.D12Y (wp_vsh wp_subi' wp_vzu wp_mov32i yconst4_ok yconst_ok' wp_vbin128)
open VG.Proof.MlKem.X86_64.DDY (mk rc dword_mk dword_rc toNat_and_mk lane4)
open VG.Proof.MlKem.X86_64.CEY (toNat_byte ext_byte byte_ofBytes toNat_qword0 toNat_qword1 toNat_byte_lo
  qword_app0 qword_app1 pairs W laneEq wp_vsh128 wp_vmovdqa128 wp_vext1 wp_vst128 Hi7 dword_ld written16
  byte_ofNat128)

/-! ## Compression of a doubleword -/

/-- `x · 322542` and `x · 5040`, by sums of shifts (`ceMul11`, `ceMul5`). -/
abbrev mul11 (x : BitVec 128) : BitVec 128 :=
  XBinOp.eval .psubd (XBinOp.eval .psubd (XBinOp.eval .paddd (XShiftOp.eval .pslld x (BitVec.ofNat 8 18))
      (XShiftOp.eval .pslld x (BitVec.ofNat 8 16)))
    (XBinOp.eval .paddd (XShiftOp.eval .pslld x (BitVec.ofNat 8 12)) (XShiftOp.eval .pslld x (BitVec.ofNat 8 10))))
    (XBinOp.eval .paddd (XShiftOp.eval .pslld x (BitVec.ofNat 8 4)) (XShiftOp.eval .pslld x (BitVec.ofNat 8 1)))

abbrev mul5 (x : BitVec 128) : BitVec 128 :=
  XBinOp.eval .psubd (XBinOp.eval .paddd (XShiftOp.eval .pslld x (BitVec.ofNat 8 12))
      (XShiftOp.eval .pslld x (BitVec.ofNat 8 10)))
    (XBinOp.eval .paddd (XShiftOp.eval .pslld x (BitVec.ofNat 8 6)) (XShiftOp.eval .pslld x (BitVec.ofNat 8 4)))

/-- `((y + 261888) >> 19) ∧ (2ᵈ - 1)` (`ceRound`, with ML-KEM-1024's constant). -/
abbrev rnd (y : BitVec 128) (d : Nat) : BitVec 128 :=
  XBinOp.eval .pand (XShiftOp.eval .psrld (XBinOp.eval .paddd y (rc 261888)) (BitVec.ofNat 8 19)) (mk d)

theorem dword_mul11 (x : BitVec 128) {j : Nat} (hj : j < 4) (hx : (dword x j).toNat < 3329) :
    (dword (mul11 x) j).toNat = (dword x j).toNat * 322542 := by
  rw [dword_psubd _ _ hj, dword_psubd _ _ hj, dword_paddd _ _ hj, dword_paddd _ _ hj, dword_paddd _ _ hj,
    dword_pslld _ _ (by decide) hj, dword_pslld _ _ (by decide) hj, dword_pslld _ _ (by decide) hj,
    dword_pslld _ _ (by decide) hj, dword_pslld _ _ (by decide) hj, dword_pslld _ _ (by decide) hj]
  generalize dword x j = y at hx ⊢
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod]
  omega_arith

theorem dword_mul5 (x : BitVec 128) {j : Nat} (hj : j < 4) (hx : (dword x j).toNat < 3329) :
    (dword (mul5 x) j).toNat = (dword x j).toNat * 5040 := by
  rw [dword_psubd _ _ hj, dword_paddd _ _ hj, dword_paddd _ _ hj,
    dword_pslld _ _ (by decide) hj, dword_pslld _ _ (by decide) hj, dword_pslld _ _ (by decide) hj,
    dword_pslld _ _ (by decide) hj]
  generalize dword x j = y at hx ⊢
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod]
  omega_arith

theorem dword_rnd (y : BitVec 128) {d : Nat} (hd : d ≤ 31) {j : Nat} (hj : j < 4)
    (hy : (dword y j).toNat + 261888 < 2 ^ 32) :
    (dword (rnd y d) j).toNat = ((dword y j).toNat + 261888) / 2 ^ 19 % 2 ^ d := by
  rw [dword_pand, dword_mk hj, toNat_and_mk hd, dword_psrld _ _ (by decide) hj, dword_paddd _ _ hj, dword_rc hj,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [show (BitVec.ofNat 8 19).toNat = 19 from rfl]
  rw [Nat.mod_eq_of_lt hy]

/-! ## Packing -/

/-- The constants of the packing: the shifts of `vpsllvd` (`ymm8`), the masks
of each quadword (`ymm9`), the shifts of `vpsllvq` of each lane (`ymm10`), and
the masks of `vpshufb` of each lane (`ymm11`). -/
def sv11 : BitVec 128 := 0x0000000b000000000000000b00000000#128
def qm22 : BitVec 128 := 0x00000000003fffff00000000003fffff#128
def qsA11 : BitVec 128 := 0x00000000000000160000000000000000#128
def qsB11 : BitVec 128 := 0x000000000000001a0000000000000004#128
def pmA11 : BitVec 128 := 0x80808080808080808080050403020100#128
def pmB11 : BitVec 128 := 0x80808080800504030201008080808080#128
def sv5 : BitVec 128 := 0x00000005000000000000000500000000#128
def qm10 : BitVec 128 := 0x00000000000003ff00000000000003ff#128
def qsA5 : BitVec 128 := 0x000000000000000a0000000000000000#128
def qsB5 : BitVec 128 := 0x000000000000000e0000000000000004#128
def pmA5 : BitVec 128 := 0x80808080808080808080808080020100#128
def pmB5 : BitVec 128 := 0x80808080808080808080800201008080#128

/-- A lane packed (`cePack true` before `vextracti128`), with the constants `S`, `Q`, `QS` and `M`. -/
abbrev pk (R S Q QS M : BitVec 128) : BitVec 128 :=
  let E := VVarOp.eval .vpsllvq (XBinOp.eval .pand (pairs R S) Q) QS
  XBinOp.eval .pshufb (XBinOp.eval .paddq E (XShiftOp.eval .psrldq E 8)) M

/-- The doublewords of `pairs`: each odd value shifted left by `d` and added to the even one before it. -/
theorem dword_pairs {d : Nat} (hd : d ≤ 11) {R S : BitVec 128}
    (hS : (dword S 0).toNat = 0 ∧ (dword S 1).toNat = d ∧ (dword S 2).toNat = 0 ∧ (dword S 3).toNat = d)
    {a : Nat → Nat} (ha : ∀ j < 4, (dword R j).toNat = a j) (hb : ∀ j < 4, a j < 2 ^ d) :
    (dword (pairs R S) 0).toNat = a 0 + a 1 * 2 ^ d ∧ (dword (pairs R S) 2).toNat = a 2 + a 3 * 2 ^ d := by
  dsimp only [pairs]
  obtain ⟨h0, h1, h2, h3⟩ := hS
  have hd'' : 2 ^ d ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hd
  have b0 := hb 0 (by decide); have b1 := hb 1 (by decide); have b2 := hb 2 (by decide)
  have b3 := hb 3 (by decide)
  have hp22 : 2 ^ d * 2 ^ d ≤ 2 ^ 22 := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega_arith)
  have m1 : a 1 * 2 ^ d < 2 ^ 22 := Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right b1 (Nat.two_pow_pos d)) hp22
  have m3 : a 3 * 2 ^ d < 2 ^ 22 := Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right b3 (Nat.two_pow_pos d)) hp22
  rw [CEY.psrlq32, dword_paddd _ _ (by decide), dword_paddd _ _ (by decide), dword_ofDwords_0, dword_ofDwords_2]
  simp only [VVarOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, h0, h1, h2, h3,
    show 0 < 32 by decide, show d < 32 by omega_arith, ↓reduceIte, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), Nat.pow_zero,
    Nat.mul_one]
  generalize a 1 * 2 ^ d = c1 at m1 ⊢
  generalize a 3 * 2 ^ d = c3 at m3 ⊢
  omega_arith

/-- `pk` before `vpshufb`: its low quadword holds the four values packed, shifted left by `s`. -/
theorem pk_q0 {d s : Nat} (hds : (d = 5 ∨ d = 11) ∧ (s = 0 ∨ s = 4)) {R S Q QS : BitVec 128}
    (hS : (dword S 0).toNat = 0 ∧ (dword S 1).toNat = d ∧ (dword S 2).toNat = 0 ∧ (dword S 3).toNat = d)
    (hQ : dword Q 0 = BitVec.ofNat 32 (2 ^ (2 * d) - 1) ∧ dword Q 1 = 0#32 ∧
      dword Q 2 = BitVec.ofNat 32 (2 ^ (2 * d) - 1) ∧ dword Q 3 = 0#32)
    (hQS : (qword QS 0).toNat = s ∧ (qword QS 1).toNat = s + 2 * d) (M : BitVec 128)
    {a : Nat → Nat} (ha : ∀ j < 4, (dword R j).toNat = a j) (hb : ∀ j < 4, a j < 2 ^ d) :
    ∃ G, pk R S Q QS M = XBinOp.eval .pshufb G M ∧ (qword G 0).toNat = 2 ^ s * W d a := by
  obtain ⟨hC0, hC2⟩ := dword_pairs (S := S) (by omega_arith) hS ha hb
  have b0 := hb 0 (by decide); have b1 := hb 1 (by decide); have b2 := hb 2 (by decide)
  have b3 := hb 3 (by decide)
  refine ⟨_, rfl, ?_⟩
  generalize pairs R S = C at hC0 hC2
  obtain ⟨q0, q1, q2, q3⟩ := hQ
  obtain ⟨s0, s1⟩ := hQS
  have hD0 : (qword (XBinOp.eval .pand C Q) 0).toNat = (dword C 0).toNat % 2 ^ (2 * d) := by
    rw [toNat_qword0, dword_pand, dword_pand, q0, q1, toNat_and_mk (by omega_arith), BitVec.and_zero]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
  have hD1 : (qword (XBinOp.eval .pand C Q) 1).toNat = (dword C 2).toNat % 2 ^ (2 * d) := by
    rw [toNat_qword1, dword_pand, dword_pand, q2, q3, toNat_and_mk (by omega_arith), BitVec.and_zero]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
  generalize XBinOp.eval .pand C Q = D at hD0 hD1
  have hE : VVarOp.eval .vpsllvq D QS = (qword D 1 <<< (s + 2 * d)) ++ (qword D 0 <<< s) := by
    simp only [VVarOp.eval, s0, s1, show s < 64 by omega_arith, show s + 2 * d < 64 by omega_arith, ↓reduceIte]
  have hF : ∀ E : BitVec 128, (qword (XShiftOp.eval .psrldq E 8) 0).toNat = (qword E 1).toNat := fun E => by
    simp only [XShiftOp.eval, show (8 : BitVec 8).toNat = 8 from rfl, show min 8 16 * 8 = 64 from rfl, CEY.toNat_qword,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one]
  simp only [XBinOp.eval, qword_app0, qword_app1, BitVec.toNat_add, hF, hE, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    hD0, hD1, hC0, hC2, W]
  rcases hds with ⟨rfl | rfl, rfl | rfl⟩ <;>
    simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceAdd] at b0 b1 b2 b3 ⊢ <;> omega_using [b0, b1, b2, b3]

/-- The byte `t` of `q mod 2^(8 n)`: that of `q` below byte `n`, and zero from there. -/
private theorem byte_mod (q n t : Nat) :
    q % 2 ^ (8 * n) / 2 ^ (8 * t) % 2 ^ 8 = if t < n then q / 2 ^ (8 * t) % 2 ^ 8 else 0 := by
  by_cases h : t < n
  · simp only [h, ↓reduceIte]
    obtain ⟨v, rfl⟩ : ∃ v, n = t + (v + 1) := ⟨n - t - 1, by omega⟩
    rw [Nat.mul_add, Nat.pow_add, Nat.mod_mul_right_div_self, Nat.mul_add, Nat.mul_one, Nat.pow_add,
      Nat.mod_mul_left_mod]
  · simp only [h, ↓reduceIte]
    rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) (by omega))), Nat.zero_mod]

/-- The byte `t` of `q mod 2^(8 n)` moved up by `k` bytes. -/
private theorem byte_shl_mod (q k n t : Nat) :
    2 ^ (8 * k) * (q % 2 ^ (8 * n)) / 2 ^ (8 * t) % 2 ^ 8 =
      if k ≤ t ∧ t < k + n then q / 2 ^ (8 * (t - k)) % 2 ^ 8 else 0 := by
  by_cases h1 : k ≤ t
  · obtain ⟨u, rfl⟩ : ∃ u, t = k + u := ⟨t - k, by omega⟩
    rw [Nat.mul_add, Nat.pow_add, Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _), Nat.add_sub_cancel_left,
      byte_mod]
    simp only [Nat.le_add_right, true_and, Nat.add_lt_add_iff_left]
  · simp only [h1, false_and, ↓reduceIte]
    obtain ⟨u, rfl⟩ : ∃ u, k = t + (u + 1) := ⟨k - t - 1, by omega⟩
    rw [Nat.mul_add, Nat.pow_add, Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _), Nat.mul_add,
      Nat.mul_one, Nat.pow_add, Nat.mul_comm (2 ^ (8 * u)), Nat.mul_assoc, Nat.mul_mod_right]

/-- The bytes `vpshufb` places: a lane's first `n` bytes from byte `o`. -/
theorem shufA11 (G : BitVec 128) : XBinOp.eval .pshufb G pmA11 = BitVec.ofNat 128 ((qword G 0).toNat % 2 ^ 48) := by
  have e : XBinOp.eval .pshufb G pmA11 = ofBytes fun i => if i < 6 then byte G i else 0 := by
    simp only [XBinOp.eval, ofBytes]; rfl
  rw [e]
  refine ext_byte fun t ht => ?_
  rw [byte_ofBytes _ ht, toNat_byte (BitVec.ofNat 128 _), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := (qword G 0).toNat % 2 ^ 48) (b := 2 ^ 128)
      (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos 48)) (Nat.pow_le_pow_right (by decide) (by decide))),
    show (2 : Nat) ^ 48 = 2 ^ (8 * 6) from rfl, byte_mod]
  by_cases h : t < 6 <;> simp only [h, ↓reduceIte]
  · exact toNat_byte_lo _ (by omega)
  · rfl

theorem shufB11 (G : BitVec 128) :
    XBinOp.eval .pshufb G pmB11 = BitVec.ofNat 128 (2 ^ 40 * ((qword G 0).toNat % 2 ^ 48)) := by
  have e : XBinOp.eval .pshufb G pmB11 = ofBytes fun i => if 5 ≤ i ∧ i < 11 then byte G (i - 5) else 0 := by
    simp only [XBinOp.eval, ofBytes]; rfl
  rw [e]
  refine ext_byte fun t ht => ?_
  rw [byte_ofBytes _ ht, toNat_byte (BitVec.ofNat 128 _), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := 2 ^ 40 * ((qword G 0).toNat % 2 ^ 48)) (b := 2 ^ 128) (by omega),
    show (2 : Nat) ^ 40 = 2 ^ (8 * 5) from rfl, show (2 : Nat) ^ 48 = 2 ^ (8 * 6) from rfl, byte_shl_mod]
  by_cases h : 5 ≤ t ∧ t < 11 <;> simp only [Nat.reduceAdd, h, ↓reduceIte]
  · exact toNat_byte_lo _ (by omega)
  · rfl

theorem shufA5 (G : BitVec 128) : XBinOp.eval .pshufb G pmA5 = BitVec.ofNat 128 ((qword G 0).toNat % 2 ^ 24) := by
  have e : XBinOp.eval .pshufb G pmA5 = ofBytes fun i => if i < 3 then byte G i else 0 := by
    simp only [XBinOp.eval, ofBytes]; rfl
  rw [e]
  refine ext_byte fun t ht => ?_
  rw [byte_ofBytes _ ht, toNat_byte (BitVec.ofNat 128 _), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := (qword G 0).toNat % 2 ^ 24) (b := 2 ^ 128)
      (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos 24)) (Nat.pow_le_pow_right (by decide) (by decide))),
    show (2 : Nat) ^ 24 = 2 ^ (8 * 3) from rfl, byte_mod]
  by_cases h : t < 3 <;> simp only [h, ↓reduceIte]
  · exact toNat_byte_lo _ (by omega)
  · rfl

theorem shufB5 (G : BitVec 128) :
    XBinOp.eval .pshufb G pmB5 = BitVec.ofNat 128 (2 ^ 16 * ((qword G 0).toNat % 2 ^ 24)) := by
  have e : XBinOp.eval .pshufb G pmB5 = ofBytes fun i => if 2 ≤ i ∧ i < 5 then byte G (i - 2) else 0 := by
    simp only [XBinOp.eval, ofBytes]; rfl
  rw [e]
  refine ext_byte fun t ht => ?_
  rw [byte_ofBytes _ ht, toNat_byte (BitVec.ofNat 128 _), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := 2 ^ 16 * ((qword G 0).toNat % 2 ^ 24)) (b := 2 ^ 128) (by omega),
    show (2 : Nat) ^ 16 = 2 ^ (8 * 2) from rfl, show (2 : Nat) ^ 24 = 2 ^ (8 * 3) from rfl, byte_shl_mod]
  by_cases h : 2 ≤ t ∧ t < 5 <;> simp only [Nat.reduceAdd, h, ↓reduceIte]
  · exact toNat_byte_lo _ (by omega)
  · rfl

/-- Two numbers whose bits do not overlap, merged by `vpor`. -/
theorem por_ofNat {A B : Nat} (k : Nat) (hA : A < 2 ^ k) (h : A + 2 ^ k * B < 2 ^ 128) :
    XBinOp.eval .por (BitVec.ofNat 128 A) (BitVec.ofNat 128 (2 ^ k * B)) = BitVec.ofNat 128 (A + 2 ^ k * B) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XBinOp.eval, BitVec.toNat_or, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h), Nat.mod_eq_of_lt h, Nat.or_comm,
    ← Nat.two_pow_add_eq_or_of_lt hA, Nat.add_comm]

theorem W_lt {d : Nat} {a : Nat → Nat} (hd : d = 5 ∨ d = 11) (ha : ∀ j < 4, a j < 2 ^ d) : W d a < 2 ^ (4 * d) := by
  have a0 := ha 0 (by decide); have a1 := ha 1 (by decide); have a2 := ha 2 (by decide)
  have a3 := ha 3 (by decide)
  rcases hd with rfl | rfl <;> simp only [W, Nat.reduceMul, Nat.reducePow] at a0 a1 a2 a3 ⊢ <;> omega_arith

/-- The two lanes of `d = 11` packed and combined (`vextracti128`, `vpor`): the eight values packed. -/
theorem pack11 {R₀ R₁ : BitVec 128} {a b : Nat → Nat} (ha : ∀ j < 4, (dword R₀ j).toNat = a j)
    (hb : ∀ j < 4, (dword R₁ j).toNat = b j) (ha' : ∀ j < 4, a j < 2 ^ 11) (hb' : ∀ j < 4, b j < 2 ^ 11) :
    XBinOp.eval .por (pk R₀ sv11 qm22 qsA11 pmA11) (pk R₁ sv11 qm22 qsB11 pmB11) =
      BitVec.ofNat 128 (W 11 a + 2 ^ 44 * W 11 b) := by
  obtain ⟨G₀, e₀, h₀⟩ := pk_q0 (d := 11) (s := 0) (S := sv11) (Q := qm22) (QS := qsA11) ⟨.inr rfl, .inl rfl⟩ ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl⟩ pmA11 ha ha'
  obtain ⟨G₁, e₁, h₁⟩ := pk_q0 (d := 11) (s := 4) (S := sv11) (Q := qm22) (QS := qsB11) ⟨.inr rfl, .inr rfl⟩ ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl⟩ pmB11 hb hb'
  have hA := W_lt (.inr rfl) ha'
  have hB := W_lt (.inr rfl) hb'
  rw [e₀, e₁, shufA11, shufB11, h₀, h₁]
  generalize W 11 a = A at hA ⊢
  generalize W 11 b = B at hB ⊢
  rw [show 2 ^ 0 * A % 2 ^ 48 = A by omega_arith, show 2 ^ 40 * (2 ^ 4 * B % 2 ^ 48) = 2 ^ 44 * B by omega_arith]
  exact por_ofNat 44 hA (by omega_arith)

/-- The two lanes of `d = 5` packed and combined. -/
theorem pack5 {R₀ R₁ : BitVec 128} {a b : Nat → Nat} (ha : ∀ j < 4, (dword R₀ j).toNat = a j)
    (hb : ∀ j < 4, (dword R₁ j).toNat = b j) (ha' : ∀ j < 4, a j < 2 ^ 5) (hb' : ∀ j < 4, b j < 2 ^ 5) :
    XBinOp.eval .por (pk R₀ sv5 qm10 qsA5 pmA5) (pk R₁ sv5 qm10 qsB5 pmB5) =
      BitVec.ofNat 128 (W 5 a + 2 ^ 20 * W 5 b) := by
  obtain ⟨G₀, e₀, h₀⟩ := pk_q0 (d := 5) (s := 0) (S := sv5) (Q := qm10) (QS := qsA5) ⟨.inl rfl, .inl rfl⟩ ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl⟩ pmA5 ha ha'
  obtain ⟨G₁, e₁, h₁⟩ := pk_q0 (d := 5) (s := 4) (S := sv5) (Q := qm10) (QS := qsB5) ⟨.inl rfl, .inr rfl⟩ ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl⟩ pmB5 hb hb'
  have hA := W_lt (.inl rfl) ha'
  have hB := W_lt (.inl rfl) hb'
  rw [e₀, e₁, shufA5, shufB5, h₀, h₁]
  generalize W 5 a = A at hA ⊢
  generalize W 5 b = B at hB ⊢
  rw [show 2 ^ 0 * A % 2 ^ 24 = A by omega_arith, show 2 ^ 16 * (2 ^ 4 * B % 2 ^ 24) = 2 ^ 20 * B by omega_arith]
  exact por_ofNat 20 hA (by omega_arith)

/-! ## The code of a group -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `ceMul11` and `ceRound`: the doublewords of `ymm0` compressed to `ymm1`. -/
theorem mulRnd11_ok (hc12 : ∀ l < 2, s.lane .xmm12 l = rc 261888) (hc13 : ∀ l < 2, s.lane .xmm13 l = mk 11)
    (k : ∀ s', (∀ l < 2, s'.lane .xmm1 l = rnd (mul11 (s.lane .xmm0 l)) 11) →
      (∀ r, r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (ceMul11 ++ ceRound ++ is)) s Q := by
  simp only [ceMul11, ceRound, ysl, ysr, yb, List.cons_append, List.nil_append]
  refine wp_vsh fun s1 u1 => wp_vsh fun s2 u2 => wp_vbin fun s3 u3 => wp_vsh fun s4 u4 => wp_vsh fun s5 u5 =>
    wp_vbin fun s6 u6 => wp_vbin fun s7 u7 => wp_vsh fun s8 u8 => wp_vsh fun s9 u9 => wp_vbin fun s10 u10 =>
    wp_vbin fun s11 u11 => wp_vbin fun s12 u12 => wp_vsh fun s13 u13 => wp_vbin fun s14 u14 =>
      k s14 (fun l hl => ?_) (fun r a b c l hl => ?_) ?_ ?_ ?_ ?_
  · simp only [laneEq u14 hl, laneEq u13 hl, laneEq u12 hl, laneEq u11 hl, laneEq u10 hl, laneEq u9 hl,
      laneEq u8 hl, laneEq u7 hl, laneEq u6 hl, laneEq u5 hl, laneEq u4 hl, laneEq u3 hl, laneEq u2 hl,
      laneEq u1 hl, reduceCtorEq, ↓reduceIte, hc12 l hl, hc13 l hl]
    rfl
  · simp only [laneEq u14 hl, laneEq u13 hl, laneEq u12 hl, laneEq u11 hl, laneEq u10 hl, laneEq u9 hl,
      laneEq u8 hl, laneEq u7 hl, laneEq u6 hl, laneEq u5 hl, laneEq u4 hl, laneEq u3 hl, laneEq u2 hl,
      laneEq u1 hl, a, b, c, ↓reduceIte]
  · rw [u14.gpr, u13.gpr, u12.gpr, u11.gpr, u10.gpr, u9.gpr, u8.gpr, u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr,
      u2.gpr, u1.gpr]
  · rw [u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem,
      u2.mem, u1.mem]
  · rw [u14.rd, u13.rd, u12.rd, u11.rd, u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u14.wr, u13.wr, u12.wr, u11.wr, u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]

/-- `ceMul5` and `ceRound`. -/
theorem mulRnd5_ok (hc12 : ∀ l < 2, s.lane .xmm12 l = rc 261888) (hc13 : ∀ l < 2, s.lane .xmm13 l = mk 5)
    (k : ∀ s', (∀ l < 2, s'.lane .xmm1 l = rnd (mul5 (s.lane .xmm0 l)) 5) →
      (∀ r, r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (ceMul5 ++ ceRound ++ is)) s Q := by
  simp only [ceMul5, ceRound, ysl, ysr, yb, List.cons_append, List.nil_append]
  refine wp_vsh fun s1 u1 => wp_vsh fun s2 u2 => wp_vbin fun s3 u3 => wp_vsh fun s4 u4 => wp_vsh fun s5 u5 =>
    wp_vbin fun s6 u6 => wp_vbin fun s7 u7 => wp_vbin fun s8 u8 => wp_vsh fun s9 u9 => wp_vbin fun s10 u10 =>
      k s10 (fun l hl => ?_) (fun r a b c l hl => ?_) ?_ ?_ ?_ ?_
  · simp only [laneEq u10 hl, laneEq u9 hl, laneEq u8 hl, laneEq u7 hl, laneEq u6 hl, laneEq u5 hl,
      laneEq u4 hl, laneEq u3 hl, laneEq u2 hl, laneEq u1 hl, reduceCtorEq, ↓reduceIte, hc12 l hl, hc13 l hl]
    rfl
  · simp only [laneEq u10 hl, laneEq u9 hl, laneEq u8 hl, laneEq u7 hl, laneEq u6 hl, laneEq u5 hl,
      laneEq u4 hl, laneEq u3 hl, laneEq u2 hl, laneEq u1 hl, a, b, c, ↓reduceIte]
  · rw [u10.gpr, u9.gpr, u8.gpr, u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  · rw [u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]

/-- `cePack true`, with the constants `S`, `Q` (both lanes), `QS₀`, `QS₁`, `M₀` and `M₁` (one lane each):
the lanes of `ymm1` packed into `xmm1`. -/
theorem pack_ok {Sv Qm QS₀ QS₁ M₀ M₁ : BitVec 128} (h8 : ∀ l < 2, s.lane .xmm8 l = Sv)
    (h9 : ∀ l < 2, s.lane .xmm9 l = Qm) (h10 : ∀ l < 2, s.lane .xmm10 l = if l = 0 then QS₀ else QS₁)
    (h11 : ∀ l < 2, s.lane .xmm11 l = if l = 0 then M₀ else M₁)
    (k : ∀ s', s'.lane .xmm1 0 = XBinOp.eval .por (pk (s.lane .xmm1 0) Sv Qm QS₀ M₀) (pk (s.lane .xmm1 1) Sv Qm QS₁ M₁) →
      (∀ r, r ≠ .xmm1 → r ≠ .xmm2 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (cePack true ++ is)) s Q := by
  simp only [cePack, ↓reduceIte, yb, List.cons_append, List.nil_append]
  refine wp_vvar fun s1 u1 => wp_vsh fun s2 u2 => wp_vbin fun s3 u3 => wp_vbin fun s4 u4 => wp_vvar fun s5 u5 =>
    wp_vsh fun s6 u6 => wp_vbin fun s7 u7 => wp_vbin fun s8 u8 => wp_vext1 fun s9 u9 => wp_vbin128 fun s10 u10 =>
      k s10 ?_ (fun r a b l hl => ?_) ?_ ?_ ?_ ?_
  · have e8 : ∀ l < 2, s8.lane .xmm1 l =
        pk (s.lane .xmm1 l) Sv Qm (if l = 0 then QS₀ else QS₁) (if l = 0 then M₀ else M₁) := fun l hl => by
      simp only [laneEq u8 hl, laneEq u7 hl, laneEq u6 hl, laneEq u5 hl, laneEq u4 hl, laneEq u3 hl,
        laneEq u2 hl, laneEq u1 hl, reduceCtorEq, ↓reduceIte, h8 l hl, h9 l hl, h10 l hl, h11 l hl]
      rfl
    rw [u10.val 0 (by decide), itT rfl, u9.other .xmm1 (by decide) 0 (by decide), u9.val 0 (by decide), itT rfl,
      e8 0 (by decide), e8 1 (by decide)]
    rfl
  · simp only [laneEq u10 hl, laneEq u9 hl, laneEq u8 hl, laneEq u7 hl, laneEq u6 hl, laneEq u5 hl,
      laneEq u4 hl, laneEq u3 hl, laneEq u2 hl, laneEq u1 hl, a, b, ↓reduceIte]
  · rw [u10.gpr, u9.gpr, u8.gpr, u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  · rw [u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]

end

/-! ## The constants -/

/-- The constants of `d = 11`. -/
structure C11 (s : State) : Prop where
  c8 : ∀ l < 2, s.lane .xmm8 l = sv11
  c9 : ∀ l < 2, s.lane .xmm9 l = qm22
  c10 : ∀ l < 2, s.lane .xmm10 l = if l = 0 then qsA11 else qsB11
  c11 : ∀ l < 2, s.lane .xmm11 l = if l = 0 then pmA11 else pmB11
  c12 : ∀ l < 2, s.lane .xmm12 l = rc 261888
  c13 : ∀ l < 2, s.lane .xmm13 l = mk 11

/-- The constants of `d = 5`. -/
structure C5 (s : State) : Prop where
  c8 : ∀ l < 2, s.lane .xmm8 l = sv5
  c9 : ∀ l < 2, s.lane .xmm9 l = qm10
  c10 : ∀ l < 2, s.lane .xmm10 l = if l = 0 then qsA5 else qsB5
  c11 : ∀ l < 2, s.lane .xmm11 l = if l = 0 then pmA5 else pmB5
  c12 : ∀ l < 2, s.lane .xmm12 l = rc 261888
  c13 : ∀ l < 2, s.lane .xmm13 l = mk 5

theorem C11.pres {s s' : State} (h : C11 s) (hk : Hi7 s s') : C11 s' :=
  ⟨fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c8 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c9 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c10 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c11 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c12 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c13 l hl]⟩

theorem C5.pres {s s' : State} (h : C5 s) (hk : Hi7 s s') : C5 s' :=
  ⟨fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c8 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c9 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c10 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c11 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c12 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl,
      h.c13 l hl]⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem consts11_ok
    (k : ∀ s', C11 s' → (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (ce11Consts ++ is)) s Q := by
  simp only [ce11Consts, List.append_assoc]
  refine yconst4_ok (by decide) (by decide) _ _ _ _ fun s1 a1 b1 o1 g1 m1 r1 w1 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s2 a2 b2 o2 g2 m2 r2 w2 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s3 a3 b3 o3 g3 m3 r3 w3 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s4 a4 b4 o4 g4 m4 r4 w4 =>
    yconst_ok' _ _ fun s5 a5 o5 g5 m5 r5 w5 => yconst_ok' _ _ fun s6 a6 o6 g6 m6 r6 w6 =>
    k s6 ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩
      (fun g hg => ?_) ?_ ?_ ?_
  · rw [o6 _ (by decide) l hl, o5 _ (by decide) l hl, o4 _ (by decide) (by decide) (by decide) l hl,
      o3 _ (by decide) (by decide) (by decide) l hl, o2 _ (by decide) (by decide) (by decide) l hl]
    exact (lane4 a1 b1 rfl rfl l hl).trans (by split <;> rfl)
  · rw [o6 _ (by decide) l hl, o5 _ (by decide) l hl, o4 _ (by decide) (by decide) (by decide) l hl,
      o3 _ (by decide) (by decide) (by decide) l hl]
    exact (lane4 a2 b2 rfl rfl l hl).trans (by split <;> rfl)
  · rw [o6 _ (by decide) l hl, o5 _ (by decide) l hl, o4 _ (by decide) (by decide) (by decide) l hl]
    exact lane4 a3 b3 rfl rfl l hl
  · rw [o6 _ (by decide) l hl, o5 _ (by decide) l hl]
    exact lane4 a4 b4 rfl rfl l hl
  · rw [o6 _ (by decide) l hl, a5 l hl]; rfl
  · rw [a6 l hl]; rfl
  · rw [g6 g hg, g5 g hg, g4 g hg, g3 g hg, g2 g hg, g1 g hg]
  · rw [m6, m5, m4, m3, m2, m1]
  · rw [r6, r5, r4, r3, r2, r1]
  · rw [w6, w5, w4, w3, w2, w1]

theorem consts5_ok
    (k : ∀ s', C5 s' → (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (ce5Consts ++ is)) s Q := by
  simp only [ce5Consts, List.append_assoc]
  refine yconst4_ok (by decide) (by decide) _ _ _ _ fun s1 a1 b1 o1 g1 m1 r1 w1 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s2 a2 b2 o2 g2 m2 r2 w2 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s3 a3 b3 o3 g3 m3 r3 w3 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s4 a4 b4 o4 g4 m4 r4 w4 =>
    yconst_ok' _ _ fun s5 a5 o5 g5 m5 r5 w5 => yconst_ok' _ _ fun s6 a6 o6 g6 m6 r6 w6 =>
    k s6 ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩
      (fun g hg => ?_) ?_ ?_ ?_
  · rw [o6 _ (by decide) l hl, o5 _ (by decide) l hl, o4 _ (by decide) (by decide) (by decide) l hl,
      o3 _ (by decide) (by decide) (by decide) l hl, o2 _ (by decide) (by decide) (by decide) l hl]
    exact (lane4 a1 b1 rfl rfl l hl).trans (by split <;> rfl)
  · rw [o6 _ (by decide) l hl, o5 _ (by decide) l hl, o4 _ (by decide) (by decide) (by decide) l hl,
      o3 _ (by decide) (by decide) (by decide) l hl]
    exact (lane4 a2 b2 rfl rfl l hl).trans (by split <;> rfl)
  · rw [o6 _ (by decide) l hl, o5 _ (by decide) l hl, o4 _ (by decide) (by decide) (by decide) l hl]
    exact lane4 a3 b3 rfl rfl l hl
  · rw [o6 _ (by decide) l hl, o5 _ (by decide) l hl]
    exact lane4 a4 b4 rfl rfl l hl
  · rw [o6 _ (by decide) l hl, a5 l hl]; rfl
  · rw [a6 l hl]; rfl
  · rw [g6 g hg, g5 g hg, g4 g hg, g3 g hg, g2 g hg, g1 g hg]
  · rw [m6, m5, m4, m3, m2, m1]
  · rw [r6, r5, r4, r3, r2, r1]
  · rw [w6, w5, w4, w3, w2, w1]

/-! ## A group -/

/-- A value compressed with the multiplier `M` to `d` bits, with ML-KEM-1024's rounding constant. -/
abbrev cw (M d y : Nat) : Nat := (y * M + 261888) / 2 ^ 19 % 2 ^ d

theorem dv11 {X : BitVec 128} {j : Nat} (hj : j < 4) {y : Nat} (hy : (dword X j).toNat = y) (hq : y < 3329) :
    (dword (rnd (mul11 X) 11) j).toNat = cw 322542 11 y := by
  have hm := dword_mul11 X hj (by omega_arith); rw [hy] at hm
  rw [dword_rnd _ (by decide) hj (by rw [hm]; omega_arith), hm]

theorem dv5 {X : BitVec 128} {j : Nat} (hj : j < 4) {y : Nat} (hy : (dword X j).toNat = y) (hq : y < 3329) :
    (dword (rnd (mul5 X) 5) j).toNat = cw 5040 5 y := by
  have hm := dword_mul5 X hj (by omega_arith); rw [hy] at hm
  rw [dword_rnd _ (by decide) hj (by rw [hm]; omega_arith), hm]

/-- A group of `d = 11`: the eight coefficients `x` at `rdi + o`, compressed and packed into `xmm1`. -/
theorem grp11_ok {o : Nat} (hc : C11 s) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 o) 32)
    {x : Nat → Nat} (hx : ∀ j < 8, (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (o + 4 * j)) 32).toNat = x j)
    (hq : ∀ j < 8, x j < 3329)
    (k : ∀ s', s'.lane .xmm1 0 = BitVec.ofNat 128 (W 11 (fun j => cw 322542 11 (x j)) +
        2 ^ 44 * W 11 (fun j => cw 322542 11 (x (4 + j)))) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (ce11Grp o ++ is)) s Q := by
  rw [show ce11Grp o ++ is = .vmovdquLoad .l256 .xmm0 (at_ .rdi o) :: (ceMul11 ++ ceRound ++ (cePack true ++ is))
    by simp [ce11Grp]]
  refine wp_vld256 (a := s.gpr .rdi + BitVec.ofNat 64 o) (by rw [ea_at]) hin fun s1 u1 => ?_
  refine mulRnd11_ok (fun l hl => by rw [u1.other _ (by decide) l hl, hc.c12 l hl])
    (fun l hl => by rw [u1.other _ (by decide) l hl, hc.c13 l hl]) fun s2 h2 o2 g2 m2 r2 w2 => ?_
  refine pack_ok (fun l hl => by rw [o2 _ (by decide) (by decide) (by decide) l hl, u1.other _ (by decide) l hl,
      hc.c8 l hl])
    (fun l hl => by rw [o2 _ (by decide) (by decide) (by decide) l hl, u1.other _ (by decide) l hl, hc.c9 l hl])
    (fun l hl => by rw [o2 _ (by decide) (by decide) (by decide) l hl, u1.other _ (by decide) l hl, hc.c10 l hl])
    (fun l hl => by rw [o2 _ (by decide) (by decide) (by decide) l hl, u1.other _ (by decide) l hl, hc.c11 l hl])
    fun s3 h3 o3 g3 m3 r3 w3 => k s3 ?_ (fun r a b c d l hl => by rw [o3 r b c l hl, o2 r b c d l hl,
      u1.other r a l hl]) (by rw [g3, g2, u1.gpr]) (by rw [m3, m2, u1.mem]) (by rw [r3, r2, u1.rd])
      (by rw [w3, w2, u1.wr])
  rw [h3, h2 0 (by decide), h2 1 (by decide), u1.val 0 (by decide), u1.val 1 (by decide)]
  refine pack11 (fun j hj => dv11 hj ?_ (hq j (by omega_arith))) (fun j hj => dv11 hj ?_ (hq (4 + j) (by omega_arith)))
    (fun _ _ => Nat.mod_lt _ (by decide)) (fun _ _ => Nat.mod_lt _ (by decide))
  · rw [dword_ld _ _ (by decide) hj, Offset.add_add, show o + (16 * 0 + 4 * j) = o + 4 * j by omega_arith,
      hx j (by omega_arith)]
  · rw [dword_ld _ _ (by decide) hj, Offset.add_add, show o + (16 * 1 + 4 * j) = o + 4 * (4 + j) by omega_arith,
      hx (4 + j) (by omega_arith)]

/-- A group of `d = 5`. -/
theorem grp5_ok {o : Nat} (hc : C5 s) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 o) 32)
    {x : Nat → Nat} (hx : ∀ j < 8, (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (o + 4 * j)) 32).toNat = x j)
    (hq : ∀ j < 8, x j < 3329)
    (k : ∀ s', s'.lane .xmm1 0 = BitVec.ofNat 128 (W 5 (fun j => cw 5040 5 (x j)) +
        2 ^ 20 * W 5 (fun j => cw 5040 5 (x (4 + j)))) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (ce5Grp o ++ is)) s Q := by
  rw [show ce5Grp o ++ is = .vmovdquLoad .l256 .xmm0 (at_ .rdi o) :: (ceMul5 ++ ceRound ++ (cePack true ++ is))
    by simp [ce5Grp]]
  refine wp_vld256 (a := s.gpr .rdi + BitVec.ofNat 64 o) (by rw [ea_at]) hin fun s1 u1 => ?_
  refine mulRnd5_ok (fun l hl => by rw [u1.other _ (by decide) l hl, hc.c12 l hl])
    (fun l hl => by rw [u1.other _ (by decide) l hl, hc.c13 l hl]) fun s2 h2 o2 g2 m2 r2 w2 => ?_
  refine pack_ok (fun l hl => by rw [o2 _ (by decide) (by decide) (by decide) l hl, u1.other _ (by decide) l hl,
      hc.c8 l hl])
    (fun l hl => by rw [o2 _ (by decide) (by decide) (by decide) l hl, u1.other _ (by decide) l hl, hc.c9 l hl])
    (fun l hl => by rw [o2 _ (by decide) (by decide) (by decide) l hl, u1.other _ (by decide) l hl, hc.c10 l hl])
    (fun l hl => by rw [o2 _ (by decide) (by decide) (by decide) l hl, u1.other _ (by decide) l hl, hc.c11 l hl])
    fun s3 h3 o3 g3 m3 r3 w3 => k s3 ?_ (fun r a b c d l hl => by rw [o3 r b c l hl, o2 r b c d l hl,
      u1.other r a l hl]) (by rw [g3, g2, u1.gpr]) (by rw [m3, m2, u1.mem]) (by rw [r3, r2, u1.rd])
      (by rw [w3, w2, u1.wr])
  rw [h3, h2 0 (by decide), h2 1 (by decide), u1.val 0 (by decide), u1.val 1 (by decide)]
  refine pack5 (fun j hj => dv5 hj ?_ (hq j (by omega_arith))) (fun j hj => dv5 hj ?_ (hq (4 + j) (by omega_arith)))
    (fun _ _ => Nat.mod_lt _ (by decide)) (fun _ _ => Nat.mod_lt _ (by decide))
  · rw [dword_ld _ _ (by decide) hj, Offset.add_add, show o + (16 * 0 + 4 * j) = o + 4 * j by omega_arith,
      hx j (by omega_arith)]
  · rw [dword_ld _ _ (by decide) hj, Offset.add_add, show o + (16 * 1 + 4 * j) = o + 4 * (4 + j) by omega_arith,
      hx (4 + j) (by omega_arith)]

end

/-! ## The bytes of the encoding -/

theorem dig8_11 (f : Nat → Nat) : digits 11 ((List.range 8).map f) = W 11 f + 2 ^ 44 * W 11 (fun j => f (4 + j)) := by
  show digits 11 [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7] = _
  simp only [digits_cons, digits_nil, W, Nat.reduceMul, Nat.reducePow, Nat.reduceAdd]
  omega_arith

theorem dig16_5 (f : Nat → Nat) : digits 5 ((List.range 16).map f) =
    (W 5 (fun j => f (8 * 0 + j)) + 2 ^ 20 * W 5 (fun j => f (8 * 0 + (4 + j)))) +
    2 ^ 40 * (W 5 (fun j => f (8 * 1 + j)) + 2 ^ 20 * W 5 (fun j => f (8 * 1 + (4 + j)))) := by
  show digits 5 [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15] = _
  simp only [digits_cons, digits_nil, W, Nat.reduceMul, Nat.reducePow, Nat.reduceAdd]
  omega_arith

theorem cw11_eq (x : Zq) : cw 322542 11 x.val = compress 11 x := (compress1024_eq (d := 11) (by decide) x).symm

theorem cw5_eq (x : Zq) : cw 5040 5 x.val = compress 5 x := (compress1024_eq (d := 5) (by decide) x).symm

section
variable (s₀ : State)
/-- The eight values of group `g` of `d = 11`, packed. -/
abbrev Vg (g : Nat) : Nat := digits 11 ((List.range 8).map fun t => compress 11 (CE.F s₀)[8 * g + t]!)
/-- The sixteen values of pair `p` of groups of `d = 5`, packed. -/
abbrev Pg (p : Nat) : Nat := digits 5 ((List.range 16).map fun t => compress 5 (CE.F s₀)[16 * p + t]!)
/-- The eight values from `16 p + 8 k` of `d = 5`, packed. -/
abbrev Ug (p k : Nat) : Nat := W 5 (fun j => compress 5 (CE.F s₀)[16 * p + (8 * k + j)]!) +
  2 ^ 20 * W 5 (fun j => compress 5 (CE.F s₀)[16 * p + (8 * k + (4 + j))]!)
end

theorem Vg_lt (s₀ : State) (g : Nat) : Vg s₀ g < 2 ^ 88 := by
  have := digits_lt (w := 11) (L := (List.range 8).map fun (t : Nat) => compress 11 (CE.F s₀)[8 * g + t]!)
    (fun a ha => by
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha
      exact compress_lt _ _)
  simpa using this

theorem Pg_lt (s₀ : State) (p : Nat) : Pg s₀ p < 2 ^ 80 := by
  have := digits_lt (w := 5) (L := (List.range 16).map fun (t : Nat) => compress 5 (CE.F s₀)[16 * p + t]!)
    (fun a ha => by
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha
      exact compress_lt _ _)
  simpa using this

theorem Ug_lt (s₀ : State) (p k : Nat) : Ug s₀ p k < 2 ^ 40 := by
  have h := fun (t : Nat) => compress_lt 5 (CE.F s₀)[t]!
  simp only [Ug, W, Nat.reducePow] at h ⊢
  have := h (16 * p + (8 * k + 0)); have := h (16 * p + (8 * k + 1)); have := h (16 * p + (8 * k + 2))
  have := h (16 * p + (8 * k + 3)); have := h (16 * p + (8 * k + (4 + 0))); have := h (16 * p + (8 * k + (4 + 1)))
  have := h (16 * p + (8 * k + (4 + 2))); have := h (16 * p + (8 * k + (4 + 3)))
  omega_arith

/-- Two groups of `d = 5` merged: the second shifted up by five bytes over the first. -/
theorem comb5 {U₀ U₁ : Nat} (h₀ : U₀ < 2 ^ 40) (h₁ : U₁ < 2 ^ 40) :
    XBinOp.eval .por (XShiftOp.eval .pslldq (BitVec.ofNat 128 U₁) 5) (BitVec.ofNat 128 U₀) =
      BitVec.ofNat 128 (U₀ + 2 ^ 40 * U₁) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XBinOp.eval, XShiftOp.eval, show (5 : BitVec 8).toNat = 5 from rfl, show min 5 16 * 8 = 40 from rfl,
    BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [show U₁ % 2 ^ 128 * 2 ^ 40 % 2 ^ 128 = 2 ^ 40 * U₁ by omega_arith, Nat.mod_eq_of_lt (show U₀ < 2 ^ 128 by omega_arith),
    show (U₀ + 2 ^ 40 * U₁) % 2 ^ 128 = 2 ^ 40 * U₁ + U₀ by omega_arith, ← Nat.two_pow_add_eq_or_of_lt h₀]

/-- The 16 bytes of the last group of `d = 11`: the last five of the group before, then its eleven. -/
theorem lastY11 {V₀ V₁ : Nat} (h₀ : V₀ < 2 ^ 88) (h₁ : V₁ < 2 ^ 88) {j : Nat} (hj : j < 16) :
    byte (XBinOp.eval .por (XShiftOp.eval .pslldq (BitVec.ofNat 128 V₁) 5)
      (XShiftOp.eval .psrldq (BitVec.ofNat 128 V₀) 6)) j =
      BitVec.ofNat 8 (if j < 5 then V₀ / 2 ^ (8 * (6 + j)) else V₁ / 2 ^ (8 * (j - 5))) := by
  have hY : (XBinOp.eval .por (XShiftOp.eval .pslldq (BitVec.ofNat 128 V₁) 5)
      (XShiftOp.eval .psrldq (BitVec.ofNat 128 V₀) 6)).toNat = 2 ^ 40 * V₁ + V₀ / 2 ^ 48 := by
    simp only [XBinOp.eval, XShiftOp.eval, show (5 : BitVec 8).toNat = 5 from rfl,
      show (6 : BitVec 8).toNat = 6 from rfl, show min 5 16 * 8 = 40 from rfl, show min 6 16 * 8 = 48 from rfl,
      BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
    rw [show V₁ % 2 ^ 128 * 2 ^ 40 % 2 ^ 128 = 2 ^ 40 * V₁ by omega_arith, show V₀ % 2 ^ 128 / 2 ^ 48 = V₀ / 2 ^ 48 by omega_arith,
      ← Nat.two_pow_add_eq_or_of_lt (by omega_arith)]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_byte, hY, BitVec.toNat_ofNat]
  by_cases h : j < 5
  · simp only [h, ↓reduceIte]
    have e : (2 : Nat) ^ 40 = 2 ^ (8 * j) * (2 ^ 8 * 2 ^ (8 * (4 - j))) := by
      rw [← Nat.pow_add, ← Nat.pow_add, show 8 * j + (8 + 8 * (4 - j)) = 40 by omega]
    rw [e, Nat.mul_assoc, Nat.mul_add_div (Nat.two_pow_pos _), Nat.mul_assoc, Nat.mul_add_mod,
      Nat.div_div_eq_div_mul, ← Nat.pow_add, show 48 + 8 * j = 8 * (6 + j) by omega]
  · simp only [h, ↓reduceIte]
    obtain ⟨u, rfl⟩ : ∃ u, j = 5 + u := ⟨j - 5, by omega⟩
    rw [Nat.add_sub_cancel_left, Nat.mul_add, Nat.pow_add, ← Nat.div_div_eq_div_mul, show 8 * 5 = 40 from rfl,
      Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (a := V₀ / 2 ^ 48) (b := 2 ^ 40) (by omega),
      Nat.add_zero]

/-! ## The loops -/

/-- After `i` groups of `d = 11`. -/
structure Inv11 (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = CE.fP s₀ + BitVec.ofNat 64 (32 * i)
  r8 : s.gpr .r8 = CE.oP s₀ + BitVec.ofNat 64 (11 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : C11 s
  frame : Frame [⟨CE.oP s₀, 32 * 11⟩] s₀.mem s.mem
  done : ∀ k < 11 * i, s.mem (CE.oP s₀ + BitVec.ofNat 64 k) = (compressEncode 11 (CE.F s₀))[k]!
  last : 0 < i → s.lane .xmm1 0 = BitVec.ofNat 128 (Vg s₀ (i - 1))

/-- After `i` pairs of groups of `d = 5`. -/
structure Inv5 (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = CE.fP s₀ + BitVec.ofNat 64 (64 * i)
  r8 : s.gpr .r8 = CE.oP s₀ + BitVec.ofNat 64 (10 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : C5 s
  frame : Frame [⟨CE.oP s₀, 32 * 5⟩] s₀.mem s.mem
  done : ∀ k < 10 * i, s.mem (CE.oP s₀ + BitVec.ofNat 64 k) = (compressEncode 5 (CE.F s₀))[k]!
  last : 0 < i → s.lane .xmm1 0 = BitVec.ofNat 128 (Pg s₀ (i - 1))

section
variable {s₀ : State} (hp : compressEncode1024K.pre s₀)
include hp

/-- The coefficient `c` of `f` in memory `m`, the output aside. -/
theorem coeffV {d : Nat} (hdd : dArg s₀ .rsi = d) {m : Mem} (hf : Frame [⟨CE.oP s₀, 32 * d⟩] s₀.mem m) {c : Nat}
    (hc : c < 256) : (m.readW (CE.fP s₀ + BitVec.ofNat 64 (4 * c)) 32).toNat = ((CE.F s₀)[c]!).val := by
  rw [← coeffAt_eq m (CE.fP s₀) c, CE.coeff hp hdd hf hc]
  exact (polyAt_val hp.2.2.2.2.2.2.2 (by rw [n_eq]; exact hc)).symm

theorem inR {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {o : Nat} (ho : o + 32 ≤ 1024) :
    InRegions (s.rd ++ s.wr) (CE.fP s₀ + BitVec.ofNat 64 o) 32 := by
  rw [hrd, hwr, hp.1]
  exact ⟨_, List.mem_cons_self .., Offset.contains_base _ ho (by omega_arith)⟩

theorem outR {d : Nat} (hdd : dArg s₀ .rsi = d) {s : State} (hwr : s.wr = s₀.wr) {o : Nat} (ho : o + 16 ≤ 32 * d) :
    InRegions s.wr (CE.oP s₀ + BitVec.ofNat 64 o) 16 := by
  have := (CE.lenEq hp hdd)
  rw [hwr, hp.2.1, this]
  exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ ho (by omega_arith)⟩

/-- Group `g` of `d = 11`, from `rdi = fP + 32 g`. -/
theorem group11 (hdd : dArg s₀ .rsi = 11) {g : Nat} (hg : g < 32) {is : List Instr} {s : State}
    {Q : State → Prop} (hdi : s.gpr .rdi = CE.fP s₀ + BitVec.ofNat 64 (32 * g)) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hc : C11 s) (hf : Frame [⟨CE.oP s₀, 32 * 11⟩] s₀.mem s.mem)
    (k : ∀ s', s'.lane .xmm1 0 = BitVec.ofNat 128 (Vg s₀ g) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (ce11Grp 0 ++ is)) s Q :=
  grp11_ok (o := 0) (x := fun j => ((CE.F s₀)[8 * g + j]!).val) hc
    (by rw [hdi, Offset.add_add]; exact inR hp hrd hwr (by omega_arith))
    (fun j hj => by rw [hdi, Offset.add_add, show 32 * g + (0 + 4 * j) = 4 * (8 * g + j) by omega_arith,
      coeffV hp hdd hf (by omega_arith)]) (fun j _ => val_lt _) fun s' h o gg m r w =>
    k s' (by rw [h, Vg, dig8_11]; simp only [W, cw11_eq]) o gg m r w

/-- Group `k` of pair `p` of `d = 5`, from `rdi = fP + 64 p`. -/
theorem group5 (hdd : dArg s₀ .rsi = 5) {p k : Nat} (hp16 : p < 16) (hk : k < 2) {is : List Instr} {s : State}
    {Q : State → Prop} (hdi : s.gpr .rdi = CE.fP s₀ + BitVec.ofNat 64 (64 * p)) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hc : C5 s) (hf : Frame [⟨CE.oP s₀, 32 * 5⟩] s₀.mem s.mem)
    (K : ∀ s', s'.lane .xmm1 0 = BitVec.ofNat 128 (Ug s₀ p k) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (ce5Grp (32 * k) ++ is)) s Q :=
  grp5_ok (o := 32 * k) (x := fun j => ((CE.F s₀)[16 * p + (8 * k + j)]!).val) hc
    (by rw [hdi, Offset.add_add]; exact inR hp hrd hwr (by omega_arith))
    (fun j hj => by rw [hdi, Offset.add_add, show 64 * p + (32 * k + 4 * j) = 4 * (16 * p + (8 * k + j)) by omega_arith,
      coeffV hp hdd hf (by omega_arith)]) (fun j _ => val_lt _) fun s' h o gg m r w =>
    K s' (by rw [h, Ug]; simp only [W, cw5_eq]) o gg m r w

/-- Pair `p` of `d = 5`, from `rdi = fP + 64 p`: its 10 bytes in `xmm1`. -/
theorem pair5 (hdd : dArg s₀ .rsi = 5) {p : Nat} (hp16 : p < 16) {is : List Instr} {s : State}
    {Q : State → Prop} (hdi : s.gpr .rdi = CE.fP s₀ + BitVec.ofNat 64 (64 * p)) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hc : C5 s) (hf : Frame [⟨CE.oP s₀, 32 * 5⟩] s₀.mem s.mem)
    (K : ∀ s', s'.lane .xmm1 0 = BitVec.ofNat 128 (Pg s₀ p) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → r ≠ .xmm4 → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (ce5Pair ++ is)) s Q := by
  simp only [ce5Pair, List.append_assoc, List.cons_append, List.nil_append]
  refine group5 hp hdd (k := 0) hp16 (by decide) hdi hrd hwr hc hf fun s1 h1 o1 g1 m1 r1 w1 => ?_
  refine wp_vmovdqa128 fun s2 u2 => ?_
  have c2 := (hc.pres fun r a b c d _ _ _ l hl => o1 r a b c d l hl).pres fun r _ _ _ _ a _ _ l hl => u2.other r a l hl
  refine group5 hp hdd (k := 1) hp16 (by decide) (by rw [u2.gpr, g1, hdi]) (by rw [u2.rd, r1, hrd])
    (by rw [u2.wr, w1, hwr]) c2 (by rw [u2.mem, m1]; exact hf) fun s3 h3 o3 g3 m3 r3 w3 => ?_
  refine wp_vsh128 fun s4 u4 => wp_vbin128 fun s5 u5 => K s5 ?_ (fun r a b c d e l hl => ?_) ?_ ?_ ?_ ?_
  · rw [u5.val 0 (by decide), itT rfl, u4.val 0 (by decide), itT rfl, u4.other .xmm4 (by decide) 0 (by decide),
      o3 .xmm4 (by decide) (by decide) (by decide) (by decide) 0 (by decide), u2.val 0 (by decide), itT rfl, h1, h3]
    exact (comb5 (Ug_lt s₀ p 0) (Ug_lt s₀ p 1)).trans (by rw [Pg, dig16_5])
  · rw [u5.other r b l hl, u4.other r b l hl, o3 r a b c d l hl, u2.other r e l hl, o1 r a b c d l hl]
  · rw [u5.gpr, u4.gpr, g3, u2.gpr, g1]
  · rw [u5.mem, u4.mem, m3, u2.mem, m1]
  · rw [u5.rd, u4.rd, r3, u2.rd, r1]
  · rw [u5.wr, u4.wr, w3, u2.wr, w1]

theorem step11 (hdd : dArg s₀ .rsi = 11) {i : Nat} (hi : i < 31) {s : State} (hI : Inv11 s₀ i s) :
    WP isa (.block (ce11Grp 0 ++ ([.vmovdquStore .l128 (at_ .r8 0) .xmm1, .alu .add .rdi (.imm 32),
        .alu .add .r8 (.imm 11), .alu .sub .rcx (.imm 1)] : List Instr))) s
      fun s' => Inv11 s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  refine group11 hp hdd (g := i) (by omega_arith) hI.rdi hI.rd hI.wr hI.c hI.frame fun s1 hX o1 g1 m1 r1 w1 => ?_
  refine wp_vst128 (a := CE.oP s₀ + BitVec.ofNat 64 (11 * i)) (by rw [ea_at, add_ofNat_zero, g1, hI.r8])
    (by rw [w1]; exact outR hp hdd hI.wr (by omega_arith)) fun s2 g2 l2 m2 r2 w2 => ?_
  refine wp_addi' fun s3 u3 => wp_addi' fun s4 u4 => wp_subi' fun s5 u5 hz => WP.block_nil ?_
  have hw : Written s.mem s2.mem (CE.oP s₀ + BitVec.ofNat 64 (11 * i)) 16 fun j =>
      CEY.mix (compressEncode 11 (CE.F s₀)) (11 * (i + 1)) (BitVec.ofNat 128 (Vg s₀ i)) (11 * i) (11 * i + j) := by
    rw [m2, m1, hX]
    refine (written16 _ _ _).congr fun j hj => ?_
    rw [CEY.mix]
    by_cases h : j < 11
    · rw [itT (show 11 * i + j < 11 * (i + 1) by omega_arith), compressEncode_group (c := 8) (b := 11) (by decide)
        (by decide) _ (by omega_arith) h, byte_ofNat128 (Nat.lt_trans (Vg_lt s₀ i) (by decide))]
    · rw [itF (show ¬ 11 * i + j < 11 * (i + 1) by omega_arith), show 11 * i + j - 11 * i = j by omega_arith]
  obtain ⟨hf', hd'⟩ := Written.step (val := CEY.mix (compressEncode 11 (CE.F s₀)) (11 * (i + 1))
    (BitVec.ofNat 128 (Vg s₀ i)) (11 * i)) hI.frame (fun k hk => by
      rw [CEY.mix, itT (show k < 11 * (i + 1) by omega_arith)]; exact hI.done k hk) hw
    (show 11 * i + 16 ≤ 32 * 11 by omega_arith) (by decide)
  have hm5 : s5.mem = s2.mem := by rw [u5.mem, u4.mem, u3.mem]
  have hg2 : s2.gpr = s.gpr := by rw [g2, g1]
  refine ⟨⟨?_, ?_, by rw [u5.rd, u4.rd, u3.rd, r2, r1, hI.rd], by rw [u5.wr, u4.wr, u3.wr, w2, w1, hI.wr],
    ((((hI.c.pres fun r a b c d _ _ _ l hl => o1 r a b c d l hl).pres (CEY.Hi7.of_lane l2)).pres
      (CEY.Hi7.of_lane u3.lane)).pres (CEY.Hi7.of_lane u4.lane)).pres (CEY.Hi7.of_lane u5.lane),
    by rw [hm5]; exact hf', fun k hk => by rw [hm5, hd' k (by omega_arith), CEY.mix, itT hk],
    fun _ => by rw [u5.lane, u4.lane, u3.lane, l2, hX, show i + 1 - 1 = i by omega_arith]⟩, ?_, ?_⟩
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, hg2, hI.rdi,
      show BitVec.signExtend 64 (32 : BitVec 32) = BitVec.ofNat 64 32 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 32 * i + 32 = 32 * (i + 1) by omega_arith]
  · rw [u5.other _ (by decide), u4.gpr, u3.other _ (by decide), hg2, hI.r8,
      show BitVec.signExtend 64 (11 : BitVec 32) = BitVec.ofNat 64 11 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 11 * i + 11 = 11 * (i + 1) by omega_arith]
  · rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide), hg2]; rfl
  · rw [hz, u4.other _ (by decide), u3.other _ (by decide), hg2]; rfl

theorem main11 (hdd : dArg s₀ .rsi = 11) {s : State} (hdi : s.gpr .rdi = CE.fP s₀) (h8 : s.gpr .r8 = CE.oP s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa ce11V s fun s' => bytesAt s'.mem (CE.oP s₀) (32 * 11) = compressEncode 11 (CE.F s₀) ∧
      Frame [⟨CE.oP s₀, 32 * 11⟩] s₀.mem s'.mem := by
  unfold ce11V
  refine WP.seq (consts11_ok fun s1 hc1 hg1 hm1 hr1 hw1 => wp_mov32i fun s2 u2 => WP.block_nil ?_)
  refine WP.seq (wp_countdown (cnt := .rcx) (N := 31) (by decide) (by decide) (Inv11 s₀)
    (fun i hi s hI _ => step11 hp hdd hi hI) (fun s hI => ?_) (s := s2) ⟨?_, ?_, by rw [u2.rd, hr1, hrd],
      by rw [u2.wr, hw1, hwr], hc1.pres (CEY.Hi7.of_lane u2.lane), by rw [u2.mem, hm1, hm]; exact Frame.refl _ _,
      fun k hk => absurd hk (by omega_arith), fun h => absurd h (by decide)⟩ (by rw [u2.gpr]; rfl))
  · have hL := hI.last (by decide)
    simp only [Nat.reduceSub] at hL
    refine wp_vsh128 fun s1 u1 => group11 hp hdd (g := 31) (by decide) (by rw [u1.gpr, hI.rdi]) (by rw [u1.rd, hI.rd])
      (by rw [u1.wr, hI.wr]) (hI.c.pres fun r _ _ _ _ a _ _ l hl => u1.other r a l hl) (by rw [u1.mem]; exact hI.frame)
      fun s2 h2 o2 g2 m2 r2 w2 => wp_vsh128 fun s3 u3 => wp_vbin128 fun s4 u4 => wp_subi' fun s5 u5 _ => ?_
    have hY : s5.lane .xmm1 0 = XBinOp.eval .por (XShiftOp.eval .pslldq (BitVec.ofNat 128 (Vg s₀ 31)) 5)
        (XShiftOp.eval .psrldq (BitVec.ofNat 128 (Vg s₀ 30)) 6) := by
      rw [u5.lane, u4.val 0 (by decide), itT rfl, u3.val 0 (by decide), itT rfl, u3.other .xmm4 (by decide) 0 (by decide),
        o2 .xmm4 (by decide) (by decide) (by decide) (by decide) 0 (by decide), u1.val 0 (by decide), itT rfl, h2, hL]
      rfl
    have hr8 : s5.gpr .r8 = CE.oP s₀ + BitVec.ofNat 64 336 := by
      rw [u5.gpr, u4.gpr, u3.gpr, g2, u1.gpr, hI.r8, show BitVec.signExtend 64 (5 : BitVec 32) = BitVec.ofNat 64 5 by decide,
        Offset.add_ofNat_sub _ (by decide)]
    refine wp_vst128 (a := CE.oP s₀ + BitVec.ofNat 64 336) (by rw [ea_at, add_ofNat_zero, hr8])
      (by rw [u5.wr, u4.wr, u3.wr, w2, u1.wr]; exact outR hp hdd hI.wr (by omega_arith)) fun s6 g6 l6 m6 r6 w6 =>
      wp_vzu fun s7 _ m7 _ _ => WP.block_nil ?_
    have hw : Written s.mem s6.mem (CE.oP s₀ + BitVec.ofNat 64 336) 16 fun j =>
        (compressEncode 11 (CE.F s₀))[336 + j]! := by
      rw [m6, u5.mem, u4.mem, u3.mem, m2, u1.mem, hY]
      refine (written16 _ _ _).congr fun j hj => ?_
      rw [lastY11 (Vg_lt s₀ 30) (Vg_lt s₀ 31) hj]
      by_cases h : j < 5
      · rw [itT h, show 336 + j = 11 * 30 + (6 + j) by omega_arith, compressEncode_group (c := 8) (b := 11) (by decide)
          (by decide) _ (by omega_arith) (show 6 + j < 11 by omega_arith)]
      · rw [itF h, show 336 + j = 11 * 31 + (j - 5) by omega_arith, compressEncode_group (c := 8) (b := 11) (by decide)
          (by decide) _ (by omega_arith) (show j - 5 < 11 by omega_arith)]
    obtain ⟨hf', hd'⟩ := Written.step (val := fun k => (compressEncode 11 (CE.F s₀))[k]!) hI.frame
      (fun k hk => hI.done k (by omega_arith)) hw (show 336 + 16 ≤ 32 * 11 by omega_arith) (by decide)
    exact ⟨bytesAt_eq! (compressEncode_length _ _) fun k hk => by rw [m7]; exact hd' k (by omega_arith),
      by rw [m7]; exact hf'⟩
  · rw [u2.other _ (by decide), hg1 _ (by decide), hdi]; simp
  · rw [u2.other _ (by decide), hg1 _ (by decide), h8]; simp

theorem step5 (hdd : dArg s₀ .rsi = 5) {i : Nat} (hi : i < 15) {s : State} (hI : Inv5 s₀ i s) :
    WP isa (.block (ce5Pair ++ ([.vmovdquStore .l128 (at_ .r8 0) .xmm1, .alu .add .rdi (.imm 64),
        .alu .add .r8 (.imm 10), .alu .sub .rcx (.imm 1)] : List Instr))) s
      fun s' => Inv5 s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  refine pair5 hp hdd (p := i) (by omega_arith) hI.rdi hI.rd hI.wr hI.c hI.frame fun s1 hX o1 g1 m1 r1 w1 => ?_
  refine wp_vst128 (a := CE.oP s₀ + BitVec.ofNat 64 (10 * i)) (by rw [ea_at, add_ofNat_zero, g1, hI.r8])
    (by rw [w1]; exact outR hp hdd hI.wr (by omega_arith)) fun s2 g2 l2 m2 r2 w2 => ?_
  refine wp_addi' fun s3 u3 => wp_addi' fun s4 u4 => wp_subi' fun s5 u5 hz => WP.block_nil ?_
  have hw : Written s.mem s2.mem (CE.oP s₀ + BitVec.ofNat 64 (10 * i)) 16 fun j =>
      CEY.mix (compressEncode 5 (CE.F s₀)) (10 * (i + 1)) (BitVec.ofNat 128 (Pg s₀ i)) (10 * i) (10 * i + j) := by
    rw [m2, m1, hX]
    refine (written16 _ _ _).congr fun j hj => ?_
    rw [CEY.mix]
    by_cases h : j < 10
    · rw [itT (show 10 * i + j < 10 * (i + 1) by omega_arith), compressEncode_group (c := 16) (b := 10) (by decide)
        (by decide) _ (by omega_arith) h, byte_ofNat128 (Nat.lt_trans (Pg_lt s₀ i) (by decide))]
    · rw [itF (show ¬ 10 * i + j < 10 * (i + 1) by omega_arith), show 10 * i + j - 10 * i = j by omega_arith]
  obtain ⟨hf', hd'⟩ := Written.step (val := CEY.mix (compressEncode 5 (CE.F s₀)) (10 * (i + 1))
    (BitVec.ofNat 128 (Pg s₀ i)) (10 * i)) hI.frame (fun k hk => by
      rw [CEY.mix, itT (show k < 10 * (i + 1) by omega_arith)]; exact hI.done k hk) hw
    (show 10 * i + 16 ≤ 32 * 5 by omega_arith) (by decide)
  have hm5 : s5.mem = s2.mem := by rw [u5.mem, u4.mem, u3.mem]
  have hg2 : s2.gpr = s.gpr := by rw [g2, g1]
  refine ⟨⟨?_, ?_, by rw [u5.rd, u4.rd, u3.rd, r2, r1, hI.rd], by rw [u5.wr, u4.wr, u3.wr, w2, w1, hI.wr],
    ((((hI.c.pres fun r a b c d e _ _ l hl => o1 r a b c d e l hl).pres (CEY.Hi7.of_lane l2)).pres
      (CEY.Hi7.of_lane u3.lane)).pres (CEY.Hi7.of_lane u4.lane)).pres (CEY.Hi7.of_lane u5.lane),
    by rw [hm5]; exact hf', fun k hk => by rw [hm5, hd' k (by omega_arith), CEY.mix, itT hk],
    fun _ => by rw [u5.lane, u4.lane, u3.lane, l2, hX, show i + 1 - 1 = i by omega_arith]⟩, ?_, ?_⟩
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, hg2, hI.rdi,
      show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 64 * i + 64 = 64 * (i + 1) by omega_arith]
  · rw [u5.other _ (by decide), u4.gpr, u3.other _ (by decide), hg2, hI.r8,
      show BitVec.signExtend 64 (10 : BitVec 32) = BitVec.ofNat 64 10 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 10 * i + 10 = 10 * (i + 1) by omega_arith]
  · rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide), hg2]; rfl
  · rw [hz, u4.other _ (by decide), u3.other _ (by decide), hg2]; rfl

theorem main5 (hdd : dArg s₀ .rsi = 5) {s : State} (hdi : s.gpr .rdi = CE.fP s₀) (h8 : s.gpr .r8 = CE.oP s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa ce5V s fun s' => bytesAt s'.mem (CE.oP s₀) (32 * 5) = compressEncode 5 (CE.F s₀) ∧
      Frame [⟨CE.oP s₀, 32 * 5⟩] s₀.mem s'.mem := by
  unfold ce5V
  refine WP.seq (consts5_ok fun s1 hc1 hg1 hm1 hr1 hw1 => wp_mov32i fun s2 u2 => WP.block_nil ?_)
  refine WP.seq (wp_countdown (cnt := .rcx) (N := 15) (by decide) (by decide) (Inv5 s₀)
    (fun i hi s hI _ => step5 hp hdd hi hI) (fun s hI => ?_) (s := s2) ⟨?_, ?_, by rw [u2.rd, hr1, hrd],
      by rw [u2.wr, hw1, hwr], hc1.pres (CEY.Hi7.of_lane u2.lane), by rw [u2.mem, hm1, hm]; exact Frame.refl _ _,
      fun k hk => absurd hk (by omega_arith), fun h => absurd h (by decide)⟩ (by rw [u2.gpr]; rfl))
  · have hL := hI.last (by decide)
    simp only [Nat.reduceSub] at hL
    refine wp_vsh128 fun s1 u1 => pair5 hp hdd (p := 15) (by decide) (by rw [u1.gpr, hI.rdi]) (by rw [u1.rd, hI.rd])
      (by rw [u1.wr, hI.wr]) (hI.c.pres fun r _ _ _ _ _ a _ l hl => u1.other r a l hl) (by rw [u1.mem]; exact hI.frame)
      fun s2 h2 o2 g2 m2 r2 w2 => wp_vsh128 fun s3 u3 => wp_vbin128 fun s4 u4 => wp_subi' fun s5 u5 _ => ?_
    have hY : s5.lane .xmm1 0 = XBinOp.eval .por (XShiftOp.eval .pslldq (BitVec.ofNat 128 (Pg s₀ 15)) 6)
        (XShiftOp.eval .psrldq (BitVec.ofNat 128 (Pg s₀ 14)) 4) := by
      rw [u5.lane, u4.val 0 (by decide), itT rfl, u3.val 0 (by decide), itT rfl, u3.other .xmm5 (by decide) 0 (by decide),
        o2 .xmm5 (by decide) (by decide) (by decide) (by decide) (by decide) 0 (by decide), u1.val 0 (by decide),
        itT rfl, h2, hL]
      rfl
    have hr8 : s5.gpr .r8 = CE.oP s₀ + BitVec.ofNat 64 144 := by
      rw [u5.gpr, u4.gpr, u3.gpr, g2, u1.gpr, hI.r8, show BitVec.signExtend 64 (6 : BitVec 32) = BitVec.ofNat 64 6 by decide,
        Offset.add_ofNat_sub _ (by decide)]
    refine wp_vst128 (a := CE.oP s₀ + BitVec.ofNat 64 144) (by rw [ea_at, add_ofNat_zero, hr8])
      (by rw [u5.wr, u4.wr, u3.wr, w2, u1.wr]; exact outR hp hdd hI.wr (by omega_arith)) fun s6 g6 l6 m6 r6 w6 =>
      wp_vzu fun s7 _ m7 _ _ => WP.block_nil ?_
    have hw : Written s.mem s6.mem (CE.oP s₀ + BitVec.ofNat 64 144) 16 fun j =>
        (compressEncode 5 (CE.F s₀))[144 + j]! := by
      rw [m6, u5.mem, u4.mem, u3.mem, m2, u1.mem, hY]
      refine (written16 _ _ _).congr fun j hj => ?_
      rw [CEY.lastY (Pg_lt s₀ 14) (Pg_lt s₀ 15) hj]
      by_cases h : j < 6
      · rw [itT h, show 144 + j = 10 * 14 + (4 + j) by omega_arith, compressEncode_group (c := 16) (b := 10) (by decide)
          (by decide) _ (by omega_arith) (show 4 + j < 10 by omega_arith)]
      · rw [itF h, show 144 + j = 10 * 15 + (j - 6) by omega_arith, compressEncode_group (c := 16) (b := 10) (by decide)
          (by decide) _ (by omega_arith) (show j - 6 < 10 by omega_arith)]
    obtain ⟨hf', hd'⟩ := Written.step (val := fun k => (compressEncode 5 (CE.F s₀))[k]!) hI.frame
      (fun k hk => hI.done k (by omega_arith)) hw (show 144 + 16 ≤ 32 * 5 by omega_arith) (by decide)
    exact ⟨bytesAt_eq! (compressEncode_length _ _) fun k hk => by rw [m7]; exact hd' k (by omega_arith),
      by rw [m7]; exact hf'⟩
  · rw [u2.other _ (by decide), hg1 _ (by decide), hdi]; simp
  · rw [u2.other _ (by decide), hg1 _ (by decide), h8]; simp

end

theorem wp {s₀ : State} (hp : compressEncode1024K.pre s₀) :
    WP isa compressEncode1024Avx2 s₀ fun s' =>
      bytesAt s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat = compressEncode (dArg s₀ .rsi) (CE.F s₀) ∧
        Frame [⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩] s₀.mem s'.mem := by
  have hd := hp.2.2.2.2.2.1
  rw [CE.lenEq hp rfl]
  unfold compressEncode1024Avx2
  refine WP.seq (WP.mono (MlKem1024.X86_64.cePrologue_ok s₀) fun s₁ ⟨⟨_, r8₁, z₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from z₁) (fun h => ?_) (fun h => ?_)
  · rw [sub_beq_zero32, decide_eq_true_eq] at h
    have h5 : dArg s₀ .rsi = 5 := by simp only [dArg, h]; rfl
    rw [h5]
    exact main5 hp h5 di₁ r8₁ k₁.2.1 k₁.2.2 m₁
  · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
    have h11 : dArg s₀ .rsi = 11 := by
      rcases MlKem1024.X86_64.widths1024 hd with e | e
      · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h
      · exact e
    rw [h11]
    exact main11 hp h11 di₁ r8₁ k₁.2.1 k₁.2.2 m₁

theorem correct (s : State) (hs : compressEncode1024K.pre s) :
    ∃ t s', Exec isa compressEncode1024Avx2 s t s' ∧ abiPreserved s s' ∧ compressEncode1024K.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := compressEncode1024Avx2)
    [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10] (wp hs) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

end VG.Proof.MlKem1024.X86_64.CEW

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem1024.X86_64 VG.Proof.MlKem.X86_64

theorem compressEncode1024Y_ct :
    ConstantTime isa compressEncode1024K.pre compressEncode1024K.pub compressEncode1024Avx2 :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rdx, .rcx, .rsp] [.rsi])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

/-- `vg_mlkem1024_compress_encode_avx2`, for the calls of the top-level functions. -/
theorem ceImpl1024Y : CEImpl "vg_mlkem1024_compress_encode_avx2" compressEncode1024Avx2
    Proof.MlKem1024.compressWidths :=
  ⟨fun _ hd => by rcases widths1024 hd with rfl | rfl <;> decide, CEW.correct, compressEncode1024Y_ct,
    nosp_of (by decide +kernel), by decide +kernel⟩

end VG.Proof.MlKem1024.X86_64

end

end

/-!
# ML-KEM-1024 on x86-64: the compressions its functions run

`vg_mlkem1024_compress_encode` and `vg_mlkem1024_decode_decompress`, or their
AVX2 implementations, for its widths.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64

/-- The implementations of `vg_mlkem1024_compress_encode` and `vg_mlkem1024_decode_decompress`. -/
theorem ce1024I : ∀ cs : Codecs, CEImpl (ceN1024 cs) (ce1024 cs) Proof.MlKem1024.compressWidths
  | .base => ceImpl1024
  | .avx2 => ceImpl1024Y

theorem dd1024I : ∀ cs : Codecs, DDImpl (ddN1024 cs) (dd1024 cs) Proof.MlKem1024.compressWidths
  | .base => ddImpl1024
  | .avx2 => ddImpl1024Y

/-- The compressions it calls. -/
theorem calls1024 : KemCalls kem1024 Proof.MlKem1024.compressWidths Proof.MlKem1024.compressWidths :=
  ⟨ce1024I, dd1024I, by decide, by decide⟩

end VG.Proof.MlKem1024.X86_64
