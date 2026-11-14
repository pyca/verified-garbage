module

public import VerifiedGarbage.Proof.MlKem.X86_64.CompressMul
public import VerifiedGarbage.Impl.MlKem1024.X86_64.CompressAvx2
import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.CompressMul
meta import VerifiedGarbage.Impl.MlKem1024.X86_64.CompressAvx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.VPack
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# ML-KEM-1024 on x86-64: `ByteEncode_d ∘ Compress_d` with multiplications, in an MXCSR region

`cm11` and `cm5` (`Impl/MlKem1024/X86_64/CompressAvx2.lean`) meet the contract
of `vg_mlkem1024_compress_encode` for one width each, as `cm10` and `cm4` do
that of ML-KEM-768's (`Proof/MlKem/X86_64/CompressMul.lean`, whose words,
lanes and loads these share): a lane of pairs of eleven bits is the number of
its 88 bits (`toNat_q11`), and the two lanes' 22 bytes are stored as sixteen,
four and two (`pack11`); the pairs of two halves of 32 coefficients of five
bits are packed and paired again (`dword_pair`), and their four quadwords of
forty bits gathered (`pack5`).
-/

@[expose] public section

namespace VG.Proof.MlKem1024.X86_64.CMW

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.Sha3.X86_64 (WP.cons)
open VG.Proof.MlKem.X86_64.S4 (LUpd wp_vbin wp_vvar wp_vld256 GUpd wp_addi' itT itF)
open VG.Proof.MlKem.X86_64.D12Y (wp_vsh wp_subi' wp_vzu wp_mov32i yconst4_ok yconst_ok' wp_vbin128)
open VG.Proof.MlKem.X86_64.CEY
open VG.Proof.MlKem.X86_64.CMY

/-! ## A word -/

theorem hiW11 {x : BitVec 16} {z : Zq} (hx : x.toNat = z.val) : (hiW 36 0x2000 0x7FF x).toNat = compress 11 z :=
  word_formula (by decide +kernel) hx

theorem loW5 {x : BitVec 16} {z : Zq} (hx : x.toNat = z.val) : (loW 0x400 0x1F x).toNat = compress 5 z :=
  word_formula (by decide +kernel) hx

/-! ## Packing eleven bits -/

/-- The constants of `cmPack11`: the shifts of `vpsllvd` and of `vpsrlvq`. -/
def s10 : BitVec 128 := (10 : BitVec 64) ++ (10 : BitVec 64)
def v1030 : BitVec 128 := (30 : BitVec 64) ++ (10 : BitVec 64)

/-- A lane of pairs after the shifts of `cmPack11`. -/
abbrev q11 (D : BitVec 128) : BitVec 128 :=
  XBinOp.eval .paddq (VVarOp.eval .vpsrlvq (VVarOp.eval .vpsllvd D s10) v1030)
    (XShiftOp.eval .psllq (XShiftOp.eval .psrldq (VVarOp.eval .vpsllvd D s10) 8) 34)

/-- `q11`: the number whose 88 bits are the four pairs. -/
theorem toNat_q11 {D : BitVec 128} {p : Nat → Nat} (hp : ∀ i < 4, (dword D i).toNat = p i)
    (hlt : ∀ i < 4, p i < 2 ^ 22) : (q11 D).toNat = p 0 + 2 ^ 22 * p 1 + 2 ^ 44 * (p 2 + 2 ^ 22 * p 3) := by
  have b0 := hlt 0 (by decide); have b1 := hlt 1 (by decide); have b2 := hlt 2 (by decide)
  have b3 := hlt 3 (by decide)
  have h0 : (dword (VVarOp.eval .vpsllvd D s10) 0).toNat = p 0 * 2 ^ 10 := by
    rw [dword_sllv _ _ (by decide), show (dword s10 0).toNat = 10 from rfl, itT (by decide), BitVec.toNat_shiftLeft,
      Nat.shiftLeft_eq, hp 0 (by decide)]
    exact Nat.mod_eq_of_lt (by omega_arith)
  have h1 : (dword (VVarOp.eval .vpsllvd D s10) 1).toNat = p 1 := by
    rw [dword_sllv _ _ (by decide), show (dword s10 1).toNat = 0 from rfl, itT (by decide), BitVec.shiftLeft_zero,
      hp 1 (by decide)]
  have h2 : (dword (VVarOp.eval .vpsllvd D s10) 2).toNat = p 2 * 2 ^ 10 := by
    rw [dword_sllv _ _ (by decide), show (dword s10 2).toNat = 10 from rfl, itT (by decide), BitVec.toNat_shiftLeft,
      Nat.shiftLeft_eq, hp 2 (by decide)]
    exact Nat.mod_eq_of_lt (by omega_arith)
  have h3 : (dword (VVarOp.eval .vpsllvd D s10) 3).toNat = p 3 := by
    rw [dword_sllv _ _ (by decide), show (dword s10 3).toNat = 0 from rfl, itT (by decide), BitVec.shiftLeft_zero,
      hp 3 (by decide)]
  dsimp only [q11]
  generalize VVarOp.eval .vpsllvd D s10 = A at h0 h1 h2 h3
  have a0 : (qword A 0).toNat = 2 ^ 10 * (p 0 + 2 ^ 22 * p 1) := by rw [toNat_qword0, h0, h1]; omega_arith
  have a1 : (qword A 1).toNat = 2 ^ 10 * (p 2 + 2 ^ 22 * p 3) := by rw [toNat_qword1, h2, h3]; omega_arith
  have l0 : p 0 + 2 ^ 22 * p 1 < 2 ^ 44 := by omega_arith
  have l1 : p 2 + 2 ^ 22 * p 3 < 2 ^ 44 := by omega_arith
  generalize p 0 + 2 ^ 22 * p 1 = Q₀ at a0 l0 ⊢
  generalize p 2 + 2 ^ 22 * p 3 = Q₁ at a1 l1 ⊢
  have eV : VVarOp.eval .vpsrlvq A v1030 = (qword A 1 >>> 30) ++ (qword A 0 >>> 10) := by
    simp only [VVarOp.eval, show (qword v1030 0).toNat = 10 from rfl, show (qword v1030 1).toNat = 30 from rfl,
      show 10 < 64 by decide, show 30 < 64 by decide, ↓reduceIte]
  have eB0 : (qword (XShiftOp.eval .psllq (XShiftOp.eval .psrldq A 8) 34) 0).toNat =
      (qword A 1).toNat * 2 ^ 34 % 2 ^ 64 := by
    rw [psrldq8]
    simp only [XShiftOp.eval, show (34 : BitVec 8).toNat = 34 from rfl, show ¬ 63 < 34 by decide, ↓reduceIte,
      qword_app0, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, toNat_qword0, toNat_qword1, dword_ofDwords_0,
      dword_ofDwords_1]
  have eB1 : (qword (XShiftOp.eval .psllq (XShiftOp.eval .psrldq A 8) 34) 1).toNat = 0 := by
    rw [psrldq8]
    simp only [XShiftOp.eval, show (34 : BitVec 8).toNat = 34 from rfl, show ¬ 63 < 34 by decide, ↓reduceIte,
      qword_app1, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, toNat_qword1, dword_ofDwords_2, dword_ofDwords_3,
      show (0 : BitVec 32).toNat = 0 from rfl]
  generalize XShiftOp.eval .psllq (XShiftOp.eval .psrldq A 8) 34 = Y at eB0 eB1
  have m1 : 2 ^ 10 * Q₁ * 2 ^ 34 % 2 ^ 64 = 2 ^ 44 * (Q₁ % 2 ^ 20) := by omega_arith
  have m2 : 2 ^ 10 * Q₁ / 2 ^ 30 = Q₁ / 2 ^ 20 := by omega_arith
  have m3 : 2 ^ 10 * Q₀ / 2 ^ 10 = Q₀ := by omega_arith
  rw [toNat_qwords, eV]
  simp only [XBinOp.eval, qword_app0, qword_app1, BitVec.toNat_add, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, a0, a1, eB0, eB1, m1, m2, m3]
  omega_arith

/-- `cmPack11` on the two lanes `D₀`, `D₁` of pairs `p`, `p'`: the sixteen
bytes it stores first, the low ones of the number `V` whose 22 bytes are the
group's, and the 48 bits it then stores from `rax`. -/
theorem pack11 {D₀ D₁ : BitVec 128} {p p' : Nat → Nat} (hp : ∀ i < 4, (dword D₀ i).toNat = p i)
    (hp' : ∀ i < 4, (dword D₁ i).toNat = p' i) (hlt : ∀ i < 4, p i < 2 ^ 22) (hlt' : ∀ i < 4, p' i < 2 ^ 22)
    {V : Nat} (hV : V = p 0 + 2 ^ 22 * p 1 + 2 ^ 44 * (p 2 + 2 ^ 22 * p 3) +
      2 ^ 88 * (p' 0 + 2 ^ 22 * p' 1 + 2 ^ 44 * (p' 2 + 2 ^ 22 * p' 3))) :
    XBinOp.eval .por (q11 D₀) (XShiftOp.eval .pslldq (q11 D₁) 11) = BitVec.ofNat 128 V ∧
      (XShiftOp.eval .psrldq (q11 D₁) 5).extractLsb' 0 64 = BitVec.ofNat 64 (V / 2 ^ 128) := by
  have eA := toNat_q11 hp hlt
  have eB := toNat_q11 hp' hlt'
  have c0 := hlt 0 (by decide); have c1 := hlt 1 (by decide); have c2 := hlt 2 (by decide)
  have c3 := hlt 3 (by decide); have d0 := hlt' 0 (by decide); have d1 := hlt' 1 (by decide)
  have d2 := hlt' 2 (by decide); have d3 := hlt' 3 (by decide)
  have hA : p 0 + 2 ^ 22 * p 1 + 2 ^ 44 * (p 2 + 2 ^ 22 * p 3) < 2 ^ 88 := by omega_arith
  have hN : p' 0 + 2 ^ 22 * p' 1 + 2 ^ 44 * (p' 2 + 2 ^ 22 * p' 3) < 2 ^ 88 := by omega_arith
  generalize q11 D₀ = E₀ at eA
  generalize q11 D₁ = E₁ at eB
  generalize p 0 + 2 ^ 22 * p 1 + 2 ^ 44 * (p 2 + 2 ^ 22 * p 3) = A at hV eA hA
  generalize p' 0 + 2 ^ 22 * p' 1 + 2 ^ 44 * (p' 2 + 2 ^ 22 * p' 3) = N at hV eB hN
  have eS : (XShiftOp.eval .pslldq E₁ 11).toNat = 2 ^ 88 * (N % 2 ^ 40) := by
    simp only [XShiftOp.eval, show (11 : BitVec 8).toNat = 11 from rfl, show min 11 16 * 8 = 88 from rfl,
      BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, eB]
    omega_arith
  have eR : (XShiftOp.eval .psrldq E₁ 5).toNat = N / 2 ^ 40 := by
    simp only [XShiftOp.eval, show (5 : BitVec 8).toNat = 5 from rfl, show min 5 16 * 8 = 40 from rfl,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, eB]
  constructor
  · apply BitVec.eq_of_toNat_eq
    show (E₀ ||| XShiftOp.eval .pslldq E₁ 11).toNat = _
    rw [BitVec.toNat_or, eA, eS, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hA, BitVec.toNat_ofNat, hV]
    omega_arith
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, eR, BitVec.toNat_ofNat, hV, Nat.shiftRight_zero]
    omega_arith

/-! ## Packing five bits -/

/-- The masks of `cmPack5`. -/
def m5a : BitVec 128 := (0x800c0b0a09088080 : BitVec 64) ++ (0x8080800403020100 : BitVec 64)
def m5b : BitVec 128 := (0x0880808080800403 : BitVec 64) ++ (0x0201008080808080 : BitVec 64)

/-- `cmPack5`, after its pairs are paired and shifted: on the two lanes
`Q₀`, `Q₁` whose quadwords are the forty bits of coefficients 0 to 7 and 16
to 23, and 8 to 15 and 24 to 31: the sixteen bytes it stores first, and the
doubleword it stores next. -/
theorem pack5 {Q₀ Q₁ : BitVec 128} {a₀ a₁ b₀ b₁ : Nat} (h₀ : (qword Q₀ 0).toNat = a₀) (h₁ : (qword Q₁ 0).toNat = a₁)
    (g₀ : (qword Q₀ 1).toNat = b₀) (g₁ : (qword Q₁ 1).toNat = b₁) (la₀ : a₀ < 2 ^ 40) (la₁ : a₁ < 2 ^ 40)
    (lb₀ : b₀ < 2 ^ 40) {V : Nat} (hV : V = a₀ + 2 ^ 40 * a₁ + 2 ^ 80 * b₀ + 2 ^ 120 * b₁) :
    XBinOp.eval .por (XBinOp.eval .pshufb Q₀ m5a) (XBinOp.eval .pshufb Q₁ m5b) = BitVec.ofNat 128 V ∧
      dword (XShiftOp.eval .psrldq Q₁ 9) 0 = BitVec.ofNat 32 (V / 2 ^ 128) := by
  have ea : XBinOp.eval .pshufb Q₀ m5a = ofBytes fun i =>
      if i < 5 then byte Q₀ i else if i < 10 then 0 else if i < 15 then byte Q₀ (8 + (i - 10)) else 0 := by
    simp only [XBinOp.eval, ofBytes]; rfl
  have eb : XBinOp.eval .pshufb Q₁ m5b = ofBytes fun i =>
      if i < 5 then 0 else if i < 10 then byte Q₁ (i - 5) else if i < 15 then 0 else byte Q₁ (8 + 0) := by
    simp only [XBinOp.eval, ofBytes]; rfl
  constructor
  · rw [ea, eb]
    refine ext_byte fun t ht => ?_
    simp only [XBinOp.eval, byte_or, byte_ofBytes _ ht, toNat_byte (BitVec.ofNat 128 _), BitVec.toNat_ofNat]
    rcases (by omega_arith : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨
      t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceAdd, BitVec.toNat_or, Nat.or_zero, Nat.zero_or,
      toNat_byte_lo _ (show (0 : Nat) < 8 by decide), toNat_byte_lo _ (show (1 : Nat) < 8 by decide),
      toNat_byte_lo _ (show (2 : Nat) < 8 by decide), toNat_byte_lo _ (show (3 : Nat) < 8 by decide),
      toNat_byte_lo _ (show (4 : Nat) < 8 by decide), show byte Q₀ 8 = byte Q₀ (8 + 0) from rfl,
      show byte Q₁ 8 = byte Q₁ (8 + 0) from rfl, show byte Q₀ 9 = byte Q₀ (8 + 1) from rfl,
      show byte Q₀ 10 = byte Q₀ (8 + 2) from rfl, show byte Q₀ 11 = byte Q₀ (8 + 3) from rfl,
      show byte Q₀ 12 = byte Q₀ (8 + 4) from rfl, toNat_byte_hi _ (show (0 : Nat) < 8 by decide),
      toNat_byte_hi _ (show (1 : Nat) < 8 by decide), toNat_byte_hi _ (show (2 : Nat) < 8 by decide),
      toNat_byte_hi _ (show (3 : Nat) < 8 by decide), toNat_byte_hi _ (show (4 : Nat) < 8 by decide), h₀, h₁, g₀, g₁,
      hV, show (0 : BitVec 8).toNat = 0 from rfl, Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one] <;>
    omega_arith
  · apply BitVec.eq_of_toNat_eq
    have e := toNat_qwords Q₁
    rw [h₁, g₁] at e
    have hX : a₀ + 2 ^ 40 * a₁ + 2 ^ 80 * b₀ < 2 ^ 120 := by omega_arith
    have e1 : (a₁ + 2 ^ 64 * b₁) / 2 ^ 72 = b₁ / 2 ^ 8 := by
      rw [show (72 : Nat) = 64 + 8 from rfl, Nat.pow_add, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos 64), Nat.div_eq_of_lt (show a₁ < 2 ^ 64 by omega_arith), Nat.zero_add]
    have e2 : (a₀ + 2 ^ 40 * a₁ + 2 ^ 80 * b₀ + 2 ^ 120 * b₁) / 2 ^ 128 = b₁ / 2 ^ 8 := by
      rw [show (128 : Nat) = 120 + 8 from rfl, Nat.pow_add, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos 120), Nat.div_eq_of_lt hX, Nat.zero_add]
    rw [toNat_dword', Nat.mul_zero, Nat.pow_zero, Nat.div_one, BitVec.toNat_ofNat, hV, e2]
    simp only [XShiftOp.eval, show (9 : BitVec 8).toNat = 9 from rfl, show min 9 16 * 8 = 72 from rfl,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, e, e1]

/-! ## Steps -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_shr32 {d : Reg} (k : ∀ s', GUpd s s' d (s.gpr d >>> 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d 32 :: is)) s Q :=
  WP.cons rfl (k _ (GUpd.withFlags _ _ _ _ _ _ _))

theorem wp_store16 {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 2)
    (k : ∀ s', s'.gpr = s.gpr → (∀ x l, s'.lane x l = s.lane x l) →
      s'.mem = s.mem.writeW a ((s.gpr r).setWidth 16) → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store16 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r).setWidth 16) }) ?_
    (k _ rfl (fun _ _ => rfl) rfl rfl rfl)
  simp [exec, State.store16, ha, hout]

theorem wp_vmovdqa256 {d a : XReg} (k : ∀ s', LUpd s s' d (fun l => s.lane a l) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vmovdqa .l256 d a) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d (s.lane a 0) (s.lane a 1)) rfl (k _ (by
    have h := LUpd.setV256 s d (s.lane a 0) (s.lane a 1)
    exact ⟨fun l hl => by rw [h.val l hl]; rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
      h.other, h.gpr, h.mem, h.rd, h.wr, h.syms⟩))

end

/-! ## The constants -/

/-- The constants of `cm11`. -/
structure C11 (s : State) : Prop where
  c8 : ∀ l < 2, s.lane .xmm8 l = wc 0x75F875F8
  c9 : ∀ l < 2, s.lane .xmm9 l = wc 0x00240024
  c10 : ∀ l < 2, s.lane .xmm10 l = wc 0x4EBF4EBF
  c11 : ∀ l < 2, s.lane .xmm11 l = wc 0x20002000
  c12 : ∀ l < 2, s.lane .xmm12 l = wc 0x07FF07FF
  c13 : ∀ l < 2, s.lane .xmm13 l = wc 0x08000001
  c14 : ∀ l < 2, s.lane .xmm14 l = s10
  c7 : ∀ l < 2, s.lane .xmm7 l = v1030

theorem C11.pres {s s' : State} (h : C11 s) (hk : Hi7 s s') : C11 s' :=
  ⟨fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c8 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c9 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c10 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c11 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c12 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c13 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c14 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c7 l hl]⟩

/-- The constants of `cm5`. -/
structure C5 (s : State) : Prop where
  c10 : ∀ l < 2, s.lane .xmm10 l = wc 0x4EBF4EBF
  c11 : ∀ l < 2, s.lane .xmm11 l = wc 0x04000400
  c12 : ∀ l < 2, s.lane .xmm12 l = wc 0x001F001F
  c13 : ∀ l < 2, s.lane .xmm13 l = wc 0x00200001
  c8 : ∀ l < 2, s.lane .xmm8 l = wc 0x04000001
  c14 : ∀ l < 2, s.lane .xmm14 l = s12
  c7 : ∀ l < 2, s.lane .xmm7 l = m5a
  c9 : ∀ l < 2, s.lane .xmm9 l = m5b

theorem C5.pres {s s' : State} (h : C5 s) (hk : Hi7 s s') : C5 s' :=
  ⟨fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c10 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c11 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c12 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c13 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c8 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c14 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c7 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c9 l hl]⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem consts11_ok
    (k : ∀ s', C11 s' → (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (cm11Consts ++ is)) s Q := by
  simp only [cm11Consts, List.append_assoc]
  refine yconst_ok' _ _ fun s1 a1 o1 g1 m1 r1 w1 => yconst_ok' _ _ fun s2 a2 o2 g2 m2 r2 w2 =>
    yconst_ok' _ _ fun s3 a3 o3 g3 m3 r3 w3 => yconst_ok' _ _ fun s4 a4 o4 g4 m4 r4 w4 =>
    yconst_ok' _ _ fun s5 a5 o5 g5 m5 r5 w5 => yconst_ok' _ _ fun s6 a6 o6 g6 m6 r6 w6 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s7 a7 b7 o7 g7 m7 r7 w7 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s8 a8 b8 o8 g8 m8 r8 w8 =>
    k s8 ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_,
      fun l hl => ?_, fun l hl => ?_⟩ (fun g hg => ?_) ?_ ?_ ?_
  · rw [o8 _ (by decide) (by decide) (by decide) l hl, o7 _ (by decide) (by decide) (by decide) l hl,
      o6 _ (by decide) l hl, o5 _ (by decide) l hl, o4 _ (by decide) l hl, o3 _ (by decide) l hl,
      o2 _ (by decide) l hl, a1 l hl]
  · rw [o8 _ (by decide) (by decide) (by decide) l hl, o7 _ (by decide) (by decide) (by decide) l hl,
      o6 _ (by decide) l hl, o5 _ (by decide) l hl, o4 _ (by decide) l hl, o3 _ (by decide) l hl, a2 l hl]
  · rw [o8 _ (by decide) (by decide) (by decide) l hl, o7 _ (by decide) (by decide) (by decide) l hl,
      o6 _ (by decide) l hl, o5 _ (by decide) l hl, o4 _ (by decide) l hl, a3 l hl]
  · rw [o8 _ (by decide) (by decide) (by decide) l hl, o7 _ (by decide) (by decide) (by decide) l hl,
      o6 _ (by decide) l hl, o5 _ (by decide) l hl, a4 l hl]
  · rw [o8 _ (by decide) (by decide) (by decide) l hl, o7 _ (by decide) (by decide) (by decide) l hl,
      o6 _ (by decide) l hl, a5 l hl]
  · rw [o8 _ (by decide) (by decide) (by decide) l hl, o7 _ (by decide) (by decide) (by decide) l hl, a6 l hl]
  · rw [o8 _ (by decide) (by decide) (by decide) l hl]
    rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
    exacts [a7, b7]
  · rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
    exacts [a8, b8]
  · rw [g8 g hg, g7 g hg, g6 g hg, g5 g hg, g4 g hg, g3 g hg, g2 g hg, g1 g hg]
  · rw [m8, m7, m6, m5, m4, m3, m2, m1]
  · rw [r8, r7, r6, r5, r4, r3, r2, r1]
  · rw [w8, w7, w6, w5, w4, w3, w2, w1]

theorem consts5_ok
    (k : ∀ s', C5 s' → (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (cm5Consts ++ is)) s Q := by
  simp only [cm5Consts, List.append_assoc]
  refine yconst_ok' _ _ fun s1 a1 o1 g1 m1 r1 w1 => yconst_ok' _ _ fun s2 a2 o2 g2 m2 r2 w2 =>
    yconst_ok' _ _ fun s3 a3 o3 g3 m3 r3 w3 => yconst_ok' _ _ fun s4 a4 o4 g4 m4 r4 w4 =>
    yconst_ok' _ _ fun s5 a5 o5 g5 m5 r5 w5 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s6 a6 b6 o6 g6 m6 r6 w6 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s7 a7 b7 o7 g7 m7 r7 w7 =>
    yconst4_ok (by decide) (by decide) _ _ _ _ fun s8 a8 b8 o8 g8 m8 r8 w8 =>
    k s8 ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_,
      fun l hl => ?_, fun l hl => ?_⟩ (fun g hg => ?_) ?_ ?_ ?_
  · rw [o8 _ (by decide) (by decide) (by decide) l hl, o7 _ (by decide) (by decide) (by decide) l hl,
      o6 _ (by decide) (by decide) (by decide) l hl, o5 _ (by decide) l hl, o4 _ (by decide) l hl,
      o3 _ (by decide) l hl, o2 _ (by decide) l hl, a1 l hl]
  · rw [o8 _ (by decide) (by decide) (by decide) l hl, o7 _ (by decide) (by decide) (by decide) l hl,
      o6 _ (by decide) (by decide) (by decide) l hl, o5 _ (by decide) l hl, o4 _ (by decide) l hl,
      o3 _ (by decide) l hl, a2 l hl]
  · rw [o8 _ (by decide) (by decide) (by decide) l hl, o7 _ (by decide) (by decide) (by decide) l hl,
      o6 _ (by decide) (by decide) (by decide) l hl, o5 _ (by decide) l hl, o4 _ (by decide) l hl, a3 l hl]
  · rw [o8 _ (by decide) (by decide) (by decide) l hl, o7 _ (by decide) (by decide) (by decide) l hl,
      o6 _ (by decide) (by decide) (by decide) l hl, o5 _ (by decide) l hl, a4 l hl]
  · rw [o8 _ (by decide) (by decide) (by decide) l hl, o7 _ (by decide) (by decide) (by decide) l hl,
      o6 _ (by decide) (by decide) (by decide) l hl, a5 l hl]
  · rw [o8 _ (by decide) (by decide) (by decide) l hl, o7 _ (by decide) (by decide) (by decide) l hl]
    rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
    exacts [a6, b6]
  · rw [o8 _ (by decide) (by decide) (by decide) l hl]
    rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
    exacts [a7, b7]
  · rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
    exacts [a8, b8]
  · rw [g8 g hg, g7 g hg, g6 g hg, g5 g hg, g4 g hg, g3 g hg, g2 g hg, g1 g hg]
  · rw [m8, m7, m6, m5, m4, m3, m2, m1]
  · rw [r8, r7, r6, r5, r4, r3, r2, r1]
  · rw [w8, w7, w6, w5, w4, w3, w2, w1]

/-! ## A group of eleven bits -/

theorem dig16_11 (c : Nat → Nat) : digits 11 ((List.range 16).map c) =
    c 0 + 2 ^ 11 * c 1 + 2 ^ 22 * (c 2 + 2 ^ 11 * c 3) +
        2 ^ 44 * (c 4 + 2 ^ 11 * c 5 + 2 ^ 22 * (c 6 + 2 ^ 11 * c 7)) +
      2 ^ 88 * (c 8 + 2 ^ 11 * c 9 + 2 ^ 22 * (c 10 + 2 ^ 11 * c 11) +
        2 ^ 44 * (c 12 + 2 ^ 11 * c 13 + 2 ^ 22 * (c 14 + 2 ^ 11 * c 15))) := by
  show digits 11 [c 0, c 1, c 2, c 3, c 4, c 5, c 6, c 7, c 8, c 9, c 10, c 11, c 12, c 13, c 14, c 15] = _
  simp only [digits_cons, digits_nil, Nat.reducePow]
  omega_arith

/-- A group of `d = 11`: the sixteen coefficients `z` at `rdi`, compressed,
and the 22 bytes of the number `V` whose digits they are stored at `r8`:
sixteen, then the low 32 bits of `V / 2¹²⁸`, then its next sixteen. -/
theorem grp11_ok (hc : C11 s) (hin0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 0) 32)
    (hin1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (0 + 32)) 32) {z : Nat → Zq}
    (hx : ∀ j < 16, (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (0 + 4 * j)) 32).toNat = (z j).val)
    (hw16 : InRegions s.wr (s.gpr .r8) 16) (hw4 : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 16) 4)
    (hw2 : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 20) 2)
    (k : ∀ s', s'.mem = ((s.mem.writeW (s.gpr .r8)
          (BitVec.ofNat 128 (digits 11 ((List.range 16).map fun j => compress 11 (z j))))).writeW
        (s.gpr .r8 + BitVec.ofNat 64 16)
          ((BitVec.ofNat 64 (digits 11 ((List.range 16).map fun j => compress 11 (z j)) / 2 ^ 128)).setWidth 32)).writeW
        (s.gpr .r8 + BitVec.ofNat 64 20)
          ((BitVec.ofNat 64 (digits 11 ((List.range 16).map fun j => compress 11 (z j)) / 2 ^ 128) >>> 32).setWidth 16) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → ∀ l < 2, s'.lane r l = s.lane r l) →
      (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (cmLd 0 ++ (toY cmHi ++ (cmPack11 ++ is)))) s Q := by
  refine ld_ok hin0 hin1 hx (fun j _ => val_lt _) fun s1 h1 o1 g1 m1 r1 w1 => ?_
  refine hi_ok fun s2 h2 o2 g2 m2 r2 w2 => ?_
  simp only [cmPack11, yb, List.cons_append, List.nil_append]
  refine wp_vvar fun s3 u3 => wp_vsh fun s4 u4 => wp_vvar fun s5 u5 => wp_vsh fun s6 u6 => wp_vbin fun s7 u7 =>
    wp_vext1 fun s8 u8 => wp_vsh128 fun s9 u9 => wp_vbin128 fun s10 u10 => ?_
  have cK : ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → ∀ l < 2, s2.lane r l = s.lane r l :=
    fun r a b c d l hl => by rw [o2 r a b c d l hl, o1 r a b l hl]
  have D : ∀ l < 2, ∀ i < 4, (dword (s2.lane .xmm0 l) i).toNat =
      compress 11 (z (8 * l + 2 * i)) + 2 ^ 11 * compress 11 (z (8 * l + (2 * i + 1))) := fun l hl i hi => by
    rw [h2 l hl, o1 .xmm8 (by decide) (by decide) l hl, o1 .xmm9 (by decide) (by decide) l hl,
      o1 .xmm10 (by decide) (by decide) l hl, o1 .xmm11 (by decide) (by decide) l hl,
      o1 .xmm12 (by decide) (by decide) l hl, o1 .xmm13 (by decide) (by decide) l hl, hc.c8 l hl, hc.c9 l hl,
      hc.c10 l hl, hc.c11 l hl, hc.c12 l hl, hc.c13 l hl]
    exact dword_hiL (d := 11) (off := 36) (sh := 0x2000) (mk := 0x7FF) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (c := fun j => compress 11 (z (8 * l + j)))
      (fun j hj => hiW11 (h1 l hl j hj)) (fun j _ => compress_lt _ _) hi
  have E : ∀ l < 2, s7.lane .xmm0 l = q11 (s2.lane .xmm0 l) := fun l hl => by
    rw [u7.val l hl, u6.val l hl, u6.other .xmm0 (by decide) l hl, u5.val l hl, u5.other .xmm1 (by decide) l hl,
      u4.val l hl, u4.other .xmm0 (by decide) l hl, u4.other .xmm7 (by decide) l hl, u3.val l hl,
      u3.other .xmm7 (by decide) l hl, cK .xmm7 (by decide) (by decide) (by decide) (by decide) l hl, hc.c7 l hl,
      cK .xmm14 (by decide) (by decide) (by decide) (by decide) l hl, hc.c14 l hl]
    rfl
  have lt : ∀ l < 2, ∀ i < 4, compress 11 (z (8 * l + 2 * i)) + 2 ^ 11 * compress 11 (z (8 * l + (2 * i + 1))) <
      2 ^ 22 := fun l _ i _ => by
    have := compress_lt 11 (z (8 * l + 2 * i)); have := compress_lt 11 (z (8 * l + (2 * i + 1))); omega_arith
  obtain ⟨hR, hT⟩ := pack11 (D 0 (by decide)) (D 1 (by decide)) (lt 0 (by decide)) (lt 1 (by decide))
    (V := digits 11 ((List.range 16).map fun j => compress 11 (z j))) (by rw [dig16_11])
  have g10 : s10.gpr = s.gpr := by
    rw [u10.gpr, u9.gpr, u8.gpr, u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, g2, g1]
  have m10 : s10.mem = s.mem := by
    rw [u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, m2, m1]
  have w10 : s10.wr = s.wr := by rw [u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, w2, w1]
  have r10 : s10.rd = s.rd := by rw [u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, r2, r1]
  have y1 : s10.lane .xmm1 0 = q11 (s2.lane .xmm0 1) := by
    rw [u10.other .xmm1 (by decide) 0 (by decide), u9.other .xmm1 (by decide) 0 (by decide), u8.val 0 (by decide),
      itT rfl, E 1 (by decide)]
  have x0 : s10.lane .xmm0 0 = BitVec.ofNat 128 (digits 11 ((List.range 16).map fun j => compress 11 (z j))) := by
    rw [u10.val 0 (by decide), itT rfl, u9.other .xmm0 (by decide) 0 (by decide),
      u8.other .xmm0 (by decide) 0 (by decide), E 0 (by decide), u9.val 0 (by decide), itT rfl,
      u8.val 0 (by decide), itT rfl, E 1 (by decide)]
    exact hR
  refine wp_vst128 (a := s.gpr .r8) (by rw [ea_at, add_ofNat_zero, g10]) (by rw [w10]; exact hw16)
    fun s11 g11 l11 m11 r11 w11 => wp_vsh128 fun s12 u12 => wp_movqR fun s13 u13 => ?_
  have hax : s13.gpr .rax =
      BitVec.ofNat 64 (digits 11 ((List.range 16).map fun j => compress 11 (z j)) / 2 ^ 128) := by
    rw [u13.gpr, show s12.xmm .xmm1 = s12.lane .xmm1 0 from rfl, u12.val 0 (by decide), itT rfl, l11, y1]
    exact hT
  refine wp_store32 (a := s.gpr .r8 + BitVec.ofNat 64 16)
    (by rw [ea_at, u13.other _ (by decide), u12.gpr, g11, g10])
    (by rw [u13.wr, u12.wr, w11, w10]; exact hw4) fun s14 g14 l14 m14 r14 w14 => wp_shr32 fun s15 u15 => ?_
  refine wp_store16 (a := s.gpr .r8 + BitVec.ofNat 64 20)
    (by rw [ea_at, u15.other _ (by decide), g14, u13.other _ (by decide), u12.gpr, g11, g10])
    (by rw [u15.wr, w14, u13.wr, u12.wr, w11, w10]; exact hw2) fun s16 g16 l16 m16 r16 w16 =>
      k s16 ?_ (fun r a b c d l hl => ?_) (fun g hg => ?_) ?_ ?_
  · rw [m16, u15.mem, m14, u13.mem, u12.mem, m11, m10, x0, u15.gpr, g14, hax]
  · rw [l16, u15.lane, l14, u13.lane, u12.other r b l hl, l11, u10.other r a l hl, u9.other r c l hl,
      u8.other r b l hl, u7.other r a l hl, u6.other r b l hl, u5.other r a l hl, u4.other r b l hl,
      u3.other r a l hl, cK r a b c d l hl]
  · rw [g16, u15.other g hg, g14, u13.other g hg, u12.gpr, g11, g10]
  · rw [r16, u15.rd, r14, u13.rd, u12.rd, r11, r10]
  · rw [w16, u15.wr, w14, u13.wr, u12.wr, w11, w10]

/-! ## A group of five bits -/

/-- The forty bits of the eight values of five bits from `b`. -/
abbrev v8 (c : Nat → Nat) (b : Nat) : Nat :=
  c b + 2 ^ 5 * c (b + 1) + 2 ^ 10 * (c (b + 2) + 2 ^ 5 * c (b + 3)) +
    2 ^ 20 * (c (b + 4) + 2 ^ 5 * c (b + 5) + 2 ^ 10 * (c (b + 6) + 2 ^ 5 * c (b + 7)))

theorem dig32_5 (c : Nat → Nat) : digits 5 ((List.range 32).map c) =
    v8 c 0 + 2 ^ 40 * v8 c 8 + 2 ^ 80 * v8 c 16 + 2 ^ 120 * v8 c 24 := by
  show digits 5 [c 0, c 1, c 2, c 3, c 4, c 5, c 6, c 7, c 8, c 9, c 10, c 11, c 12, c 13, c 14, c 15, c 16, c 17,
    c 18, c 19, c 20, c 21, c 22, c 23, c 24, c 25, c 26, c 27, c 28, c 29, c 30, c 31] = _
  simp only [digits_cons, digits_nil, v8, Nat.reducePow, Nat.reduceAdd]
  omega_arith

/-- The pairs of the pairs of a half: `vpackssdw` and `vpmaddwd` by `1, 2¹⁰`
of the lanes `A`, `B` of pairs `a`, `b` of values of five bits. -/
theorem dword_pp {A B K : BitVec 128} (hK : ∀ i < 4, word K (2 * i) = 1 ∧ word K (2 * i + 1) = BitVec.ofNat 16 (2 ^ 10))
    {a b : Nat → Nat} (ha : ∀ i < 4, (dword A i).toNat = a i) (hb : ∀ i < 4, (dword B i).toNat = b i)
    (la : ∀ i < 4, a i < 2 ^ 10) (lb : ∀ i < 4, b i < 2 ^ 10) :
    (dword (XBinOp.eval .pmaddwd (XBinOp.eval .packssdw A B) K) 0).toNat = a 0 + 2 ^ 10 * a 1 ∧
    (dword (XBinOp.eval .pmaddwd (XBinOp.eval .packssdw A B) K) 1).toNat = a 2 + 2 ^ 10 * a 3 ∧
    (dword (XBinOp.eval .pmaddwd (XBinOp.eval .packssdw A B) K) 2).toNat = b 0 + 2 ^ 10 * b 1 ∧
    (dword (XBinOp.eval .pmaddwd (XBinOp.eval .packssdw A B) K) 3).toNat = b 2 + 2 ^ 10 * b 3 := by
  have hw : ∀ e < 8, (word (XBinOp.eval .packssdw A B) e).toNat = if e < 4 then a e else b (e - 4) := fun e he => by
    rw [word_packssdw_small _ _ he (fun j hj => by rw [ha j hj]; have := la j hj; omega_arith)
      (fun j hj => by rw [hb j hj]; have := lb j hj; omega_arith)]
    split
    · rw [ha e (by omega_arith)]
    · rw [hb (e - 4) (by omega_arith)]
  have hl : ∀ e < 8, (if e < 4 then a e else b (e - 4)) < 2 ^ 10 := fun e he => by
    split
    · exact la e (by omega_arith)
    · exact lb (e - 4) (by omega_arith)
  have h := fun i (hi : i < 4) => dword_pair (d := 10) (c := fun e => if e < 4 then a e else b (e - 4)) (by decide)
    hK hw hl (i := i) hi
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide); have h3 := h 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte, Nat.reduceSub] at h0 h1 h2 h3
  exact ⟨h0, h1, h2, h3⟩

/-- The quadwords of a lane of `cmPack5` before `vpshufb`: the forty bits of
the eight values of each half. -/
theorem qword_pp {A B K : BitVec 128} (hK : ∀ i < 4, word K (2 * i) = 1 ∧ word K (2 * i + 1) = BitVec.ofNat 16 (2 ^ 10))
    {a b : Nat → Nat} (ha : ∀ i < 4, (dword A i).toNat = a i) (hb : ∀ i < 4, (dword B i).toNat = b i)
    (la : ∀ i < 4, a i < 2 ^ 10) (lb : ∀ i < 4, b i < 2 ^ 10) :
    (qword (q10 (XBinOp.eval .pmaddwd (XBinOp.eval .packssdw A B) K)) 0).toNat =
        a 0 + 2 ^ 10 * a 1 + 2 ^ 20 * (a 2 + 2 ^ 10 * a 3) ∧
      (qword (q10 (XBinOp.eval .pmaddwd (XBinOp.eval .packssdw A B) K)) 1).toNat =
        b 0 + 2 ^ 10 * b 1 + 2 ^ 20 * (b 2 + 2 ^ 10 * b 3) := by
  obtain ⟨p0, p1, p2, p3⟩ := dword_pp hK ha hb la lb
  have a0 := la 0 (by decide); have a1 := la 1 (by decide); have a2 := la 2 (by decide)
  have a3 := la 3 (by decide); have b0 := lb 0 (by decide); have b1 := lb 1 (by decide)
  have b2 := lb 2 (by decide); have b3 := lb 3 (by decide)
  exact qword_q10 (p := fun i => if i = 0 then a 0 + 2 ^ 10 * a 1 else if i = 1 then a 2 + 2 ^ 10 * a 3
      else if i = 2 then b 0 + 2 ^ 10 * b 1 else b 2 + 2 ^ 10 * b 3)
    (fun i hi => by
      rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
      exacts [p0, p1, p2, p3])
    (fun i hi => by
      rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
      · rw [itT rfl]; omega_arith
      · rw [itF (by decide), itT rfl]; omega_arith
      · rw [itF (by decide), itF (by decide), itT rfl]; omega_arith
      · rw [itF (by decide), itF (by decide), itF (by decide)]; omega_arith)

/-- A group of `d = 5`: the 32 coefficients `z` at `rdi`, compressed, and the
twenty bytes of the number whose digits they are stored at `r8`. -/
theorem grp5_ok (hc : C5 s) (hin0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 0) 32)
    (hin1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (0 + 32)) 32)
    (hin2 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 64) 32)
    (hin3 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (64 + 32)) 32) {z : Nat → Zq}
    (hx : ∀ j < 32, (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32).toNat = (z j).val)
    (hw16 : InRegions s.wr (s.gpr .r8) 16) (hw4 : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 16) 4)
    (k : ∀ s', s'.mem = (s.mem.writeW (s.gpr .r8)
          (BitVec.ofNat 128 (digits 5 ((List.range 32).map fun j => compress 5 (z j))))).writeW
        (s.gpr .r8 + BitVec.ofNat 64 16)
          (BitVec.ofNat 32 (digits 5 ((List.range 32).map fun j => compress 5 (z j)) / 2 ^ 128)) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → r ≠ .xmm4 → ∀ l < 2, s'.lane r l = s.lane r l) →
      (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (cmLd 0 ++ (toY cmLo ++ (.vop (.vmovdqa .l256 .xmm4 .xmm0) :: (cmLd 64 ++ (toY cmLo ++
      (cmPack5 ++ is))))))) s Q := by
  refine ld_ok hin0 hin1 (x := fun j => (z j).val)
    (fun j hj => by rw [Nat.zero_add]; exact hx j (by omega_arith)) (fun j _ => val_lt _)
    fun s1 h1 o1 g1 m1 r1 w1 => ?_
  refine lo_ok fun s2 h2 o2 g2 m2 r2 w2 => wp_vmovdqa256 fun s3 u3 => ?_
  have g3 : s3.gpr = s.gpr := by rw [u3.gpr, g2, g1]
  have m3 : s3.mem = s.mem := by rw [u3.mem, m2, m1]
  have r3 : s3.rd = s.rd := by rw [u3.rd, r2, r1]
  have w3 : s3.wr = s.wr := by rw [u3.wr, w2, w1]
  refine ld_ok (o := 64) (by rw [r3, w3, g3]; exact hin2) (by rw [r3, w3, g3]; exact hin3)
    (x := fun j => (z (16 + j)).val)
    (fun j hj => by rw [m3, g3, show 64 + 4 * j = 4 * (16 + j) by omega_arith]; exact hx (16 + j) (by omega_arith))
    (fun j _ => val_lt _) fun s4 h4 o4 g4 m4 r4 w4 => ?_
  refine lo_ok fun s5 h5 o5 g5 m5 r5 w5 => ?_
  simp only [cmPack5, yb, List.cons_append, List.nil_append]
  refine wp_vbin fun s6 u6 => wp_vbin fun s7 u7 => wp_vvar fun s8 u8 => wp_vsh fun s9 u9 => wp_vext1 fun s10 u10 =>
    wp_vbin128 fun s11 u11 => wp_vbin128 fun s12 u12 => wp_vbin128 fun s13 u13 => ?_
  have k2 : ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → ∀ l < 2, s2.lane r l = s.lane r l :=
    fun r a b l hl => by rw [o2 r a l hl, o1 r a b l hl]
  have k4 : ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm4 → ∀ l < 2, s4.lane r l = s.lane r l :=
    fun r a b c l hl => by rw [o4 r a b l hl, u3.other r c l hl, k2 r a b l hl]
  have k5 : ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm4 → ∀ l < 2, s5.lane r l = s.lane r l :=
    fun r a b c l hl => by rw [o5 r a l hl, k4 r a b c l hl]
  have DA : ∀ l < 2, ∀ i < 4, (dword (s2.lane .xmm0 l) i).toNat =
      compress 5 (z (8 * l + 2 * i)) + 2 ^ 5 * compress 5 (z (8 * l + (2 * i + 1))) := fun l hl i hi => by
    rw [h2 l hl, o1 .xmm10 (by decide) (by decide) l hl, o1 .xmm11 (by decide) (by decide) l hl,
      o1 .xmm12 (by decide) (by decide) l hl, o1 .xmm13 (by decide) (by decide) l hl, hc.c10 l hl, hc.c11 l hl,
      hc.c12 l hl, hc.c13 l hl]
    exact dword_loL (d := 5) (sh := 0x400) (mk := 0x1F) (by decide) (by decide) (by decide) (by decide) (by decide)
      (c := fun j => compress 5 (z (8 * l + j))) (fun j hj => loW5 (h1 l hl j hj)) (fun j _ => compress_lt _ _) hi
  have DB : ∀ l < 2, ∀ i < 4, (dword (s5.lane .xmm0 l) i).toNat =
      compress 5 (z (16 + (8 * l + 2 * i))) + 2 ^ 5 * compress 5 (z (16 + (8 * l + (2 * i + 1)))) :=
    fun l hl i hi => by
    rw [h5 l hl, k4 .xmm10 (by decide) (by decide) (by decide) l hl, k4 .xmm11 (by decide) (by decide) (by decide) l hl,
      k4 .xmm12 (by decide) (by decide) (by decide) l hl, k4 .xmm13 (by decide) (by decide) (by decide) l hl,
      hc.c10 l hl, hc.c11 l hl, hc.c12 l hl, hc.c13 l hl]
    exact dword_loL (d := 5) (sh := 0x400) (mk := 0x1F) (by decide) (by decide) (by decide) (by decide) (by decide)
      (c := fun j => compress 5 (z (16 + (8 * l + j)))) (fun j hj => loW5 (h4 l hl j hj))
      (fun j _ => compress_lt _ _) hi
  have ltA : ∀ l < 2, ∀ i < 4, compress 5 (z (8 * l + 2 * i)) + 2 ^ 5 * compress 5 (z (8 * l + (2 * i + 1))) <
      2 ^ 10 := fun l _ i _ => by
    have := compress_lt 5 (z (8 * l + 2 * i)); have := compress_lt 5 (z (8 * l + (2 * i + 1))); omega_arith
  have ltB : ∀ l < 2, ∀ i < 4, compress 5 (z (16 + (8 * l + 2 * i))) +
      2 ^ 5 * compress 5 (z (16 + (8 * l + (2 * i + 1)))) < 2 ^ 10 := fun l _ i _ => by
    have := compress_lt 5 (z (16 + (8 * l + 2 * i))); have := compress_lt 5 (z (16 + (8 * l + (2 * i + 1))))
    omega_arith
  have e7 : ∀ l < 2, s7.lane .xmm0 l = XBinOp.eval .pmaddwd (XBinOp.eval .packssdw (s2.lane .xmm0 l)
      (s5.lane .xmm0 l)) (wc 0x04000001) := fun l hl => by
    rw [u7.val l hl, u6.val l hl, u6.other .xmm8 (by decide) l hl,
      k5 .xmm8 (by decide) (by decide) (by decide) l hl, hc.c8 l hl, o5 .xmm4 (by decide) l hl,
      o4 .xmm4 (by decide) (by decide) l hl, u3.val l hl]
    rfl
  have e9 : ∀ l < 2, s9.lane .xmm0 l = q10 (s7.lane .xmm0 l) := fun l hl => by
    rw [u9.val l hl, u8.val l hl, u7.other .xmm14 (by decide) l hl, u6.other .xmm14 (by decide) l hl,
      k5 .xmm14 (by decide) (by decide) (by decide) l hl, hc.c14 l hl]
  have c := fun (j : Nat) => compress_lt 5 (z j)
  have q0 := qword_pp (K := wc 0x04000001) (by decide) (DA 0 (by decide)) (DB 0 (by decide)) (ltA 0 (by decide))
    (ltB 0 (by decide))
  have q1 := qword_pp (K := wc 0x04000001) (by decide) (DA 1 (by decide)) (DB 1 (by decide)) (ltA 1 (by decide))
    (ltB 1 (by decide))
  rw [← e7 0 (by decide), ← e9 0 (by decide)] at q0
  rw [← e7 1 (by decide), ← e9 1 (by decide)] at q1
  obtain ⟨hR, hT⟩ := pack5 (V := digits 5 ((List.range 32).map fun j => compress 5 (z j))) q0.1 q1.1 q0.2 q1.2
    (by have := c (8 * 0 + 2 * 0); have := c (8 * 0 + (2 * 0 + 1)); have := c (8 * 0 + 2 * 1)
        have := c (8 * 0 + (2 * 1 + 1)); have := c (8 * 0 + 2 * 2); have := c (8 * 0 + (2 * 2 + 1))
        have := c (8 * 0 + 2 * 3); have := c (8 * 0 + (2 * 3 + 1)); omega_arith)
    (by have := c (8 * 1 + 2 * 0); have := c (8 * 1 + (2 * 0 + 1)); have := c (8 * 1 + 2 * 1)
        have := c (8 * 1 + (2 * 1 + 1)); have := c (8 * 1 + 2 * 2); have := c (8 * 1 + (2 * 2 + 1))
        have := c (8 * 1 + 2 * 3); have := c (8 * 1 + (2 * 3 + 1)); omega_arith)
    (by have := c (16 + (8 * 0 + 2 * 0)); have := c (16 + (8 * 0 + (2 * 0 + 1))); have := c (16 + (8 * 0 + 2 * 1))
        have := c (16 + (8 * 0 + (2 * 1 + 1))); have := c (16 + (8 * 0 + 2 * 2))
        have := c (16 + (8 * 0 + (2 * 2 + 1))); have := c (16 + (8 * 0 + 2 * 3))
        have := c (16 + (8 * 0 + (2 * 3 + 1))); omega_arith)
    (by rw [dig32_5])
  have g13 : s13.gpr = s.gpr := by
    rw [u13.gpr, u12.gpr, u11.gpr, u10.gpr, u9.gpr, u8.gpr, u7.gpr, u6.gpr, g5, g4, g3]
  have m13 : s13.mem = s.mem := by
    rw [u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, m5, m4, m3]
  have w13 : s13.wr = s.wr := by rw [u13.wr, u12.wr, u11.wr, u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, w5, w4, w3]
  have r13 : s13.rd = s.rd := by rw [u13.rd, u12.rd, u11.rd, u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, r5, r4, r3]
  have k9 : ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm4 → ∀ l < 2, s9.lane r l = s.lane r l := fun r a b c l hl => by
    rw [u9.other r a l hl, u8.other r a l hl, u7.other r a l hl, u6.other r a l hl, k5 r a b c l hl]
  have y1 : s13.lane .xmm1 0 = s9.lane .xmm0 1 := by
    rw [u13.other .xmm1 (by decide) 0 (by decide), u12.other .xmm1 (by decide) 0 (by decide),
      u11.other .xmm1 (by decide) 0 (by decide), u10.val 0 (by decide), itT rfl]
  have x0 : s13.lane .xmm0 0 = BitVec.ofNat 128 (digits 5 ((List.range 32).map fun j => compress 5 (z j))) := by
    rw [u13.val 0 (by decide), itT rfl, u12.other .xmm0 (by decide) 0 (by decide), u12.val 0 (by decide), itT rfl,
      u11.val 0 (by decide), itT rfl, u11.other .xmm1 (by decide) 0 (by decide),
      u11.other .xmm9 (by decide) 0 (by decide), u10.val 0 (by decide), itT rfl,
      u10.other .xmm0 (by decide) 0 (by decide), u10.other .xmm7 (by decide) 0 (by decide),
      u10.other .xmm9 (by decide) 0 (by decide), k9 .xmm7 (by decide) (by decide) (by decide) 0 (by decide),
      k9 .xmm9 (by decide) (by decide) (by decide) 0 (by decide), hc.c7 0 (by decide), hc.c9 0 (by decide)]
    exact hR
  refine wp_vst128 (a := s.gpr .r8) (by rw [ea_at, add_ofNat_zero, g13]) (by rw [w13]; exact hw16)
    fun s14 g14 l14 m14 r14 w14 => wp_vsh128 fun s15 u15 => wp_movqR fun s16 u16 => ?_
  refine wp_store32 (a := s.gpr .r8 + BitVec.ofNat 64 16)
    (by rw [ea_at, u16.other _ (by decide), u15.gpr, g14, g13])
    (by rw [u16.wr, u15.wr, w14, w13]; exact hw4) fun s17 g17 l17 m17 r17 w17 =>
      k s17 ?_ (fun r a b c d e l hl => ?_) (fun g hg => ?_) ?_ ?_
  · rw [m17, u16.mem, u15.mem, m14, m13, x0, u16.gpr, show s15.xmm .xmm1 = s15.lane .xmm1 0 from rfl,
      u15.val 0 (by decide), itT rfl, l14, y1, setWidth_ext64, hT]
  · rw [l17, u16.lane, u15.other r b l hl, l14, u13.other r a l hl, u12.other r c l hl, u11.other r a l hl,
      u10.other r b l hl, k9 r a b e l hl]
  · rw [g17, u16.other g hg, u15.gpr, g14, g13]
  · rw [r17, u16.rd, u15.rd, r14, r13]
  · rw [w17, u16.wr, u15.wr, w14, w13]

end

/-! ## The loops -/

theorem written2 (m : Mem) (o : Addr) (X : BitVec 16) :
    Written m (m.writeW o X) o 2 fun j => X.extractLsb' (8 * j) 8 := by
  intro x
  simp only [Mem.writeW, Mem.write, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

theorem ext32 (T : Nat) {t : Nat} (ht : t < 4) :
    ((BitVec.ofNat 64 T).setWidth 32).extractLsb' (8 * t) 8 = BitVec.ofNat 8 (T / 2 ^ (8 * t)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  rcases (by omega_arith : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one] <;> omega_arith

theorem ext16 {T : Nat} (hT : T < 2 ^ 64) {t : Nat} (ht : t < 2) :
    ((BitVec.ofNat 64 T >>> 32).setWidth 16).extractLsb' (8 * t) 8 = BitVec.ofNat 8 (T / 2 ^ (8 * (4 + t))) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hT, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  rcases (by omega_arith : t = 0 ∨ t = 1) with rfl | rfl <;>
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reducePow, Nat.pow_zero, Nat.div_one] <;> omega_arith

section
variable {ws : List Nat} {s₀ : State} (hp : (compressEncodeWK ws).pre s₀)
include hp

theorem step11 (hdd : dArg s₀ .rsi = 11) {i : Nat} (hi : i < 16) {s : State} (hI : Inv C11 64 11 22 s₀ i s) :
    WP isa (.block (cmLd 0 ++ toY cmHi ++ cmPack11 ++ ([.alu .add .rdi (.imm 64), .alu .add .r8 (.imm 22)] : List Instr) ++
        ([.alu .sub .rcx (.imm 1)] : List Instr))) s
      fun s' => Inv C11 64 11 22 s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0) := by
  rw [show cmLd 0 ++ toY cmHi ++ cmPack11 ++ [.alu .add .rdi (.imm 64), .alu .add .r8 (.imm 22)] ++
      [.alu .sub .rcx (.imm 1)] = cmLd 0 ++ (toY cmHi ++ (cmPack11 ++
        ([.alu .add .rdi (.imm 64), .alu .add .r8 (.imm 22), .alu .sub .rcx (.imm 1)] : List Instr))) by
    simp only [List.append_assoc, List.cons_append, List.nil_append]]
  refine grp11_ok (z := fun j => (CE.F s₀)[16 * i + j]!) hI.c
    (by rw [hI.rdi, Offset.add_add]; exact inR hp hI.rd hI.wr (by omega_arith))
    (by rw [hI.rdi, Offset.add_add]; exact inR hp hI.rd hI.wr (by omega_arith))
    (fun j hj => by rw [hI.rdi, Offset.add_add, show 64 * i + (0 + 4 * j) = 4 * (16 * i + j) by omega_arith,
      coeffV hp hdd hI.frame (by omega_arith)])
    (by rw [hI.r8]; exact outN hp hdd hI.wr (by omega_arith))
    (by rw [hI.r8, Offset.add_add]; exact outN hp hdd hI.wr (by omega_arith))
    (by rw [hI.r8, Offset.add_add]; exact outN hp hdd hI.wr (by omega_arith))
    fun s1 m1 o1 g1 r1 w1 => ?_
  refine wp_addi' fun s2 u2 => wp_addi' fun s3 u3 => wp_subi' fun s4 u4 hz => WP.block_nil ?_
  have hV := digits_lt (w := 11) (L := (List.range 16).map fun (j : Nat) => compress 11 (CE.F s₀)[16 * i + j]!)
    (fun a ha => by obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha; exact compress_lt _ _)
  rw [List.length_map, List.length_range, show 11 * 16 = 176 from rfl] at hV
  have hV' : digits 11 ((List.range 16).map fun (j : Nat) => compress 11 (CE.F s₀)[16 * i + j]!) / 2 ^ 128 < 2 ^ 64 :=
    Nat.div_lt_of_lt_mul (by omega_arith)
  have hw : Written s.mem s1.mem (CE.oP s₀ + BitVec.ofNat 64 (22 * i)) (16 + 4 + 2) fun j =>
      (compressEncode 11 (CE.F s₀))[22 * i + j]! := by
    rw [m1, hI.r8]
    refine (((written16 _ _ _).append (written4 _ _ _) (by decide)).append (written2 _ _ _) (by decide)).congr
      fun j hj => ?_
    rw [compressEncode_group (c := 16) (b := 22) (by decide) (by decide) _ (by omega_arith) hj]
    by_cases h : j < 16
    · rw [itT (by omega_arith), itT h, byte_ofNat128' _ h]
    · by_cases h' : j < 20
      · obtain ⟨t, rfl⟩ : ∃ t, j = 16 + t := ⟨j - 16, by omega_arith⟩
        rw [itT (by omega_arith), itF h, Nat.add_sub_cancel_left, ext32 _ (by omega_arith), Nat.div_div_eq_div_mul,
          ← Nat.pow_add, show 128 + 8 * t = 8 * (16 + t) by omega_arith]
      · obtain ⟨t, rfl⟩ : ∃ t, j = 20 + t := ⟨j - 20, by omega_arith⟩
        rw [itF (by omega_arith), show 20 + t - (16 + 4) = t by omega_arith, ext16 hV' (by omega_arith),
          Nat.div_div_eq_div_mul, ← Nat.pow_add, show 128 + 8 * (4 + t) = 8 * (20 + t) by omega_arith]
  obtain ⟨hf', hd'⟩ := Written.step (val := fun k => (compressEncode 11 (CE.F s₀))[k]!) hI.frame hI.done hw
    (show 22 * i + (16 + 4 + 2) ≤ 32 * 11 by omega_arith) (by decide)
  have hm4 : s4.mem = s1.mem := by rw [u4.mem, u3.mem, u2.mem]
  refine ⟨⟨?_, ?_, by rw [u4.rd, u3.rd, u2.rd, r1, hI.rd], by rw [u4.wr, u3.wr, u2.wr, w1, hI.wr],
    (((hI.c.pres fun r a b c d _ _ _ l hl => o1 r a b c d l hl).pres (Hi7.of_lane u2.lane)).pres
      (Hi7.of_lane u3.lane)).pres (Hi7.of_lane u4.lane),
    by rw [hm4]; exact hf', fun k hk => by rw [hm4]; exact hd' k (by omega_arith)⟩, ?_, ?_⟩
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, g1 _ (by decide), hI.rdi,
      show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 64 * i + 64 = 64 * (i + 1) by omega_arith]
  · rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), g1 _ (by decide), hI.r8,
      show BitVec.signExtend 64 (22 : BitVec 32) = BitVec.ofNat 64 22 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 22 * i + 22 = 22 * (i + 1) by omega_arith]
  · rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), g1 _ (by decide)]; rfl
  · rw [hz, u3.other _ (by decide), u2.other _ (by decide), g1 _ (by decide)]; rfl

theorem main11 (hdd : dArg s₀ .rsi = 11) :
    WP isa cm11 s₀ fun s' => bytesAt s'.mem (CE.oP s₀) (32 * 11) = compressEncode 11 (CE.F s₀) ∧
      Frame [⟨CE.oP s₀, 32 * 11⟩] s₀.mem s'.mem := by
  unfold cm11 rcxLoop
  rw [show (.mov .r8 (.reg .rdx) :: cm11Consts : List Instr) = .mov .r8 (.reg .rdx) :: (cm11Consts ++ []) by
    rw [List.append_nil]]
  refine WP.seq (wp_movr fun s0 u0 => consts11_ok fun s1 hc1 hg1 hm1 hr1 hw1 => WP.block_nil ?_)
  refine WP.seq (WP.seq (wp_mov32i fun s2 u2 => WP.block_nil ?_))
  refine wp_countdown (cnt := .rcx) (N := 16) (by decide) (by decide) (Inv C11 64 11 22 s₀)
    (fun i hi s hI _ => step11 hp hdd hi hI) (fun s hI => ?_) (s := s2) ⟨?_, ?_, by rw [u2.rd, hr1, u0.rd],
      by rw [u2.wr, hw1, u0.wr], (hc1.pres (Hi7.of_lane u2.lane)), by rw [u2.mem, hm1, u0.mem]; exact Frame.refl _ _,
      fun k hk => absurd hk (by omega_arith)⟩ (by rw [u2.gpr]; rfl)
  · exact wp_vzu fun s3 _ m3 _ _ => WP.block_nil ⟨bytesAt_eq! (compressEncode_length _ _) fun k hk => by
      rw [m3]; exact hI.done k (by omega_arith), by rw [m3]; exact hI.frame⟩
  · rw [u2.other _ (by decide), hg1 _ (by decide), u0.other _ (by decide)]; simp
  · rw [u2.other _ (by decide), hg1 _ (by decide), u0.gpr]; simp

theorem step5 (hdd : dArg s₀ .rsi = 5) {i : Nat} (hi : i < 8) {s : State} (hI : Inv C5 128 5 20 s₀ i s) :
    WP isa (.block (cmLd 0 ++ toY cmLo ++ ([.vop (.vmovdqa .l256 .xmm4 .xmm0)] : List Instr) ++ cmLd 64 ++
        toY cmLo ++ cmPack5 ++ ([.alu .add .rdi (.imm 128), .alu .add .r8 (.imm 20)] : List Instr) ++
        ([.alu .sub .rcx (.imm 1)] : List Instr))) s
      fun s' => Inv C5 128 5 20 s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0) := by
  rw [show cmLd 0 ++ toY cmLo ++ [.vop (.vmovdqa .l256 .xmm4 .xmm0)] ++ cmLd 64 ++ toY cmLo ++ cmPack5 ++
      [.alu .add .rdi (.imm 128), .alu .add .r8 (.imm 20)] ++ [.alu .sub .rcx (.imm 1)] =
      cmLd 0 ++ (toY cmLo ++ (.vop (.vmovdqa .l256 .xmm4 .xmm0) :: (cmLd 64 ++ (toY cmLo ++ (cmPack5 ++
        ([.alu .add .rdi (.imm 128), .alu .add .r8 (.imm 20), .alu .sub .rcx (.imm 1)] : List Instr)))))) by
    simp only [List.append_assoc, List.cons_append, List.nil_append]]
  refine grp5_ok (z := fun j => (CE.F s₀)[32 * i + j]!) hI.c
    (by rw [hI.rdi, Offset.add_add]; exact inR hp hI.rd hI.wr (by omega_arith))
    (by rw [hI.rdi, Offset.add_add]; exact inR hp hI.rd hI.wr (by omega_arith))
    (by rw [hI.rdi, Offset.add_add]; exact inR hp hI.rd hI.wr (by omega_arith))
    (by rw [hI.rdi, Offset.add_add]; exact inR hp hI.rd hI.wr (by omega_arith))
    (fun j hj => by rw [hI.rdi, Offset.add_add, show 128 * i + 4 * j = 4 * (32 * i + j) by omega_arith,
      coeffV hp hdd hI.frame (by omega_arith)])
    (by rw [hI.r8]; exact outN hp hdd hI.wr (by omega_arith))
    (by rw [hI.r8, Offset.add_add]; exact outN hp hdd hI.wr (by omega_arith))
    fun s1 m1 o1 g1 r1 w1 => ?_
  refine wp_addi' fun s2 u2 => wp_addi' fun s3 u3 => wp_subi' fun s4 u4 hz => WP.block_nil ?_
  have hV := digits_lt (w := 5) (L := (List.range 32).map fun (j : Nat) => compress 5 (CE.F s₀)[32 * i + j]!)
    (fun a ha => by obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha; exact compress_lt _ _)
  rw [List.length_map, List.length_range, show 5 * 32 = 160 from rfl] at hV
  have hV' : digits 5 ((List.range 32).map fun (j : Nat) => compress 5 (CE.F s₀)[32 * i + j]!) / 2 ^ 128 < 2 ^ 32 :=
    Nat.div_lt_of_lt_mul (by omega_arith)
  have hw : Written s.mem s1.mem (CE.oP s₀ + BitVec.ofNat 64 (20 * i)) (16 + 4) fun j =>
      (compressEncode 5 (CE.F s₀))[20 * i + j]! := by
    rw [m1, hI.r8]
    refine ((written16 _ _ _).append (written4 _ _ _) (by decide)).congr fun j hj => ?_
    rw [compressEncode_group (c := 32) (b := 20) (by decide) (by decide) _ (by omega_arith) hj]
    by_cases h : j < 16
    · rw [itT h, byte_ofNat128' _ h]
    · obtain ⟨t, rfl⟩ : ∃ t, j = 16 + t := ⟨j - 16, by omega_arith⟩
      rw [itF h, Nat.add_sub_cancel_left, ext8_ofNat hV' t, Nat.div_div_eq_div_mul, ← Nat.pow_add,
        show 128 + 8 * t = 8 * (16 + t) by omega_arith]
  obtain ⟨hf', hd'⟩ := Written.step (val := fun k => (compressEncode 5 (CE.F s₀))[k]!) hI.frame hI.done hw
    (show 20 * i + (16 + 4) ≤ 32 * 5 by omega_arith) (by decide)
  have hm4 : s4.mem = s1.mem := by rw [u4.mem, u3.mem, u2.mem]
  refine ⟨⟨?_, ?_, by rw [u4.rd, u3.rd, u2.rd, r1, hI.rd], by rw [u4.wr, u3.wr, u2.wr, w1, hI.wr],
    (((hI.c.pres fun r a b c d e _ _ l hl => o1 r a b c d e l hl).pres (Hi7.of_lane u2.lane)).pres
      (Hi7.of_lane u3.lane)).pres (Hi7.of_lane u4.lane),
    by rw [hm4]; exact hf', fun k hk => by rw [hm4]; exact hd' k (by omega_arith)⟩, ?_, ?_⟩
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, g1 _ (by decide), hI.rdi,
      show BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 128 * i + 128 = 128 * (i + 1) by omega_arith]
  · rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), g1 _ (by decide), hI.r8,
      show BitVec.signExtend 64 (20 : BitVec 32) = BitVec.ofNat 64 20 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 20 * i + 20 = 20 * (i + 1) by omega_arith]
  · rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), g1 _ (by decide)]; rfl
  · rw [hz, u3.other _ (by decide), u2.other _ (by decide), g1 _ (by decide)]; rfl

theorem main5 (hdd : dArg s₀ .rsi = 5) :
    WP isa cm5 s₀ fun s' => bytesAt s'.mem (CE.oP s₀) (32 * 5) = compressEncode 5 (CE.F s₀) ∧
      Frame [⟨CE.oP s₀, 32 * 5⟩] s₀.mem s'.mem := by
  unfold cm5 rcxLoop
  rw [show (.mov .r8 (.reg .rdx) :: cm5Consts : List Instr) = .mov .r8 (.reg .rdx) :: (cm5Consts ++ []) by
    rw [List.append_nil]]
  refine WP.seq (wp_movr fun s0 u0 => consts5_ok fun s1 hc1 hg1 hm1 hr1 hw1 => WP.block_nil ?_)
  refine WP.seq (WP.seq (wp_mov32i fun s2 u2 => WP.block_nil ?_))
  refine wp_countdown (cnt := .rcx) (N := 8) (by decide) (by decide) (Inv C5 128 5 20 s₀)
    (fun i hi s hI _ => step5 hp hdd hi hI) (fun s hI => ?_) (s := s2) ⟨?_, ?_, by rw [u2.rd, hr1, u0.rd],
      by rw [u2.wr, hw1, u0.wr], (hc1.pres (Hi7.of_lane u2.lane)), by rw [u2.mem, hm1, u0.mem]; exact Frame.refl _ _,
      fun k hk => absurd hk (by omega_arith)⟩ (by rw [u2.gpr]; rfl)
  · exact wp_vzu fun s3 _ m3 _ _ => WP.block_nil ⟨bytesAt_eq! (compressEncode_length _ _) fun k hk => by
      rw [m3]; exact hI.done k (by omega_arith), by rw [m3]; exact hI.frame⟩
  · rw [u2.other _ (by decide), hg1 _ (by decide), u0.other _ (by decide)]; simp
  · rw [u2.other _ (by decide), hg1 _ (by decide), u0.gpr]; simp

end

/-! ## The contracts -/

theorem wp11 {s₀ : State} (hp : (compressEncodeWK [11]).pre s₀) :
    WP isa cm11 s₀ fun s' =>
      bytesAt s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat = compressEncode (dArg s₀ .rsi) (CE.F s₀) ∧
        Frame [⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩] s₀.mem s'.mem := by
  have h11 : dArg s₀ .rsi = 11 := List.mem_singleton.mp hp.2.2.2.2.2.1
  rw [CE.lenEq hp h11, h11]
  exact main11 hp h11

theorem wp5 {s₀ : State} (hp : (compressEncodeWK [5]).pre s₀) :
    WP isa cm5 s₀ fun s' =>
      bytesAt s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat = compressEncode (dArg s₀ .rsi) (CE.F s₀) ∧
        Frame [⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩] s₀.mem s'.mem := by
  have h5 : dArg s₀ .rsi = 5 := List.mem_singleton.mp hp.2.2.2.2.2.1
  rw [CE.lenEq hp h5, h5]
  exact main5 hp h5

theorem correct11 (s : State) (hs : (compressEncodeWK [11]).pre s) :
    ∃ t s', Exec isa cm11 s t s' ∧ abiPreserved s s' ∧ (compressEncodeWK [11]).post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := cm11) [.rax, .rcx, .rdi, .r8] (wp11 hs) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

theorem correct5 (s : State) (hs : (compressEncodeWK [5]).pre s) :
    ∃ t s', Exec isa cm5 s t s' ∧ abiPreserved s s' ∧ (compressEncodeWK [5]).post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := cm5) [.rax, .rcx, .rdi, .r8] (wp5 hs) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

end VG.Proof.MlKem1024.X86_64.CMW

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem1024.X86_64 VG.Proof.MlKem.X86_64

theorem cm11_ct : ConstantTime isa (compressEncodeWK [11]).pre (compressEncodeWK [11]).pub cm11 :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rdx, .rcx, .rsp] [.rsi]) cm_pub (by taint_decide)

theorem cm5_ct : ConstantTime isa (compressEncodeWK [5]).pre (compressEncodeWK [5]).pub cm5 :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rdx, .rcx, .rsp] [.rsi]) cm_pub (by taint_decide)

end VG.Proof.MlKem1024.X86_64
