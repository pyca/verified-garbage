module

public import VerifiedGarbage.Impl.MlKem.X86_64.CompressAvx2
meta import VerifiedGarbage.Impl.MlKem.X86_64.CompressAvx2
public import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
public import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress

/-!
# ML-KEM on x86-64: `Decompress_d ∘ ByteDecode_d` with AVX2, which the K-PKE functions inline

The values of a group are extracted from its bytes in the doublewords of
each lane (`dword_vals`), decompressed by sums of shifts (`dword_ddMul`),
and are the coefficients of the specification by `DD.seg`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.DDY

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.Sha3.X86_64 (WP.cons)
open S4 (LUpd wp_vbin wp_vvar wp_vbcast128 wp_vst256 GUpd wp_addi' itT itF ext_app2 toNat_dword_ofBytes)
open D12Y (wp_vsh wp_subi' wp_vzu wp_mov32i yconst4_ok yconst_ok')

/-! ## The masks of `vpshufb` -/

/-- Lane `l` of a group of `d = 10`: doubleword `j` takes bytes `o + j` and `o + j + 1`. -/
def m10a : BitVec 128 := 0x80800403808003028080020180800100#128
def m10b : BitVec 128 := 0x80800908808008078080070680800605#128
def m10c : BitVec 128 := 0x80800a09808009088080080780800706#128
def m10d : BitVec 128 := 0x80800f0e80800e0d80800d0c80800c0b#128

/-- What the mask `M` selects: the two bytes from `o + j` in doubleword `j`. -/
def Sel (M : BitVec 128) (o : Nat) : Prop :=
  ∀ a : BitVec 128, XBinOp.eval .pshufb a M = ofBytes fun i => if i % 4 < 2 then byte a (o + i / 4 + i % 4) else 0

theorem sel_m10a : Sel m10a 0 := fun a => by simp only [XBinOp.eval, ofBytes]; rfl
theorem sel_m10b : Sel m10b 5 := fun a => by simp only [XBinOp.eval, ofBytes]; rfl
theorem sel_m10c : Sel m10c 6 := fun a => by simp only [XBinOp.eval, ofBytes]; rfl
theorem sel_m10d : Sel m10d 11 := fun a => by simp only [XBinOp.eval, ofBytes]; rfl

/-- The masks of `d = 4`: doubleword `j` of lane `l` of group `k` takes byte `4k + 2l + j / 2`. -/
def m4 (k : Nat) : BitVec 128 := match k with
  | 0 => 0x80808001808080018080800080808000#128
  | 1 => 0x80808005808080058080800480808004#128
  | 2 => 0x80808009808080098080800880808008#128
  | _ => 0x8080800d8080800d8080800c8080800c#128
def m4h (k : Nat) : BitVec 128 := match k with
  | 0 => 0x80808003808080038080800280808002#128
  | 1 => 0x80808007808080078080800680808006#128
  | 2 => 0x8080800b8080800b8080800a8080800a#128
  | _ => 0x8080800f8080800f8080800e8080800e#128

/-- What the mask `M` selects: byte `o + j / 2` in doubleword `j`. -/
def Sel1 (M : BitVec 128) (o : Nat) : Prop :=
  ∀ a : BitVec 128, XBinOp.eval .pshufb a M = ofBytes fun i => if i % 4 = 0 then byte a (o + i / 8) else 0

theorem sel_m4 {k : Nat} (hk : k < 4) : Sel1 (m4 k) (4 * k) ∧ Sel1 (m4h k) (4 * k + 2) := by
  rcases cases4 hk with rfl | rfl | rfl | rfl <;>
    exact ⟨fun a => by simp only [m4, XBinOp.eval, ofBytes]; rfl, fun a => by simp only [m4h, XBinOp.eval, ofBytes]; rfl⟩

/-! ## The values -/

/-- The shifts of `vpsrlvd`, and the masks of the values. -/
def sh10 : BitVec 128 := 0x00000006000000040000000200000000#128
def sh4 : BitVec 128 := 0x00000004000000000000000400000000#128
def mk (d : Nat) : BitVec 128 := let v := BitVec.ofNat 32 (2 ^ d - 1); ofDwords v v v v

/-- The values of lane of the 16 bytes `a`, with the mask `M`, the shifts `sh` and width `d`. -/
abbrev vals (a M sh : BitVec 128) (d : Nat) : BitVec 128 :=
  XBinOp.eval .pand (VVarOp.eval .vpsrlvd (XBinOp.eval .pshufb a M) sh) (mk d)

theorem dword_mk {d : Nat} {j : Nat} (hj : j < 4) : dword (mk d) j = BitVec.ofNat 32 (2 ^ d - 1) := by
  rcases cases4 hj with rfl | rfl | rfl | rfl <;> simp [mk]

theorem toNat_and_mk {d : Nat} (hd : d ≤ 31) (x : BitVec 32) :
    (x &&& BitVec.ofNat 32 (2 ^ d - 1)).toNat = x.toNat % 2 ^ d := by
  have : 2 ^ d ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) hd
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.and_two_pow_sub_one_eq_mod]

theorem dword_vals10 (a : BitVec 128) {M : BitVec 128} {o : Nat} (hM : Sel M o) {j : Nat} (hj : j < 4) :
    (dword (vals a M sh10 10) j).toNat =
      ((byte a (o + j)).toNat + 256 * (byte a (o + j + 1)).toNat) / 2 ^ (2 * j) % 2 ^ 10 := by
  rw [dword_pand, dword_mk hj, toNat_and_mk (by decide), hM]
  rcases cases4 hj with rfl | rfl | rfl | rfl <;>
  simp only [VVarOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
    show (dword sh10 0).toNat = 0 from rfl, show (dword sh10 1).toNat = 2 from rfl,
    show (dword sh10 2).toNat = 4 from rfl, show (dword sh10 3).toNat = 6 from rfl, Nat.reduceLT, ↓reduceIte,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    toNat_dword_ofBytes _ (show 0 < 4 by decide), toNat_dword_ofBytes _ (show 1 < 4 by decide),
    toNat_dword_ofBytes _ (show 2 < 4 by decide), toNat_dword_ofBytes _ (show 3 < 4 by decide),
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.add_zero,
    show (0 : BitVec 8).toNat = 0 from rfl, Nat.mul_zero]

theorem dword_vals4 (a : BitVec 128) {M : BitVec 128} {o : Nat} (hM : Sel1 M o) {j : Nat} (hj : j < 4) :
    (dword (vals a M sh4 4) j).toNat = (byte a (o + j / 2)).toNat / 2 ^ (4 * (j % 2)) % 2 ^ 4 := by
  rw [dword_pand, dword_mk hj, toNat_and_mk (by decide), hM]
  rcases cases4 hj with rfl | rfl | rfl | rfl <;>
  simp only [VVarOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
    show (dword sh4 0).toNat = 0 from rfl, show (dword sh4 1).toNat = 4 from rfl,
    show (dword sh4 2).toNat = 0 from rfl, show (dword sh4 3).toNat = 4 from rfl, Nat.reduceLT, ↓reduceIte,
    Nat.reduceEqDiff,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    toNat_dword_ofBytes _ (show 0 < 4 by decide), toNat_dword_ofBytes _ (show 1 < 4 by decide),
    toNat_dword_ofBytes _ (show 2 < 4 by decide), toNat_dword_ofBytes _ (show 3 < 4 by decide),
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.add_zero,
    show (0 : BitVec 8).toNat = 0 from rfl, Nat.mul_zero]

/-! ## Decompression -/

/-- `(q · y + r) >> d` in each doubleword, by sums of shifts (`ddMul`). -/
abbrev ddM (x R : BitVec 128) (d : Nat) : BitVec 128 :=
  XShiftOp.eval .psrld (XBinOp.eval .paddd (XBinOp.eval .paddd (XBinOp.eval .paddd (XShiftOp.eval .pslld x 8) x)
    (XBinOp.eval .psubd (XShiftOp.eval .pslld x 12) (XShiftOp.eval .pslld x 10))) R) (BitVec.ofNat 8 d)

theorem dword_ddM (x R : BitVec 128) {d : Nat} (hd : d ≤ 10) {j : Nat} (hj : j < 4)
    (hy : (dword x j).toNat < 2 ^ 10) (hr : (dword R j).toNat < 2 ^ 10) :
    (dword (ddM x R d) j).toNat = (3329 * (dword x j).toNat + (dword R j).toNat) / 2 ^ d := by
  have h8 : BitVec.toNat (8 : BitVec 8) = 8 := rfl
  have h10 : BitVec.toNat (10 : BitVec 8) = 10 := rfl
  have h12 : BitVec.toNat (12 : BitVec 8) = 12 := rfl
  have hdn : (BitVec.ofNat 8 d).toNat = d := by rw [BitVec.toNat_ofNat]; omega
  rw [dword_psrld _ _ (by omega) hj, hdn, dword_paddd _ _ hj, dword_paddd _ _ hj, dword_paddd _ _ hj,
    dword_psubd _ _ hj, dword_pslld _ _ (by decide) hj, dword_pslld _ _ (by decide) hj,
    dword_pslld _ _ (by decide) hj, h8, h10, h12]
  generalize dword x j = y at hy ⊢
  generalize dword R j = r at hr ⊢
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  congr 1
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- Each doubleword of `rc v` is `v`. -/
def rc (v : Nat) : BitVec 128 := let w := BitVec.ofNat 32 v; ofDwords w w w w

theorem dword_rc {v j : Nat} (hj : j < 4) : dword (rc v) j = BitVec.ofNat 32 v := by
  rcases cases4 hj with rfl | rfl | rfl | rfl <;> simp [rc]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem ddMul_ok {o x t₁ t₂ rr : XReg} {d : Nat} (h1 : o ≠ x) (h2 : t₁ ≠ x) (h4 : t₁ ≠ t₂)
    (h5 : o ≠ t₁) (h6 : o ≠ t₂) (h7 : rr ≠ o) (h8 : rr ≠ t₁) (h9 : rr ≠ t₂)
    (k : ∀ s', (∀ l < 2, s'.lane o l = ddM (s.lane x l) (s.lane rr l) d) →
      (∀ r, r ≠ o → r ≠ t₁ → r ≠ t₂ → ∀ l < 2, s'.lane r l = s.lane r l) →
      s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (ddMul o x t₁ t₂ rr d ++ is)) s Q := by
  simp only [ddMul, ysl, ysr, yb, List.cons_append, List.nil_append]
  refine wp_vsh fun s1 u1 => wp_vbin fun s2 u2 => wp_vsh fun s3 u3 => wp_vsh fun s4 u4 => wp_vbin fun s5 u5 =>
    wp_vbin fun s6 u6 => wp_vbin fun s7 u7 => wp_vsh fun s8 u8 =>
      k s8 (fun l hl => ?_) (fun r a b c l hl => ?_) ?_ ?_ ?_ ?_
  · have x1 : s1.lane x l = s.lane x l := u1.other x (Ne.symm h1) l hl
    have x2 : s2.lane x l = s.lane x l := by rw [u2.other x (Ne.symm h1) l hl, x1]
    have x3 : s3.lane x l = s.lane x l := by rw [u3.other x (Ne.symm h2) l hl, x2]
    have a2 : s2.lane o l = XBinOp.eval .paddd (XShiftOp.eval .pslld (s.lane x l) (BitVec.ofNat 8 8))
        (s.lane x l) := by rw [u2.val l hl, u1.val l hl, x1]; rfl
    have a4 : s4.lane o l = s2.lane o l := by rw [u4.other o h6 l hl, u3.other o h5 l hl]
    have t5 : s5.lane t₁ l = XBinOp.eval .psubd (XShiftOp.eval .pslld (s.lane x l) (BitVec.ofNat 8 12))
        (XShiftOp.eval .pslld (s.lane x l) (BitVec.ofNat 8 10)) := by
      rw [u5.val l hl, u4.other t₁ h4 l hl, u4.val l hl, u3.val l hl, x2, x3]; rfl
    have r6 : s6.lane rr l = s.lane rr l := by
      rw [u6.other rr h7 l hl, u5.other rr h8 l hl, u4.other rr h9 l hl, u3.other rr h8 l hl,
        u2.other rr h7 l hl, u1.other rr h7 l hl]
    rw [u8.val l hl, u7.val l hl, r6, u6.val l hl, u5.other o h5 l hl, a4, a2, t5]; rfl
  · rw [u8.other r a l hl, u7.other r a l hl, u6.other r a l hl, u5.other r b l hl, u4.other r c l hl,
      u3.other r b l hl, u2.other r a l hl, u1.other r a l hl]
  · rw [u8.gpr, u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  · rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]

end

/-! ## The constants -/

/-- The vector registers from `ymm5` on are those of `s`. -/
def Hi (s s' : State) : Prop :=
  ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → r ≠ .xmm4 → ∀ l < 2, s'.lane r l = s.lane r l

theorem Hi.trans {s₁ s₂ s₃ : State} (h₁ : Hi s₁ s₂) (h₂ : Hi s₂ s₃) : Hi s₁ s₃ :=
  fun r a b c d e l hl => by rw [h₂ r a b c d e l hl, h₁ r a b c d e l hl]

theorem Hi.of_lane {s s' : State} (h : ∀ x l, s'.lane x l = s.lane x l) : Hi s s' := fun r _ _ _ _ _ l _ => h r l

/-- The constants of `d = 10`. -/
structure C10 (s : State) : Prop where
  c8 : ∀ l < 2, s.lane .xmm8 l = if l = 0 then m10a else m10b
  c12 : ∀ l < 2, s.lane .xmm12 l = if l = 0 then m10c else m10d
  c9 : ∀ l < 2, s.lane .xmm9 l = sh10
  c10 : ∀ l < 2, s.lane .xmm10 l = mk 10
  c11 : ∀ l < 2, s.lane .xmm11 l = rc 512

theorem C10.pres {s s' : State} (h : C10 s) (hk : Hi s s') : C10 s' :=
  ⟨fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c8 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c12 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c9 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c10 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c11 l hl]⟩

/-- The constants of `d = 4`. -/
structure C4 (s : State) : Prop where
  c8 : ∀ l < 2, s.lane .xmm8 l = if l = 0 then m4 0 else m4h 0
  c9 : ∀ l < 2, s.lane .xmm9 l = if l = 0 then m4 1 else m4h 1
  c10 : ∀ l < 2, s.lane .xmm10 l = if l = 0 then m4 2 else m4h 2
  c11 : ∀ l < 2, s.lane .xmm11 l = if l = 0 then m4 3 else m4h 3
  c12 : ∀ l < 2, s.lane .xmm12 l = sh4
  c13 : ∀ l < 2, s.lane .xmm13 l = mk 4
  c14 : ∀ l < 2, s.lane .xmm14 l = rc 8

theorem C4.pres {s s' : State} (h : C4 s) (hk : Hi s s') : C4 s' :=
  ⟨fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c8 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c9 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c10 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c11 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c12 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c13 l hl],
    fun l hl => by rw [hk _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl, h.c14 l hl]⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- The lanes of `yconst4`, by lane. -/
theorem lane4 {s : State} {r : XReg} {q₀ q₁ q₂ q₃ : BitVec 64} {A B : BitVec 128}
    (h0 : s.lane r 0 = (q₁ ++ q₀ : BitVec 128)) (h1 : s.lane r 1 = (q₃ ++ q₂ : BitVec 128))
    (hA : (q₁ ++ q₀ : BitVec 128) = A) (hB : (q₃ ++ q₂ : BitVec 128) = B) :
    ∀ l < 2, s.lane r l = if l = 0 then A else B := fun l hl => by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · rw [h0, hA]; rfl
  · rw [h1, hB]; rfl

theorem consts10_ok
    (k : ∀ s', C10 s' → (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (dd10Consts ++ is)) s Q := by
  simp only [dd10Consts, List.append_assoc]
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
    exact (lane4 a3 b3 rfl rfl l hl).trans (by split <;> rfl)
  · rw [o5 _ (by decide) l hl, a4 l hl]; rfl
  · rw [a5 l hl]; rfl
  · rw [g5 g hg, g4 g hg, g3 g hg, g2 g hg, g1 g hg]
  · rw [m5, m4, m3, m2, m1]
  · rw [r5, r4, r3, r2, r1]
  · rw [w5, w4, w3, w2, w1]

theorem consts4_ok
    (k : ∀ s', C4 s' → (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (dd4Consts ++ is)) s Q := by
  simp only [dd4Consts, List.append_assoc]
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
    exact (lane4 a5 b5 rfl rfl l hl).trans (by split <;> rfl)
  · rw [o7 _ (by decide) l hl, a6 l hl]; rfl
  · rw [a7 l hl]; rfl
  · rw [g7 g hg, g6 g hg, g5 g hg, g4 g hg, g3 g hg, g2 g hg, g1 g hg]
  · rw [m7, m6, m5, m4, m3, m2, m1]
  · rw [r7, r6, r5, r4, r3, r2, r1]
  · rw [w7, w6, w5, w4, w3, w2, w1]

end

/-! ## A group -/

/-- The vector registers but `ymm1` to `ymm4` are those of `s`. -/
def Kp (s s' : State) : Prop :=
  ∀ r, r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → r ≠ .xmm4 → ∀ l < 2, s'.lane r l = s.lane r l

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- A group of `d = 10`: the eight values of the 16 bytes at `rdi` that the masks `M` select, decompressed,
stored to `rsi`. -/
theorem body10_ok {m : XReg} {M : Nat → BitVec 128} (hm : ∀ l < 2, s.lane m l = M l) (hm0 : m ≠ .xmm0)
    (hc : C10 s) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 16) (hout : InRegions s.wr (s.gpr .rsi) 32)
    (k : ∀ s', Hi s s' → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∃ V : BitVec 256, s'.mem = s.mem.writeW (s.gpr .rsi) V ∧ ∀ i < 8, V.extractLsb' (32 * i) 32 =
        dword (ddM (vals (s.mem.readW (s.gpr .rdi) 128) (M (i / 4)) sh10 10) (rc 512) 10) (i % 4)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (dd10Grp m ++ is)) s Q := by
  simp only [dd10Grp, yb, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_vbcast128 (a := s.gpr .rdi) (by rw [ea_at, add_ofNat_zero]) hin fun s1 u1 => ?_
  refine wp_vbin fun s2 u2 => wp_vvar fun s3 u3 => wp_vbin fun s4 u4 => ddMul_ok (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) fun s5 v5 o5 g5 m5 r5 w5 => ?_
  have hg : s5.gpr = s.gpr := by rw [g5, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  refine wp_vst256 (a := s.gpr .rsi) (by rw [ea_at, add_ofNat_zero, hg])
    (by rw [w5, u4.wr, u3.wr, u2.wr, u1.wr]; exact hout) fun s6 g6 l6 m6 r6 w6 => ?_
  generalize hL : s.mem.readW (s.gpr .rdi) 128 = L at u1
  have h4 : ∀ l < 2, s4.lane .xmm0 l = vals L (M l) sh10 10 := fun l hl => by
    rw [u4.val l hl, u3.other .xmm10 (by decide) l hl, u3.val l hl, u2.other .xmm9 (by decide) l hl,
      u2.other .xmm10 (by decide) l hl, u2.val l hl, u1.other .xmm9 (by decide) l hl,
      u1.other .xmm10 (by decide) l hl, u1.other m hm0 l hl, u1.val l hl, hm l hl, hc.c9 l hl, hc.c10 l hl]; rfl
  have r4 : ∀ l < 2, s4.lane .xmm11 l = rc 512 := fun l hl => by
    rw [u4.other _ (by decide) l hl, u3.other _ (by decide) l hl, u2.other _ (by decide) l hl,
      u1.other _ (by decide) l hl, hc.c11 l hl]
  refine k s6 (fun r a b c d _ l hl => ?_) (by rw [g6, hg]) (by rw [r6, r5, u4.rd, u3.rd, u2.rd, u1.rd])
    (by rw [w6, w5, u4.wr, u3.wr, u2.wr, u1.wr]) ⟨s5.ymm .xmm1, by rw [m6, m5, u4.mem, u3.mem, u2.mem, u1.mem],
      fun i hi => ?_⟩
  · rw [l6, o5 r b c d l hl, u4.other r a l hl, u3.other r a l hl, u2.other r a l hl, u1.other r a l hl]
  · rw [State.ymm_eq, ext_app2 _ _ hi, hL]
    by_cases h : i < 4
    · rw [itT h, v5 0 (by decide), h4 0 (by decide), r4 0 (by decide), show i / 4 = 0 by omega]
    · rw [itF h, v5 1 (by decide), h4 1 (by decide), r4 1 (by decide), show i / 4 = 1 by omega]

/-- A group of `d = 4`: the eight values of the bytes of `ymm0` that the masks `M` select, decompressed,
stored to `rsi + 32 k`. -/
theorem body4_ok {m : XReg} {k : Nat} {M : Nat → BitVec 128} {L : BitVec 128}
    (hm : ∀ l < 2, s.lane m l = M l) (h0 : ∀ l < 2, s.lane .xmm0 l = L) (hc : C4 s)
    (hout : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (32 * k)) 32)
    (k' : ∀ s', Kp s s' → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∃ V : BitVec 256, s'.mem = s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (32 * k)) V ∧ ∀ i < 8,
        V.extractLsb' (32 * i) 32 = dword (ddM (vals L (M (i / 4)) sh4 4) (rc 8) 4) (i % 4)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (dd4Grp m k ++ is)) s Q := by
  simp only [dd4Grp, yb, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_vbin fun s1 u1 => wp_vvar fun s2 u2 => wp_vbin fun s3 u3 => ddMul_ok (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) fun s4 v4 o4 g4 m4 r4 w4 => ?_
  have hg : s4.gpr = s.gpr := by rw [g4, u3.gpr, u2.gpr, u1.gpr]
  refine wp_vst256 (a := s.gpr .rsi + BitVec.ofNat 64 (32 * k)) (by rw [ea_at, hg])
    (by rw [w4, u3.wr, u2.wr, u1.wr]; exact hout) fun s5 g5 l5 m5 r5 w5 => ?_
  have h3 : ∀ l < 2, s3.lane .xmm1 l = vals L (M l) sh4 4 := fun l hl => by
    rw [u3.val l hl, u2.other .xmm13 (by decide) l hl, u2.val l hl, u1.other .xmm12 (by decide) l hl,
      u1.other .xmm13 (by decide) l hl, u1.val l hl, h0 l hl, hm l hl, hc.c12 l hl, hc.c13 l hl]; rfl
  have r3 : ∀ l < 2, s3.lane .xmm14 l = rc 8 := fun l hl => by
    rw [u3.other _ (by decide) l hl, u2.other _ (by decide) l hl, u1.other _ (by decide) l hl, hc.c14 l hl]
  refine k' s5 (fun r a b c d l hl => ?_) (by rw [g5, hg]) (by rw [r5, r4, u3.rd, u2.rd, u1.rd])
    (by rw [w5, w4, u3.wr, u2.wr, u1.wr]) ⟨s4.ymm .xmm2, by rw [m5, m4, u3.mem, u2.mem, u1.mem], fun i hi => ?_⟩
  · rw [l5, o4 r b c d l hl, u3.other r a l hl, u2.other r a l hl, u1.other r a l hl]
  · rw [State.ymm_eq, ext_app2 _ _ hi]
    by_cases h : i < 4
    · rw [itT h, v4 0 (by decide), h3 0 (by decide), r3 0 (by decide), show i / 4 = 0 by omega]
    · rw [itF h, v4 1 (by decide), h3 1 (by decide), r3 1 (by decide), show i / 4 = 1 by omega]

end

/-! ## The values of a group -/

theorem dig2 (f : Nat → Nat) : digits 8 ((List.range 2).map f) = f 0 + 256 * f 1 := by
  simp [List.range_succ, digits_cons, digits_nil]

theorem dig1 (f : Nat → Nat) : digits 8 ((List.range 1).map f) = f 0 := by
  simp [List.range_succ, digits_cons, digits_nil]

/-- Value `j` of lane `l` of group `g` (`d = 10`), of the bytes `L` that hold the group's from `ob`. -/
theorem val10 {B : List Byte} (hB : B.length = 320) {g : Nat} (hg : g < 32) {L : BitVec 128} {ob : Nat}
    (hL : ∀ t < 10, byte L (ob + t) = B.getD (10 * g + t) 0) {M : BitVec 128} {l : Nat} (hl : l < 2)
    (hM : Sel M (ob + 5 * l)) {j : Nat} (hj : j < 4) :
    (dword (ddM (vals L M sh10 10) (rc 512) 10) j).toNat = ((decodeDecompress 10 B)[8 * g + (4 * l + j)]!).val := by
  have hv := dword_vals10 L hM hj
  rw [dword_ddM _ _ (by decide) hj (by rw [hv]; exact Nat.mod_lt _ (by decide)) (by rw [dword_rc hj]; decide), hv,
    dword_rc hj, show ob + 5 * l + j = ob + (5 * l + j) by omega,
    show ob + (5 * l + j) + 1 = ob + (5 * l + j + 1) by omega, hL _ (by omega), hL _ (by omega),
    ← DD.seg (d := 10) (c := 8) (b := 10) (o := 5 * l + j) (l := 2) (s := 0) (p := 2 * j) (by decide) (by decide)
      (by decide) B (by omega) (by omega) (by omega) (by omega), dig2]
  simp only [Nat.add_zero, Nat.pow_zero, Nat.div_one, Nat.reduceSub, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.reduceMod]

/-- Value `j` of lane `l` of group `k` of iteration `i` (`d = 4`), of the 16 bytes `L` of the iteration. -/
theorem val4 {B : List Byte} (hB : B.length = 128) {i : Nat} (hi : i < 8) {L : BitVec 128}
    (hL : ∀ t < 16, byte L t = B.getD (16 * i + t) 0) {k : Nat} (hk : k < 4) {M : BitVec 128} {l : Nat}
    (hl : l < 2) (hM : Sel1 M (4 * k + 2 * l)) {j : Nat} (hj : j < 4) :
    (dword (ddM (vals L M sh4 4) (rc 8) 4) j).toNat =
      ((decodeDecompress 4 B)[32 * i + (8 * k + 4 * l + j)]!).val := by
  have hv := dword_vals4 L hM hj
  rw [dword_ddM _ _ (by decide) hj (by rw [hv]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
      (by rw [dword_rc hj]; decide), hv, dword_rc hj, hL _ (by omega),
    ← DD.seg (d := 4) (c := 32) (b := 16) (o := 4 * k + 2 * l + j / 2) (l := 1) (s := 0) (p := 4 * (j % 2))
      (by decide) (by decide) (by decide) B (by omega) (by omega) (by omega) (by omega), dig1]
  simp only [Nat.add_zero, Nat.pow_zero, Nat.div_one, Nat.reduceSub, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.reduceMod]

/-! ## The loops -/

theorem hM10 : ∀ l < 2, Sel (if l = 0 then m10a else m10b) (0 + 5 * l) := fun l hl => by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  exacts [sel_m10a, sel_m10b]

theorem hM10' : ∀ l < 2, Sel (if l = 0 then m10c else m10d) (6 + 5 * l) := fun l hl => by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  exacts [sel_m10c, sel_m10d]

theorem hM4 {k : Nat} (hk : k < 4) : ∀ l < 2, Sel1 (if l = 0 then m4 k else m4h k) (4 * k + 2 * l) := fun l hl => by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  exacts [(sel_m4 hk).1, (sel_m4 hk).2]

/-- After `i` groups of `d = 10`. -/
structure Inv10 (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = DD.bP s₀ + BitVec.ofNat 64 (10 * i)
  rsi : s.gpr .rsi = coeffAddr (DD.fP s₀) (8 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : C10 s
  frame : Frame [pR (DD.fP s₀)] s₀.mem s.mem
  done : ∀ k < 8 * i, (coeffAt s.mem (DD.fP s₀) k).toNat = ((decodeDecompress 10 (DD.B s₀ 10))[k]!).val

/-- After `i` iterations of `d = 4`. -/
structure Inv4 (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = DD.bP s₀ + BitVec.ofNat 64 (16 * i)
  rsi : s.gpr .rsi = coeffAddr (DD.fP s₀) (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : C4 s
  frame : Frame [pR (DD.fP s₀)] s₀.mem s.mem
  done : ∀ k < 32 * i, (coeffAt s.mem (DD.fP s₀) k).toNat = ((decodeDecompress 4 (DD.B s₀ 4))[k]!).val

section
variable {s₀ : State} (hp : decodeDecompressK.pre s₀)
include hp

theorem regs {d : Nat} (hdd : dArg s₀ .rdx = d) : s₀.rd ++ s₀.wr = [⟨DD.bP s₀, 32 * d⟩, pR (DD.fP s₀)] := by
  rw [hp.1, hp.2.1, DD.lenEq hp hdd]; rfl

/-- Group `g` of `d = 10`, from the 16 bytes at `bP + ob'`, the group's from `ob`. -/
theorem group10 (hdd : dArg s₀ .rdx = 10) {g ob' ob : Nat} (hg : g < 32) (hob : ob' + ob = 10 * g)
    (ho : ob' + 16 ≤ 320) (ho' : ob + 10 ≤ 16) {m : XReg} {M : Nat → BitVec 128} {is : List Instr} {s : State} {Q : State → Prop}
    (hm : ∀ l < 2, s.lane m l = M l) (hm0 : m ≠ .xmm0) (hM : ∀ l < 2, Sel (M l) (ob + 5 * l))
    (hdi : s.gpr .rdi = DD.bP s₀ + BitVec.ofNat 64 ob') (hsi : s.gpr .rsi = coeffAddr (DD.fP s₀) (8 * g))
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hc : C10 s) (hf : Frame [pR (DD.fP s₀)] s₀.mem s.mem)
    (hd : ∀ k < 8 * g, (coeffAt s.mem (DD.fP s₀) k).toNat = ((decodeDecompress 10 (DD.B s₀ 10))[k]!).val)
    (k : ∀ s', C10 s' → s'.gpr = s.gpr → s'.rd = s₀.rd → s'.wr = s₀.wr → Frame [pR (DD.fP s₀)] s₀.mem s'.mem →
      (∀ k < 8 * (g + 1), (coeffAt s'.mem (DD.fP s₀) k).toNat = ((decodeDecompress 10 (DD.B s₀ 10))[k]!).val) →
      WP isa (.block is) s' Q) :
    WP isa (.block (dd10Grp m ++ is)) s Q := by
  have hrw : s.rd ++ s.wr = [⟨DD.bP s₀, 32 * 10⟩, pR (DD.fP s₀)] := by rw [hrd, hwr, regs hp hdd]
  refine body10_ok hm hm0 hc (by rw [hrw, hdi]; exact ⟨_, by simp, Offset.contains_base _ ho (by omega)⟩)
    (by rw [hwr, hp.2.1, hsi]; exact ⟨_, List.mem_singleton_self _,
      Offset.contains_base _ (show 4 * (8 * g) + 32 ≤ 1024 by omega) (by omega)⟩)
    fun s' hk' hg' hrd' hwr' ⟨V, hmem, hV⟩ => k s' (hc.pres hk') hg' (by rw [hrd', hrd]) (by rw [hwr', hwr]) ?_ ?_
  · rw [hmem, hsi]
    exact hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (show 4 * (8 * g) + 256 / 8 ≤ 1024 by omega) (by omega))
  · intro c hcl
    have hL : ∀ t < 10, byte (s.mem.readW (s.gpr .rdi) 128) (ob + t) = (DD.B s₀ 10).getD (10 * g + t) 0 :=
      fun t ht => by
        rw [byte, byte_readW _ _ (by omega), hdi, Offset.add_add, DD.byte hp (by decide) hdd hf (by omega),
          show ob' + (ob + t) = 10 * g + t by omega]
    rw [hmem, hsi, D12Y.coeffAt_write8 _ _ _ hg (by omega)]
    split
    · rename_i hin
      rw [hV _ (by omega), val10 (bytesAt_length _ _ _) hg hL (show (c - 8 * g) / 4 < 2 by omega)
        (hM _ (by omega)) (by omega), show 8 * g + (4 * ((c - 8 * g) / 4) + (c - 8 * g) % 4) = c by omega]
    · exact hd c (by omega)

/-- Group `k` of iteration `i` of `d = 4`, of the 16 bytes `L` in `ymm0`. -/
theorem group4 {i k : Nat} (hi : i < 8) (hk : k < 4) {m : XReg} {M : Nat → BitVec 128}
    {L : BitVec 128} {is : List Instr} {s : State} {Q : State → Prop}
    (hm : ∀ l < 2, s.lane m l = M l) (hM : ∀ l < 2, Sel1 (M l) (4 * k + 2 * l)) (h0 : ∀ l < 2, s.lane .xmm0 l = L)
    (hL : ∀ t < 16, byte L t = (DD.B s₀ 4).getD (16 * i + t) 0)
    (hsi : s.gpr .rsi = coeffAddr (DD.fP s₀) (32 * i)) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hc : C4 s)
    (hf : Frame [pR (DD.fP s₀)] s₀.mem s.mem)
    (hd : ∀ c < 32 * i + 8 * k, (coeffAt s.mem (DD.fP s₀) c).toNat = ((decodeDecompress 4 (DD.B s₀ 4))[c]!).val)
    (k' : ∀ s', C4 s' → (∀ l < 2, s'.lane .xmm0 l = L) → s'.gpr = s.gpr → s'.rd = s₀.rd → s'.wr = s₀.wr →
      Frame [pR (DD.fP s₀)] s₀.mem s'.mem →
      (∀ c < 32 * i + 8 * (k + 1), (coeffAt s'.mem (DD.fP s₀) c).toNat =
        ((decodeDecompress 4 (DD.B s₀ 4))[c]!).val) →
      WP isa (.block is) s' Q) :
    WP isa (.block (dd4Grp m k ++ is)) s Q := by
  have ha : s.gpr .rsi + BitVec.ofNat 64 (32 * k) = coeffAddr (DD.fP s₀) (8 * (4 * i + k)) := by
    rw [hsi, coeffAddr, coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 4 * (32 * i) + 32 * k = 4 * (8 * (4 * i + k)) by omega]
  refine body4_ok hm h0 hc (by rw [hwr, hp.2.1, ha]; exact ⟨_, List.mem_singleton_self _,
      Offset.contains_base _ (show 4 * (8 * (4 * i + k)) + 32 ≤ 1024 by omega) (by omega)⟩)
    fun s' hk' hg' hrd' hwr' ⟨V, hmem, hV⟩ => k' s' (hc.pres fun r _ a b c d l hl => hk' r a b c d l hl)
      (fun l hl => by rw [hk' _ (by decide) (by decide) (by decide) (by decide) l hl, h0 l hl]) hg'
      (by rw [hrd', hrd]) (by rw [hwr', hwr]) ?_ ?_
  · rw [hmem, ha]
    exact hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (show 4 * (8 * (4 * i + k)) + 256 / 8 ≤ 1024 by omega) (by omega))
  · intro c hcl
    rw [hmem, ha, D12Y.coeffAt_write8 _ _ _ (show 4 * i + k < 32 by omega) (by omega)]
    split
    · rename_i hin
      rw [hV _ (by omega), val4 (bytesAt_length _ _ _) hi hL hk (show (c - 8 * (4 * i + k)) / 4 < 2 by omega)
        (hM _ (by omega)) (by omega),
        show 32 * i + (8 * k + 4 * ((c - 8 * (4 * i + k)) / 4) + (c - 8 * (4 * i + k)) % 4) = c by omega]
    · exact hd c (by omega)

theorem step10 (hdd : dArg s₀ .rdx = 10) {i : Nat} (hi : i < 31) {s : State} (hI : Inv10 s₀ i s) :
    WP isa (.block (dd10Grp .xmm8 ++
        ([.alu .add .rdi (.imm 10), .alu .add .rsi (.imm 32), .alu .sub .rcx (.imm 1)] : List Instr)))
      s fun s' => Inv10 s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  refine group10 hp hdd (g := i) (ob' := 10 * i) (ob := 0) (by omega) (by omega) (by omega) (by decide) hI.c.c8 (by decide)
    hM10 hI.rdi hI.rsi hI.rd hI.wr hI.c hI.frame hI.done fun s1 hc1 hg1 hrd1 hwr1 hf1 hd1 => ?_
  refine wp_addi' fun s2 u2 => wp_addi' fun s3 u3 => wp_subi' fun s4 u4 hz => WP.block_nil ?_
  have c4 := ((hc1.pres (Hi.of_lane u2.lane)).pres (Hi.of_lane u3.lane)).pres (Hi.of_lane u4.lane)
  refine ⟨⟨?_, ?_, by rw [u4.rd, u3.rd, u2.rd, hrd1], by rw [u4.wr, u3.wr, u2.wr, hwr1], c4,
    by rw [u4.mem, u3.mem, u2.mem]; exact hf1, fun k hk => by rw [u4.mem, u3.mem, u2.mem]; exact hd1 k hk⟩, ?_, ?_⟩
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, hg1, hI.rdi,
      show BitVec.signExtend 64 (10 : BitVec 32) = BitVec.ofNat 64 10 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 10 * i + 10 = 10 * (i + 1) by omega]
  · rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), hg1, hI.rsi, coeffAddr, coeffAddr,
      show BitVec.signExtend 64 (32 : BitVec 32) = BitVec.ofNat 64 32 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 4 * (8 * i) + 32 = 4 * (8 * (i + 1)) by omega]
  · rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), hg1]; rfl
  · rw [hz, u3.other _ (by decide), u2.other _ (by decide), hg1]; rfl

theorem step4 (hdd : dArg s₀ .rdx = 4) {i : Nat} (hi : i < 8) {s : State} (hI : Inv4 s₀ i s) :
    WP isa (.block (.vbroadcasti128 .xmm0 (at_ .rdi 0) :: dd4Grp .xmm8 0 ++ dd4Grp .xmm9 1 ++
        dd4Grp .xmm10 2 ++ dd4Grp .xmm11 3 ++
        ([.alu .add .rdi (.imm 16), .alu .add .rsi (.imm 128), .alu .sub .rcx (.imm 1)] : List Instr))) s
      fun s' => Inv4 s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  simp only [List.cons_append, List.append_assoc]
  have hrw : s.rd ++ s.wr = [⟨DD.bP s₀, 32 * 4⟩, pR (DD.fP s₀)] := by rw [hI.rd, hI.wr, regs hp hdd]
  refine wp_vbcast128 (a := s.gpr .rdi) (by rw [ea_at, add_ofNat_zero]) (by
    rw [hrw, hI.rdi]; exact ⟨_, by simp, Offset.contains_base _ (show 16 * i + 16 ≤ 32 * 4 by omega) (by omega)⟩)
    fun s1 u1 => ?_
  have hL : ∀ t < 16, byte (s.mem.readW (s.gpr .rdi) 128) t = (DD.B s₀ 4).getD (16 * i + t) 0 := fun t ht => by
    rw [byte, byte_readW _ _ (by omega), hI.rdi, Offset.add_add, DD.byte hp (by decide) hdd hI.frame (by omega)]
  have c1 := hI.c.pres fun r a _ _ _ _ l hl => u1.other r a l hl
  refine group4 hp hi (show 0 < 4 by decide) c1.c8 (hM4 (by decide)) u1.val hL (by rw [u1.gpr, hI.rsi])
    (by rw [u1.rd, hI.rd]) (by rw [u1.wr, hI.wr]) c1 (by rw [u1.mem]; exact hI.frame)
    (fun c hc => by rw [u1.mem]; exact hI.done c (by omega)) fun s2 c2 x2 g2 r2 w2 f2 d2 => ?_
  refine group4 hp hi (show 1 < 4 by decide) c2.c9 (hM4 (by decide)) x2 hL (by rw [g2, u1.gpr, hI.rsi]) r2 w2
    c2 f2 d2 fun s3 c3 x3 g3 r3 w3 f3 d3 => ?_
  refine group4 hp hi (show 2 < 4 by decide) c3.c10 (hM4 (by decide)) x3 hL (by rw [g3, g2, u1.gpr, hI.rsi])
    r3 w3 c3 f3 d3 fun s4 c4 x4 g4 r4 w4 f4 d4 => ?_
  refine group4 hp hi (show 3 < 4 by decide) c4.c11 (hM4 (by decide)) x4 hL
    (by rw [g4, g3, g2, u1.gpr, hI.rsi]) r4 w4 c4 f4 d4 fun s5 c5 _ g5 r5 w5 f5 d5 => ?_
  have hg5 : s5.gpr = s.gpr := by rw [g5, g4, g3, g2, u1.gpr]
  refine wp_addi' fun s6 u6 => wp_addi' fun s7 u7 => wp_subi' fun s8 u8 hz => WP.block_nil ?_
  have c8 := ((c5.pres (Hi.of_lane u6.lane)).pres (Hi.of_lane u7.lane)).pres (Hi.of_lane u8.lane)
  refine ⟨⟨?_, ?_, by rw [u8.rd, u7.rd, u6.rd, r5], by rw [u8.wr, u7.wr, u6.wr, w5], c8,
    by rw [u8.mem, u7.mem, u6.mem]; exact f5, fun c hc => by rw [u8.mem, u7.mem, u6.mem]; exact d5 c (by omega)⟩,
    ?_, ?_⟩
  · rw [u8.other _ (by decide), u7.other _ (by decide), u6.gpr, hg5, hI.rdi,
      show BitVec.signExtend 64 (16 : BitVec 32) = BitVec.ofNat 64 16 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 16 * i + 16 = 16 * (i + 1) by omega]
  · rw [u8.other _ (by decide), u7.gpr, u6.other _ (by decide), hg5, hI.rsi, coeffAddr, coeffAddr,
      show BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 4 * (32 * i) + 128 = 4 * (32 * (i + 1)) by omega]
  · rw [u8.gpr, u7.other _ (by decide), u6.other _ (by decide), hg5]; rfl
  · rw [hz, u7.other _ (by decide), u6.other _ (by decide), hg5]; rfl

/-- The postcondition of the loops. -/
abbrev Done (d : Nat) (s : State) : Prop := Frame [pR (DD.fP s₀)] s₀.mem s.mem ∧
  ∀ k < 256, (coeffAt s.mem (DD.fP s₀) k).toNat = ((decodeDecompress d (DD.B s₀ d))[k]!).val

theorem main10 (hdd : dArg s₀ .rdx = 10) {s : State} (hdi : s.gpr .rdi = DD.bP s₀)
    (hsi : s.gpr .rsi = DD.fP s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa dd10V s (Done (s₀ := s₀) 10) := by
  unfold dd10V
  refine WP.seq (consts10_ok fun s1 hc1 hg1 hm1 hr1 hw1 => wp_mov32i fun s2 u2 => WP.block_nil ?_)
  refine WP.seq (wp_countdown (cnt := .rcx) (N := 31) (by decide) (by decide) (Inv10 s₀)
    (fun i hi s hI _ => step10 hp hdd hi hI) (fun s hI => ?_) (s := s2) ⟨?_, ?_, by rw [u2.rd, hr1, hrd],
      by rw [u2.wr, hw1, hwr], hc1.pres (Hi.of_lane u2.lane), by rw [u2.mem, hm1, hm]; exact Frame.refl _ _,
      fun k hk => absurd hk (by omega)⟩ (by rw [u2.gpr]; rfl))
  · refine wp_subi' fun s3 u3 _ => group10 hp hdd (g := 31) (ob' := 304) (ob := 6) (by decide) (by decide)
      (by decide) (by decide) (fun l hl => by rw [u3.lane, hI.c.c12 l hl]) (by decide) hM10' ?_
      (by rw [u3.other _ (by decide), hI.rsi]) (by rw [u3.rd, hI.rd]) (by rw [u3.wr, hI.wr])
      (hI.c.pres (Hi.of_lane u3.lane)) (by rw [u3.mem]; exact hI.frame) (fun k hk => by rw [u3.mem]; exact hI.done k hk)
      fun s4 _ _ _ _ hf4 hd4 => wp_vzu fun s5 _ hm5 _ _ => WP.block_nil ⟨by rw [hm5]; exact hf4,
        fun k hk => by rw [hm5]; exact hd4 k hk⟩
    rw [u3.gpr, hI.rdi, show BitVec.signExtend 64 (6 : BitVec 32) = BitVec.ofNat 64 6 by decide,
      Offset.add_ofNat_sub _ (by decide)]
  · rw [u2.other _ (by decide), hg1 _ (by decide), hdi]; simp
  · rw [u2.other _ (by decide), hg1 _ (by decide), hsi]; simp

theorem main4 (hdd : dArg s₀ .rdx = 4) {s : State} (hdi : s.gpr .rdi = DD.bP s₀)
    (hsi : s.gpr .rsi = DD.fP s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa dd4V s (Done (s₀ := s₀) 4) := by
  unfold dd4V
  refine WP.seq (consts4_ok fun s1 hc1 hg1 hm1 hr1 hw1 => wp_mov32i fun s2 u2 => WP.block_nil ?_)
  refine WP.seq (wp_countdown (cnt := .rcx) (N := 8) (by decide) (by decide) (Inv4 s₀)
    (fun i hi s hI _ => step4 hp hdd hi hI) (fun s hI => ?_) (s := s2) ⟨?_, ?_, by rw [u2.rd, hr1, hrd],
      by rw [u2.wr, hw1, hwr], hc1.pres (Hi.of_lane u2.lane), by rw [u2.mem, hm1, hm]; exact Frame.refl _ _,
      fun k hk => absurd hk (by omega)⟩ (by rw [u2.gpr]; rfl))
  · exact wp_vzu fun s5 _ hm5 _ _ => WP.block_nil ⟨by rw [hm5]; exact hI.frame,
      fun k hk => by rw [hm5]; exact hI.done k (by omega)⟩
  · rw [u2.other _ (by decide), hg1 _ (by decide), hdi]; simp
  · rw [u2.other _ (by decide), hg1 _ (by decide), hsi]; simp

end

theorem wp {s₀ : State} (hp : decodeDecompressK.pre s₀) :
    WP isa decodeDecompressAvx2 s₀ fun s' =>
      PolyIs s'.mem (s₀.gpr .rcx) (decodeDecompress (dArg s₀ .rdx) (bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat)) ∧
        Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem := by
  have hd := hp.2.2.2.2.2.1
  rw [DD.lenEq hp rfl]
  unfold decodeDecompressAvx2
  refine WP.seq (WP.mono (ddPrologue_ok s₀) fun s₁ ⟨⟨dx₁, si₁, z₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  have fin : ∀ {d : Nat}, dArg s₀ .rdx = d → ∀ s : State, Done (s₀ := s₀) d s →
      PolyIs s.mem (s₀.gpr .rcx) (decodeDecompress (dArg s₀ .rdx) (bytesAt s₀.mem (s₀.gpr .rdi)
        (32 * dArg s₀ .rdx))) ∧ Frame [pR (s₀.gpr .rcx)] s₀.mem s.mem := by
    intro d hdd s ⟨hf, hk⟩
    rw [hdd]
    exact ⟨polyIs_of_toNat hk, hf⟩
  refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from z₁) (fun h => ?_) (fun h => ?_)
  · rw [sub_beq_zero32, decide_eq_true_eq] at h
    have h1 : dArg s₀ .rdx = 1 := by simp only [dArg, h]; rfl
    rw [h1]
    exact DD.loop_ok (d := 1) (c := 8) (b := 1) hp (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) h1 (fun i hi s hs => DD.grp_ok (by decide) (by decide) (by decide) (by decide) (by decide) _
        (by rw [bytesAt_length]; omega) (by omega) hs) di₁ si₁ k₁.2.1 k₁.2.2 m₁
  · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
    refine WP.seq (WP.mono (cmp32_ok .rdx 4 s₁) fun s₂ ⟨⟨z₂, m₂⟩, k₂⟩ => ?_)
    rw [dx₁, BitVec.setWidth_32_64_32] at z₂
    have di₂ : s₂.gpr .rdi = DD.bP s₀ := by rw [k₂.gpr (by decide), di₁]
    have si₂ : s₂.gpr .rsi = DD.fP s₀ := by rw [k₂.gpr (by decide), si₁]
    refine WP.ite (M := isa) _ (show isa.eval .e s₂ = _ from z₂) (fun h' => ?_) (fun h' => ?_)
    · rw [sub_beq_zero32, decide_eq_true_eq] at h'
      have h4 : dArg s₀ .rdx = 4 := by simp only [dArg, h']; rfl
      exact WP.mono (main4 hp h4 di₂ si₂ (by rw [k₂.2.1, k₁.2.1]) (by rw [k₂.2.2, k₁.2.2]) (by rw [m₂, m₁]))
        (fin h4)
    · rw [sub_beq_zero32, decide_eq_false_iff_not] at h'
      have h10 : dArg s₀ .rdx = 10 := by
        rcases mem_compressWidths hd with e | e | e
        · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h
        · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h'
        · exact e
      exact WP.mono (main10 hp h10 di₂ si₂ (by rw [k₂.2.1, k₁.2.1]) (by rw [k₂.2.2, k₁.2.2]) (by rw [m₂, m₁]))
        (fin h10)

theorem correct (s : State) (hs : decodeDecompressK.pre s) :
    ∃ t s', Exec isa decodeDecompressAvx2 s t s' ∧ abiPreserved s s' ∧ decodeDecompressK.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := decodeDecompressAvx2)
    [.rax, .rcx, .rdx, .rsi, .rdi, .r9, .r10] (wp hs) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

end VG.Proof.MlKem.X86_64.DDY

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

theorem decodeDecompressY_ct :
    ConstantTime isa decodeDecompressK.pre decodeDecompressK.pub decodeDecompressAvx2 :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rsi, .rcx, .rsp] [.rdx])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

end VG.Proof.MlKem.X86_64
