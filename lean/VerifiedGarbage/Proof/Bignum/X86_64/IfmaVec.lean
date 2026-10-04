import VerifiedGarbage.Proof.Bignum.X86_64.IfmaExp

/-!
# RSA with AVX512_IFMA on x86-64: the vector code

`vec` (`vec_ok`): within Intel's MXCSR prologue and epilogue (the caller's
MXCSR saved at `oMx`, `0x1FBF` loaded, and the saved value, bits 31:16
cleared, restored), `X` and `Y` into Montgomery form for `R = 2¹⁰⁴⁰` (by
`K1 ≡ 2¹⁰⁵⁶`, as they hold `x 2¹⁰²⁴` and `2¹⁰²⁴`), the exponentiations,
and `Y := Y Fin / R`: `Y ≡ x^e Fin`.
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum.X86_64 (off word ofs Outside off_off Scr ofs_off writeW_outside)
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 oK1 oTab oS oV oX oY oE oFin oMx mask52)

theorem Scr.mono {s : State} {B : Addr} {Z Z' : Nat} (h : Scr s B Z) (hz : Z' ≤ Z) : Scr s B Z' :=
  let ⟨B₀, o, L, hm, hb, hL, hL'⟩ := h.wr
  ⟨⟨B₀, o, L, hm, hb, by omega, hL'⟩, by have := h.nowrap; omega⟩

/-- The prologue's first half: the caller's MXCSR, bits 31:16 cleared, at `oMx`. -/
theorem mxSave_ok {s : State} {B : Addr} (hB : s.gpr .rbx = B) (hs : Scr s B (2 * D + 8)) :
    WP isa (.block [.stmxcsr (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx oMx),
        .mov32 .r11 (.mem (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx oMx)), .alu32 .and .r11 (.imm 0xFFFF),
        .store32 (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx oMx) .r11]) s fun s' =>
      s'.mem = (s.mem.writeW (off B oMx) s.mxcsr).writeW (off B oMx) (s.mxcsr &&& 0xFFFF) ∧
      VG.Proof.MlKem.X86_64.Keep [.r11] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hst : InRegions s.wr (B + BitVec.ofNat 64 oMx) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := oMx) (n := 4) (by simp only [oMx]; omega) (by decide); ⟨_, h, c⟩
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 oMx) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := oMx) (n := 4) (by simp only [oMx]; omega) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r11] (Q := fun s' =>
    s'.mem = (s.mem.writeW (off B oMx) s.mxcsr).writeW (off B oMx) (s.mxcsr &&& 0xFFFF) ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [ea_at', hB, hst, hld, Mem.readW_writeW_self32]
    and_intros <;> rfl) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩


/-- The prologue's second half: `MXCSR := 0x1FBF`. -/
theorem mxSet_ok {s : State} {B : Addr} (hB : s.gpr .rbx = B) (hs : Scr s B (2 * D + 8)) :
    WP isa (.block [.mov32 .rax (.imm 0x1FBF), .store32 (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx (oMx + 4)) .rax,
        .ldmxcsr (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx (oMx + 4)), .lfence]) s fun s' =>
      s'.mem = s.mem.writeW (off B (oMx + 4)) (0x1FBF : BitVec 32) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax] s s' ∧ s'.mxcsr = 0x1FBF := by
  have hst : InRegions s.wr (B + BitVec.ofNat 64 (oMx + 4)) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := oMx + 4) (n := 4) (by simp only [oMx]; omega) (by decide); ⟨_, h, c⟩
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (oMx + 4)) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := oMx + 4) (n := 4) (by simp only [oMx]; omega) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun s' =>
    s'.mem = s.mem.writeW (off B (oMx + 4)) (0x1FBF : BitVec 32) ∧ s'.mxcsr = 0x1FBF) (by
    xrun [ea_at', hB, hst, hld, Mem.readW_writeW_self32]) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩

theorem and_ffff_hi (x : BitVec 32) : (x &&& 0xFFFF).extractLsb' 16 16 = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, hi, decide_true, Bool.true_and]
  rw [show (0xFFFF : BitVec 32) = BitVec.ofNat 32 (2 ^ 16 - 1) from rfl, BitVec.getLsbD_ofNat]
  simp only [Nat.testBit_two_pow_sub_one]
  simp

/-- The epilogue: the saved MXCSR. -/
theorem mxRestore_ok {s : State} {B : Addr} {v : BitVec 32} (hB : s.gpr .rbx = B) (hs : Scr s B (2 * D + 8))
    (hv : s.mem.readW (off B oMx) 32 = v &&& 0xFFFF) :
    WP isa (.block [.ldmxcsr (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx oMx), .vop .vzeroupper]) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = v &&& 0xFFFF := by
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 oMx) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := oMx) (n := 4) (by simp only [oMx]; omega) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  rw [WP.block_cons_iff]
  refine ⟨{ s with mxcsr := v &&& 0xFFFF }, ?_, ?_⟩
  · simp only [exec, ea_at', hB, State.load32, hld, ite_true, Option.bind_some]
    rw [show s.mem.readW (B + BitVec.ofNat 64 oMx) 32 = v &&& 0xFFFF from hv, and_ffff_hi]; rfl
  · rw [WP.block_cons_iff]
    exact ⟨_, rfl, WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩⟩


/-- Into Montgomery form: `X ≡ a c`, `K ≡ d` with `c d = R²` give `X K / R ≡ a R`. -/
theorem mont_into {X K X' a c d R m : Nat} (hR : Nat.Coprime R m) (hX : X % m = a * c % m) (hK : K % m = d % m)
    (e : c * d = R * R) (h : X' * R % m = X * K % m) : X' % m = a * R % m := by
  apply VG.Proof.Bignum.mont_cancel hR
  rw [h, Nat.mul_mod, hX, hK, ← Nat.mul_mod]
  congr 1
  rw [Nat.mul_assoc, e, Nat.mul_assoc]

/-- Out of Montgomery form: `Y ≡ b R` gives `Y F / R ≡ b F`. -/
theorem mont_out {Y F Y' b R m : Nat} (hR : Nat.Coprime R m) (hY : Y % m = b * R % m)
    (h : Y' * R % m = Y * F % m) : Y' % m = b * F % m := by
  apply VG.Proof.Bignum.mont_cancel hR
  rw [h, Nat.mul_mod, hY, ← Nat.mul_mod]
  congr 1
  grind

/-- A word of a region outside `Y`, `S`, `V` and the table. -/
theorem OutE.word_at {B : Addr} {m m' : Mem} (h : OutE B m m') {p c : Nat} (hp : p < 2)
    (hY : c + 8 ≤ oY ∨ oY + 160 ≤ c) (hS : c + 8 ≤ oS ∨ oS + 160 ≤ c) (hV : c + 8 ≤ oV ∨ oV + 8 ≤ c)
    (hT : c + 8 ≤ oTab ∨ oTab + 2560 ≤ c) (hcD : c + 8 ≤ D) :
    word m' B (D * p + c) = word m B (D * p + c) := by
  have hD : D = 3872 := rfl
  refine (Mem.readW_congr fun i hi => (h _ fun p' hp' => ?_).symm).symm
  rw [ofs_off B (by rcases D_mul hp with h | h <;> omega)]
  have : i < 8 := hi
  simp only [oY, oS, oV, oTab] at *
  rcases D_mul hp with h1 | h1 <;> rcases D_mul hp' with h2 | h2 <;> omega

theorem OutE.limb {B : Addr} {m m' : Mem} (h : OutE B m m') {p c : Nat} (hp : p < 2)
    (hY : c + 160 ≤ oY ∨ oY + 160 ≤ c) (hS : c + 160 ≤ oS ∨ oS + 160 ≤ c) (hV : c + 160 ≤ oV ∨ oV + 8 ≤ c)
    (hT : c + 160 ≤ oTab ∨ oTab + 2560 ≤ c) (hcD : c + 160 ≤ D) {j : Nat} (hj : j < 20) :
    limb m' B (D * p + c) j = limb m B (D * p + c) j := by
  have := off_lt j hj
  show (word m' B _).toNat = (word m B _).toNat
  rw [Nat.add_assoc, h.word_at hp (by omega) (by omega) (by omega) (by omega) (by omega)]

end VG.Proof.Bignum.X86_64.AmmSym
