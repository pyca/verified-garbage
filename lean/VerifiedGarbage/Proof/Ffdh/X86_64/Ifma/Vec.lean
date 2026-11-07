module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.VecR
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubVec
public import VerifiedGarbage.Impl.Ffdh.X86_64.Ifma
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Conv
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Vec
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.VecR
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubVec
meta import VerifiedGarbage.Impl.Ffdh.X86_64.Ifma
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Conv
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Vec
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# FFDH's exponentiation with AVX512_IFMA on x86-64: the vector code

`vec_ok`: `Ifma.vec`, one lane of `CrtIfma.expLoop` from the digit at `oSt`
(`expLoopFrom_ok`), within Intel's MXCSR prologue and epilogue, which keep
the caller's MXCSR, bits 31:16 cleared, in `r14` (`pro_ok`, `epi_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Impl.Ffdh.X86_64.Ifma
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Bignum.X86_64.Ifma
open VG.Proof.Bignum.X86_64.AmmSym (limbN limbN_lt pow2_le cop2 writeW32_outside)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The prologue: the caller's MXCSR, bits 31:16 cleared, in `r14`, and
`MXCSR := 0x1FBF`. -/
theorem pro_ok {s : State} {B : Addr} {d Z : Nat} (hB : s.gpr .rbx = B) (hs : Scr s B Z) (hd : d + 8 ≤ Z) :
    WP isa (.block [.stmxcsr (at_ .rbx d), .mov32 .r14 (.mem (at_ .rbx d)), .alu32 .and .r14 (.imm 0xFFFF),
        .mov32 .rax (.imm 0x1FBF), .store32 (at_ .rbx (d + 4)) .rax, .ldmxcsr (at_ .rbx (d + 4)), .lfence]) s
      fun s' => s'.mem = (s.mem.writeW (off B d) s.mxcsr).writeW (off B (d + 4)) (0x1FBF : BitVec 32) ∧
        s'.gpr .r14 = (s.mxcsr &&& 0xFFFF).setWidth 64 ∧
        VG.Proof.MlKem.X86_64.Keep [.r14, .rax] s s' ∧ s'.mxcsr = 0x1FBF := by
  have hst : InRegions s.wr (B + BitVec.ofNat 64 d) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d) (n := 4) (by omega_using [hd]) (by decide); ⟨_, h, c⟩
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d) (n := 4) (by omega_using [hd]) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  have hst4 : InRegions s.wr (B + BitVec.ofNat 64 (d + 4)) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d + 4) (n := 4) (by omega_using [hd]) (by decide); ⟨_, h, c⟩
  have hld4 : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (d + 4)) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d + 4) (n := 4) (by omega_using [hd]) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r14, .rax] (Q := fun s' =>
    s'.mem = (s.mem.writeW (off B d) s.mxcsr).writeW (off B (d + 4)) (0x1FBF : BitVec 32) ∧
      s'.gpr .r14 = (s.mxcsr &&& 0xFFFF).setWidth 64 ∧ s'.mxcsr = 0x1FBF) (by
    xrun [eaG', hB, hst, hld, hst4, hld4, Mem.readW_writeW_self32]) rfl)
    fun s' ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, k, c⟩

/-- The epilogue: the saved MXCSR back from `r14`. -/
theorem epi_ok {s : State} {B : Addr} {d Z : Nat} {v : BitVec 32} (hB : s.gpr .rbx = B) (hs : Scr s B Z)
    (hd : d + 8 ≤ Z) (h14 : s.gpr .r14 = (v &&& 0xFFFF).setWidth 64) :
    WP isa (.block [.lfence, .store32 (at_ .rbx d) .r14, .ldmxcsr (at_ .rbx d), .vop .vzeroupper]) s fun s' =>
      s'.mem = s.mem.writeW (off B d) (v &&& 0xFFFF) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.mxcsr = v &&& 0xFFFF := by
  have hst : InRegions s.wr (B + BitVec.ofNat 64 d) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d) (n := 4) (by omega_using [hd]) (by decide); ⟨_, h, c⟩
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d) (n := 4) (by omega_using [hd]) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  xrun [eaG', hB, hst, hld, h14, Mem.readW_writeW_self32, VG.Proof.Bignum.X86_64.AmmSym.and_ffff_hi]
  and_intros <;> rfl

/-- The first digit, from `oSt`. -/
theorem start_ok {t : State} {F : Addr} {Z i₀ : Nat} (hB : t.gpr .rbx = F) (hs : Scr t F Z) (hd : oSt l + 8 ≤ Z)
    (hv : word t.mem F (oSt l) = BitVec.ofNat 64 i₀) :
    WP isa (.block [.mov .r13 (.mem (at_ .rbx (oSt l)))]) t fun u => u.mem = t.mem ∧ u.rd = t.rd ∧ u.wr = t.wr ∧
      u.mxcsr = t.mxcsr ∧ u.gpr .r13 = BitVec.ofNat 64 i₀ ∧ ∀ r, r ≠ .r13 → u.gpr r = t.gpr r := by
  have hld : InRegions (t.rd ++ t.wr) (F + BitVec.ofNat 64 (oSt l)) 8 :=
    let ⟨_, h, c⟩ := hs.region (d := oSt l) (n := 8) (by omega_using [hd]) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r13] (Q := fun u =>
    u.gpr .r13 = BitVec.ofNat 64 i₀ ∧ u.mem = t.mem ∧ u.mxcsr = t.mxcsr) (by
    xrun [eaG', hB, hld]
    exact ⟨hv, rfl⟩) rfl)
    fun u ⟨⟨a, b, c⟩, k⟩ => ⟨b, k.2.1, k.2.2, c, a, fun r hr => k.gpr (by simp [hr])⟩

/-- A word above the lanes' regions, through a frame of them. -/
theorem Out2.word_hi (hl : AmmOk l) {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 l B o n m m') {c : Nat}
    (hoD : o + n ≤ l.D) (hc : l.nl * l.D ≤ c) (hz : c + 8 ≤ 2 ^ 64) : word m' B c = word m B c := by
  refine (Mem.readW_congr fun i hi => (h _ fun p hp => ?_).symm).symm
  rw [ofs_off B (by omega_using [hz, hi])]
  have := lane_end hl hp
  exact .inr (by omega_using [hoD, hc, this])

/-- The vector code, from what the region holds (as `vecR_ok`), from the
digit `i₀` at `oSt`, before which the exponents' digits are zero. -/
theorem vec_ok (hl : AmmOk l) {s : State} {F : Addr} {M K1 Xc Y Fin x e : Nat → Nat} {mi : Nat → BitVec 64}
    {Q : Prop} {w R i₀ : Nat}
    (hw : w = l.W) (hR : R = 2 ^ (64 * w)) (hB : s.gpr .rbx = F) (hs : Scr s F (oSt l + 8))
    (hM : LimbsAt l s.mem F oM M) (hK : LimbsAt l s.mem F l.oK1 K1) (hX : LimbsAt l s.mem F l.oX Xc)
    (hY : LimbsAt l s.mem F l.oY Y) (hF : LimbsAt l s.mem F l.oFin Fin)
    (hk0 : ∀ p < l.nl, ∀ t < 4, word s.mem F (l.D * p + l.oK0 + 8 * t) = mi p &&& mask52)
    (hinv : ∀ p < l.nl, (M p % 2 ^ 64 * (mi p).toNat + 1) % 2 ^ 64 = 0)
    (hMlt : ∀ p < l.nl, M p < 2 ^ (64 * w)) (hModd : ∀ p < l.nl, M p % 2 = 1)
    (hKlt : ∀ p < l.nl, K1 p < M p) (hXlt : ∀ p < l.nl, Xc p < M p) (hYlt : ∀ p < l.nl, Y p < M p)
    (hFlt : ∀ p < l.nl, Fin p < 2 * M p)
    (vx : Q → ∀ p < l.nl, Xc p % M p = x p * R % M p)
    (vy : Q → ∀ p < l.nl, Y p % M p = R % M p)
    (vk : Q → ∀ p < l.nl, K1 p % M p = 2 ^ l.dbls * R % M p)
    (hi₀ : i₀ ≤ l.ND) (hst : word s.mem F (oSt l) = BitVec.ofNat 64 i₀)
    (hz : ∀ p < l.nl, e p / l.T ^ (l.ND - i₀) = 0)
    (hd : ∀ p < l.nl, ∀ i < l.ND, dig l s.mem F p i = digit l (e p) i) :
    WP isa (Impl.Ffdh.X86_64.Ifma.vec l) s fun s' =>
      (∀ p < l.nl, Good l s'.mem F M l.oY p ∧
        (Q → val52 l s'.mem F (l.D * p + l.oY) % M p = x p ^ e p * Fin p % M p)) ∧
      Outside F 0 (l.nl * l.D + 8) s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr &&& 0xFFFF := by
  subst hR hw
  obtain ⟨cb1, cb2, cb3, cb4, cb5, cb6⟩ := conv_boundsN hl
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  have hn := hs.nowrap
  have hMx : l.oMx = l.nl * l.D := rfl
  have hSt : oSt l = l.nl * l.D + 8 := rfl
  have hnD := nlD_le hl
  have hv : ∀ {c} {v : Nat → Nat}, LimbsAt l s.mem F c v → ∀ p < l.nl, v p < 2 * M p →
      val52 l s.mem F (l.D * p + c) = v p :=
    fun h p hp hlt => val52_of hl (h p hp) (by have := two_mul_lt (hMlt p hp); omega_arith)
  have ar : Ar l s.mem F M (fun p => (mi p &&& mask52).toNat) := by
    refine ⟨fun p hp j hj => ?_, fun p hp => hv hM p hp (by have := hModd p hp; omega_arith), fun p hp t ht => ?_,
      fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
    · rw [limb_of (hM p hp) hj]; exact limbN_lt _ _
    · rw [hk0 p hp t ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [BitVec.toNat_and, show mask52.toNat = 2 ^ 52 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by decide)
    · rw [limb_of (hM p hp) (by simp only [Lay.L]; have := hl.bounds; omega_arith)]; exact k0_of (hinv p hp)
    · have h4 : 4 * M p ≤ 2 ^ (64 * l.W + 2) := by
        have := hMlt p hp
        rw [Nat.pow_succ, Nat.pow_succ]; omega_arith
      exact Nat.le_trans h4 (pow2_le (by omega_arith))
  have e2 : 2 ^ (104 * l.S - 64 * l.W) = 2 ^ l.dbls * 2 ^ (64 * l.W) := by
    rw [← Nat.pow_add]; congr 1; simp only [Lay.dbls]; omega_arith
  unfold Impl.Ffdh.X86_64.Ifma.vec withMx
  refine WP.seq (WP.mono (pro_ok (d := l.oMx) hB hs (by omega_using [hMx, hSt])) fun s₁ ⟨m₁, r14₁, k₁, x₁⟩ => ?_)
  have hB₁ : s₁.gpr .rbx = F := by rw [k₁.gpr (by decide)]; exact hB
  have hs₁ : Scr s₁ F (oSt l + 8) := hs.congr k₁.2.2
  have O : Outside F (l.nl * l.D) 8 s.mem s₁.mem := by
    rw [m₁, hMx]
    exact ((writeW32_outside _ F _ (by omega_using [hn, hSt])).mono (by omega_using []) (by omega_using [])).trans
      ((writeW32_outside _ F _ (by omega_using [hn, hSt])).mono (by omega_using []) (by omega_using []))
  have gx := fun p hp => (good_of hl (hX p hp) (by have := hXlt p hp; omega_arith) (hMlt p hp)).of_hi hl O hp
    (by omega_using [o3, o10])
  have gy := fun p hp => (good_of hl (hY p hp) (by have := hYlt p hp; omega_arith) (hMlt p hp)).of_hi hl O hp
    (by omega_using [o2, o10])
  have gk := fun p hp => (good_of hl (hK p hp) (by have := hKlt p hp; omega_arith) (hMlt p hp)).of_hi hl O hp
    (by omega_using [o7, o10])
  have gf := fun p hp => (good_of hl (hF p hp) (hFlt p hp) (hMlt p hp)).of_hi hl O hp (by omega_using [o9, o10])
  have hst₁ : word s₁.mem F (oSt l) = BitVec.ofNat 64 i₀ := by
    rw [O.word (.inr (by omega_using [hSt])) (by omega_using [hn, hSt])]; exact hst
  refine WP.seq (WP.mono (expLoopFrom_ok hl (st := [.mov .r13 (.mem (at_ .rbx (oSt l)))]) (x := x) (e := e) (Q := Q)
    ⟨hB₁, VG.Proof.Bignum.X86_64.AmmSym.Scr.mono hs₁ (by omega_using [hSt]), Ar.of_hi hl O ar, fun p hp => cop2 (hModd p hp) _, gx, gy, gk,
      fun q p hp => by
        rw [hi_val hl O hp (by omega_using [o3, o10]), hv hX p hp (by have := hXlt p hp; omega_arith)]; exact vx q p hp,
      fun q p hp => by
        rw [hi_val hl O hp (by omega_using [o2, o10]), Nat.one_mul, ← vy q p hp,
          hv hY p hp (by have := hYlt p hp; omega_arith)],
      fun q p hp => by
        rw [hi_val hl O hp (by omega_using [o7, o10]), e2, ← vk q p hp,
          hv hK p hp (by have := hKlt p hp; omega_arith)]⟩ gf hi₀ hz
    (fun p hp i hi => by rw [dig_of_hi hl O hp hi]; exact hd p hp i hi)
    fun t hBt _ hwt ht => start_ok hBt (hs₁.congr hwt) (Nat.le_refl _)
      (by rw [Out2.word_hi hl ht (by omega_using [o2, o5, o10]) (by omega_using [hSt]) (by omega_using [hn, hSt])]
          exact hst₁))
    fun s₂ ⟨v₂, O₂, g₂, rd₂, wr₂, x₂⟩ => ?_)
  have hB₂ : s₂.gpr .rbx = F := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact hB₁
  have r14₂ : s₂.gpr .r14 = (s.mxcsr &&& 0xFFFF).setWidth 64 := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact r14₁
  refine WP.mono (epi_ok (d := l.oMx) hB₂ (hs₁.congr wr₂) (by omega_using [hMx, hSt]) r14₂)
    fun s₃ ⟨m₃, g₃, rd₃, wr₃, x₃⟩ => ⟨fun p hp => ?_, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 => ?_,
      by rw [rd₃, rd₂, k₁.2.1], by rw [wr₃, wr₂, k₁.2.2], x₃⟩
  · have O₃ : Outside F (l.nl * l.D) 8 s₂.mem s₃.mem := by
      rw [m₃, hMx]
      exact (writeW32_outside _ F _ (by omega_using [hn, hSt])).mono (by omega_using []) (by omega_using [])
    refine ⟨(v₂ p hp).1.of_hi hl O₃ hp (by omega_using [o2, o10]), fun hq => ?_⟩
    rw [hi_val hl O₃ hp (by omega_using [o2, o10]), (v₂ p hp).2 hq, hi_val hl O hp (by omega_using [o9, o10]),
      hv hF p hp (hFlt p hp)]
  · have O₃ : Outside F 0 (l.nl * l.D + 8) s₂.mem s₃.mem := by
      rw [m₃, hMx]
      exact (writeW32_outside _ F _ (by omega_using [hn, hSt])).mono (by omega_using []) (by omega_using [])
    exact ((O.mono (by omega_using []) (by omega_using [])).trans
      ((O₂.toOutside hl).mono (by omega_using []) (by omega_using []))).trans O₃
  · rw [g₃, g₂ r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12, k₁.gpr (by simp [r1, r11])]

end VG.Proof.Ffdh.X86_64.Ifma
