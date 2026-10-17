module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Init
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Field48
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Pow
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Cvt
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.AesGcm.X86_64.Init
import VerifiedGarbage.Proof.Gcm.Powers

/-!
# Key setup with prepared powers on 512-bit registers

`Prepared.initZ` computes the powers as the AVX-512 loops do: `H'`–`H'¹⁶`
(`Stitch.setupG_ok'`), stored to `scratch = W + 1024`, and `H'¹⁷`–`H'⁴⁸`
from them (`StitchZ.pow48_ok`); `H'ᵏ = Hᵏ · x⁻¹` is the prepared form of
`Hᵏ` (`eq_hInvF`), so copying the pairs to the context (`copies_ok`) leaves
`PreparedPowersRepr` (`powersZ_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.PreparedZ
open VG VG.X86_64 VG.X86_64.RegUpd VG.Proof.Gcm.Poly
open VG.Spec.Gcm (Block blockAt hpow ctxH PreparedPowersRepr)
open VG.Proof.Gcm.X86_64.StitchZP (hInvF)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB ea_at)
open VG.Proof.Gcm.X86_64.StitchZ (φ_lanemul pw16 pow48_ok)
open VG.Proof.Gcm.X86_64.Stitch (setupG_ok' storesK_ok)
open VG.Proof.Gcm.X86_64.Vpclmul (load256_lo load256_hi)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Impl.Gcm.X86_64.Stitch (storesK pregs setupG)
open VG.Impl.Gcm.X86_64.StitchZ (pow48)
open VG.Impl.AesGcm.X86_64 (ptr imm)
open VG.Impl.AesGcm.X86_64.Prepared (copyPair powersZ)
open VG.Proof.AesGcm.X86_64 (imm_eq in_off in_left covers_off)

/-! ## The prepared form, in the field -/

theorem x_φ_hInvF (H : Block) (n : Nat) : x * φ (hInvF (hpow H n)) = φ H ^ n := by
  rw [hInvF, Gcm.X86_64.Pclmul.x_φ_hInv, φ_hpow]

/-- `x` cancels: a block `v` with `x · v = Hⁿ` is `Hⁿ · x⁻¹`. -/
theorem eq_hInvF {v H : Block} {n : Nat} (h : x * φ v = φ H ^ n) : v = hInvF (hpow H n) := by
  apply φ_inj
  have u := x_φ_hInvF H 0
  rw [pow_zero] at u
  have e := h.trans (x_φ_hInvF H n).symm
  calc φ v = φ (hInvF (hpow H 0)) * (x * φ v) := by rw [← mul_assoc, mul_comm _ x, u, one_mul]
    _ = φ (hInvF (hpow H 0)) * (x * φ (hInvF (hpow H n))) := by rw [e]
    _ = φ (hInvF (hpow H n)) := by rw [← mul_assoc, mul_comm _ x, u, one_mul]

/-! ## The copies -/

theorem toNat_add {p : Addr} {d n : Nat} (hw : p.toNat + n ≤ 2 ^ 64) (hd : d < n) :
    (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  have := p.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at hw this ⊢
  omega

/-- A 256-bit load into the two lanes of `d`. -/
theorem ld256_ok (d : XReg) (b : Reg) (o : Nat) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofInt 64 (o : Int)) 32) :
    WP isa (.block [.vmovdquLoad .l256 d (at_ b o)]) s fun s' =>
      (∀ l < 2, s'.lane d l = s.mem.readW (s.gpr b + BitVec.ofNat 64 (o + 16 * l)) 128) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let a := s.gpr b + BitVec.ofInt 64 (o : Int)
  let v := s.mem.readW a 256
  let t := s.setV .l256 d (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  rw [WP.block_cons_iff]
  refine ⟨t, by simp only [isa, exec, State.load256, ea_at, hin, ite_true, Option.map_some]; rfl,
    WP.block_nil ⟨fun l hl => ?_, rfl, rfl, rfl, rfl⟩⟩
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · simp only [t, State.lane_setV256, ite_true, v, load256_lo, a, BitVec.ofInt_natCast, Nat.mul_zero,
      Nat.add_zero]
  · simp only [t, State.lane_setV256, ite_true, Nat.one_ne_zero, ite_false, v, load256_hi, a,
      BitVec.ofInt_natCast, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]

/-- The pair of the context that pair `q` of the tables goes to. -/
def slot (q : Nat) : Nat := 8 * (q / 8) + 7 - q % 8

/-- Where the copies run: the tables at `S`, the context at `C`. -/
structure CEnv (C S : Addr) (G : Reg → BitVec 64) (rd wr : List Region) (s : State) : Prop where
  gpr : s.gpr = G
  r11 : s.gpr .r11 = S
  r13 : s.gpr .r13 = C
  rd : s.rd = rd
  wr : s.wr = wr

/-- Copy `q`. -/
theorem copyPair_ok {C S : Addr} {G : Reg → BitVec 64} {rd wr : List Region} (pC : Covers [⟨C, 1024⟩] wr) (pS : Covers [⟨S, 1024⟩] wr)
    (hc : C.toNat + 1024 ≤ 2 ^ 64) {q : Nat} (hq : q < 24) {s : State} (E : CEnv C S G rd wr s) :
    WP isa (.block (copyPair q)) s fun s' => CEnv C S G rd wr s' ∧
      (∀ l < 2, s'.mem.readW (C + BitVec.ofNat 64 (256 + 32 * slot q + 16 * l)) 128 =
        s.mem.readW (S + BitVec.ofNat 64 (32 * q + 16 * l)) 128) ∧
      Frame [⟨C + BitVec.ofNat 64 (256 + 32 * slot q), 32⟩] s.mem s'.mem := by
  rw [copyPair, show ∀ (i : Instr) is, (i :: is) = [i] ++ is from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (ld256_ok .xmm12 .r11 (32 * q) s (by
    rw [E.r11, E.rd, E.wr, BitVec.ofInt_natCast]; exact in_left (in_off pS (by omega) (by decide))))
    fun s₁ ⟨v₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  have e : 32 * (8 * (q / 8) + 15 - q % 8) = 256 + 32 * slot q := by simp only [slot]; omega
  refine WP.mono (storesK_ok .r13 [.xmm12] (8 * (q / 8) + 15 - q % 8) s₁ (fun k hk => by
      simp only [List.length_cons, List.length_nil] at hk
      rw [show k = 0 by omega, Nat.add_zero, e, wr₁, E.wr, g₁, E.r13, BitVec.ofInt_natCast]
      exact in_off pC (by simp only [slot]; omega) (by decide))
    (by rw [g₁, E.r13]; simp only [List.length_cons, List.length_nil]; omega))
    fun s' ⟨v, f, g, rd, wr, _⟩ => ⟨⟨by rw [g, g₁]; exact E.gpr, by rw [g, g₁]; exact E.r11, by rw [g, g₁]; exact E.r13,
      by rw [rd, rd₁]; exact E.rd, by rw [wr, wr₁]; exact E.wr⟩, fun l hl => ?_, ?_⟩
  · have h := v 0 (by decide) l hl
    rw [Nat.add_zero, e, g₁, E.r13] at h
    rw [h]
    simp only [List.getElem_cons_zero]
    rw [v₁ l hl, E.r11]
  · rw [g₁, E.r13, Nat.add_zero, e] at f
    rw [← m₁]
    exact f

/-- The first `n` copies. -/
theorem copies_ok {C S : Addr} {G : Reg → BitVec 64} {rd wr : List Region} (pC : Covers [⟨C, 1024⟩] wr) (pS : Covers [⟨S, 1024⟩] wr)
    (hc : C.toNat + 1024 ≤ 2 ^ 64) (hs : S.toNat + 1024 ≤ 2 ^ 64)
    (cs : (⟨C, 1024⟩ : Region).Disjoint ⟨S, 1024⟩) {s₀ : State} :
    ∀ n, n ≤ 24 → ∀ s, CEnv C S G rd wr s → s.mem = s₀.mem →
      WP isa (.block ((List.range n).flatMap copyPair)) s fun s' => CEnv C S G rd wr s' ∧
        (∀ q < n, ∀ l < 2, s'.mem.readW (C + BitVec.ofNat 64 (256 + 32 * slot q + 16 * l)) 128 =
          s₀.mem.readW (S + BitVec.ofNat 64 (32 * q + 16 * l)) 128) ∧
        Frame [⟨C + BitVec.ofNat 64 256, 768⟩] s₀.mem s'.mem
  | 0, _, s, E, hm => by
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨E, fun q hq => absurd hq (by omega), by rw [hm]; exact Frame.refl _ _⟩
  | n + 1, hn, s, E, hm => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (copies_ok pC pS hc hs cs n (by omega) s E hm) fun s₁ ⟨E₁, p₁, f₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (copyPair_ok pC pS hc (by omega) E₁) fun s' ⟨E', v, f⟩ => ⟨E', fun q hq l hl => ?_, ?_⟩
    · have hsl : slot n < 24 := by simp only [slot]; omega
      by_cases hqn : q = n
      · subst hqn
        rw [v l hl]
        refine f₁.readW (r := ⟨S + BitVec.ofNat 64 (32 * q + 16 * l), 16⟩) (Region.contains_self _ _)
          (fun r hr => ?_) (by decide)
        obtain rfl := List.mem_singleton.mp hr
        exact (cs.sub_left (Offset.sub_base _ (by decide))).symm.sub_left (Offset.sub_base _ (by omega))
      · have hsq : slot q ≠ slot n := by simp only [slot]; omega
        have hq24 : slot q < 24 := by simp only [slot]; omega
        rw [f.readW (r := ⟨C + BitVec.ofNat 64 (256 + 32 * slot q + 16 * l), 16⟩) (Region.contains_self _ _)
          (fun r hr => by
            obtain rfl := List.mem_singleton.mp hr
            exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)]
        exact p₁ q (by omega) l hl
    · exact f₁.trans (f.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        obtain rfl := List.mem_singleton.mp hr
        exact Offset.sub _ (by omega) (by simp only [slot]; omega)⟩)

/-! ## The powers -/

theorem pregs_get : ∀ i (h : i < pregs.length), pregs[i] = preg16 i
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
  | 7, _ => rfl | _ + 8, h => absurd h (by simp [pregs])

theorem slot_slot {k : Nat} (hk : k < 24) : slot (slot k) = k := by simp only [slot]; omega

/-- `rdi` at the context and `r11` at `scratch = W + 1024`. -/
theorem ptrs_run {C W : Addr} {s : State} (h13 : s.gpr .r13 = C) (h15 : s.gpr .r15 = W) :
    ∃ s₁, runBlock isa ([.mov .rdi (.reg .r13)] ++ ptr .r11 .r15 1024) s = some s₁ ∧
      s₁.gpr .rdi = C ∧ s₁.gpr .r11 = W + BitVec.ofNat 64 1024 ∧
      (∀ r, r ≠ .rdi → r ≠ .r11 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h13]
  · simp [gpr_setReg, h15]
  · intro r h1 h2; simp [gpr_setReg, h1, h2]
  all_goals simp [mem_arithFlags, mem_setReg, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags]

/-- `StitchZ.pow48`'s tables at `S`, from the sixteen powers there: pair `q`
holds `H'¹⁶ᵗ⁺¹⁶⁻²ᵐ` and the power below, for `q = 8 t + m`. -/
theorem tables {H : Block} {s₄ s₅ : State} {S : Addr} (hS : s₄.gpr .r11 = S)
    (B : ∀ k < 4, ∀ l < 4, x * φ (pw16 s₄ k l) = φ H ^ (16 - 4 * k - l))
    (t0 : ∀ k < 4, ∀ l < 4, s₅.mem.readW (s₄.gpr .r11 + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = pw16 s₄ k l)
    (t1 : ∀ k < 4, ∀ l < 4, s₅.mem.readW (s₄.gpr .r11 + BitVec.ofNat 64 (256 + 64 * k + 16 * l)) 128 =
      reduceB (Prod.zero.acc (pw16 s₄ k l) (pw16 s₄ 0 0)))
    (t2 : ∀ k < 4, ∀ l < 4, s₅.mem.readW (s₄.gpr .r11 + BitVec.ofNat 64 (512 + 64 * k + 16 * l)) 128 =
      reduceB (Prod.zero.acc (pw16 s₄ k l) (reduceB (Prod.zero.acc (pw16 s₄ 0 0) (pw16 s₄ 0 0))))) :
    ∀ q < 24, ∀ l < 2, x * φ (s₅.mem.readW (S + BitVec.ofNat 64 (32 * q + 16 * l)) 128) =
      φ H ^ (16 * (q / 8) + 16 - 2 * (q % 8) - l) := by
  intro q hq l hl
  rw [← hS]
  have hk : (2 * (q % 8) + l) / 4 < 4 := by omega
  have hj : (2 * (q % 8) + l) % 4 < 4 := by omega
  have B0 := B 0 (by decide) 0 (by decide)
  have Bk := B _ hk _ hj
  rcases (by omega : q / 8 = 0 ∨ q / 8 = 1 ∨ q / 8 = 2) with h | h | h
  · rw [show 32 * q + 16 * l = 64 * ((2 * (q % 8) + l) / 4) + 16 * ((2 * (q % 8) + l) % 4) by omega, t0 _ hk _ hj, Bk]
    congr 1; omega
  · rw [show 32 * q + 16 * l = 256 + 64 * ((2 * (q % 8) + l) / 4) + 16 * ((2 * (q % 8) + l) % 4) by omega,
      t1 _ hk _ hj, φ_lanemul Bk B0]
    congr 1; omega
  · rw [show 32 * q + 16 * l = 512 + 64 * ((2 * (q % 8) + l) / 4) + 16 * ((2 * (q % 8) + l) % 4) by omega,
      t2 _ hk _ hj, φ_lanemul Bk (φ_lanemul B0 B0)]
    congr 1; omega

/-- `vshufi32x4 zmm1, zmm1, zmm1, 0x44`: the two lanes of `xmm1`'s 256 bits in all four. -/
theorem bcast_ok (s : State) (h1 : ∀ l < 2, s.lane .xmm1 l = poly) :
    WP isa (.block [.zop (.vshufi32x4 .xmm1 .xmm1 .xmm1 0x44)]) s fun s' =>
      (∀ l < 4, s'.zlane .xmm1 l = poly) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ⟨fun l hl => ?_, rfl, rfl, rfl, rfl⟩⟩
  rw [zlane_vshufi32x4 _ _ _ _ _ _ hl]
  simp only [↓reduceIte]
  have h0 := (State.zlane_lt2 s .xmm1 (by decide : 0 < 2)).trans (h1 0 (by decide))
  have h1' := (State.zlane_lt2 s .xmm1 (by decide : 1 < 2)).trans (h1 1 (by decide))
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1'
  · exact h0
  · exact h1'

/-- `powersZ`: the 48 prepared powers of the hash subkey at `C + 240` into the
context at `C`, with `W` (2560 bytes of working space) at `r15`. -/
theorem powersZ_ok {C W : Addr} {rd wr : List Region} (pC : Covers [⟨C, 1024⟩] wr) (pW : Covers [⟨W, 2560⟩] wr)
    (cw : C.toNat + 1024 ≤ 2 ^ 64) (ww : W.toNat + 2560 ≤ 2 ^ 64) (cs : (⟨C, 1024⟩ : Region).Disjoint ⟨W, 2560⟩)
    {s : State} (h13 : s.gpr .r13 = C) (h15 : s.gpr .r15 = W) (hrd : s.rd = rd) (hwr : s.wr = wr) :
    WP isa (.block powersZ) s fun s' =>
      (∀ k < 24, ∀ l < 2, s'.mem.readW (C + BitVec.ofNat 64 (256 + 32 * k + 16 * l)) 128 =
        hInvF (hpow (ctxH s.mem C) (2 * k + 2 - l))) ∧
      Frame [⟨C + BitVec.ofNat 64 256, 768⟩, ⟨W + BitVec.ofNat 64 1024, 1024⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [show powersZ = ([.mov .rdi (.reg .r13)] ++ ptr .r11 .r15 1024) ++ (setupG ++ (storesK .r11 pregs 0 ++
      (([.zop (.vshufi32x4 .xmm1 .xmm1 .xmm1 0x44)] : List Instr) ++ (pow48 ++ (List.range 24).flatMap copyPair))))
    by simp only [powersZ, List.append_assoc], WP.block_append_iff]
  obtain ⟨s₁, run₁, d₁, r₁, g₁, m₁, rd₁, wr₁⟩ := ptrs_run h13 h15
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  set S := W + BitVec.ofNat 64 1024 with hSdef
  have pS : Covers [⟨S, 1024⟩] wr := covers_off pW (by decide) (by decide)
  have sw : S.toNat + 1024 ≤ 2 ^ 64 := by rw [hSdef, toNat_add ww (by decide)]; omega
  have cS : (⟨C, 1024⟩ : Region).Disjoint ⟨S, 1024⟩ := cs.sub_right (Offset.sub_base _ (by decide))
  -- `H'`–`H'¹⁶`.
  rw [WP.block_append_iff]
  have hk_in : InRegions (s₁.rd ++ s₁.wr) (Gcm.X86_64.Stitch.kp s₁) 256 := by
    show InRegions _ (s₁.gpr .rdi) 256
    have := in_off pC (d := 0) (n := 256) (by decide) (by decide)
    rw [show C + BitVec.ofNat 64 0 = C from BitVec.add_zero C] at this
    rw [d₁, rd₁, wr₁, hrd, hwr]; exact in_left this
  refine WP.mono (setupG_ok' hk_in) fun s₂ ⟨l0, l1, pw, g₂, m₂, rd₂, wr₂⟩ => ?_
  have hH : Gcm.X86_64.Stitch.hk s₁ = ctxH s.mem C := by
    show blockAt s₁.mem (s₁.gpr .rdi + 240) = blockAt s.mem (C + 240); rw [m₁, d₁]
  rw [hH] at pw
  have r₂ : s₂.gpr .r11 = S := by rw [g₂ _ (by decide), r₁]
  -- Stored to `S`.
  rw [WP.block_append_iff]
  refine WP.mono (storesK_ok .r11 pregs 0 s₂ (fun k hk => by
      simp only [pregs, List.length_cons, List.length_nil] at hk
      rw [wr₂, wr₁, hwr, r₂, BitVec.ofInt_natCast]
      exact in_off pS (by omega) (by decide))
    (by rw [r₂]; simp only [pregs, List.length_cons, List.length_nil]; omega)) fun s₃ ⟨sv, fr₃, g₃, rd₃, wr₃, ln₃⟩ => ?_
  have fr₃' : Frame [⟨S, 1024⟩] s₂.mem s₃.mem := fr₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    obtain rfl := List.mem_singleton.mp hr
    rw [r₂]; exact Offset.sub_base _ (by simp only [pregs, List.length_cons, List.length_nil]; omega)⟩
  -- The reduction constant in the four lanes.
  rw [WP.block_append_iff]
  refine WP.mono (bcast_ok s₃ fun l hl => by rw [ln₃]; exact l1 l hl) fun s₄ ⟨b₄, g₄, m₄, rd₄, wr₄⟩ => ?_
  have r₄ : s₄.gpr .r11 = S := by rw [g₄, g₃, r₂]
  -- `H'¹⁷`–`H'⁴⁸`.
  rw [WP.block_append_iff]
  have sIn : InRegions wr S 1024 := by
    have h := in_off pS (d := 0) (n := 1024) (by decide) (by decide)
    rwa [show S + BitVec.ofNat 64 0 = S from BitVec.add_zero S] at h
  refine WP.mono (pow48_ok s₄ (by rw [wr₄, wr₃, wr₂, wr₁, hwr, r₄]; exact sIn) b₄)
    fun s₅ ⟨t0, t1, t2, _, fr₅, g₅, rd₅, wr₅, _⟩ => ?_
  have B : ∀ k < 4, ∀ l < 4, x * φ (pw16 s₄ k l) = φ (ctxH s.mem C) ^ (16 - 4 * k - l) := by
    intro k hk l hl
    have hi : 2 * k + l / 2 < pregs.length := by simp only [pregs, List.length_cons, List.length_nil]; omega
    have e := sv (2 * k + l / 2) hi (l % 2) (by omega)
    rw [pregs_get _ hi] at e
    show x * φ (s₄.mem.readW (s₄.gpr .r11 + BitVec.ofNat 64 (64 * k + 16 * l)) 128) = _
    rw [m₄, g₄, g₃, show 64 * k + 16 * l = 32 * (0 + (2 * k + l / 2)) + 16 * (l % 2) by omega, e,
      pw _ (by omega) _ (by omega)]
    congr 1; omega
  have T := tables r₄ B t0 t1 t2
  rw [r₄] at fr₅
  -- The copies.
  have h13₅ : s₅.gpr .r13 = C := by rw [g₅, g₄, g₃, g₂ _ (by decide), g₁ _ (by decide) (by decide), h13]
  have h11₅ : s₅.gpr .r11 = S := by rw [g₅, r₄]
  refine WP.mono (copies_ok (rd := rd) pC pS cw sw cS 24 (Nat.le_refl _) s₅
    ⟨rfl, h11₅, h13₅, by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hrd], by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hwr]⟩ rfl)
    fun s' ⟨E', pv, f'⟩ => ⟨fun k hk l hl => ?_, ?_, fun r h1 h2 h3 => ?_, by rw [E'.rd, hrd], by rw [E'.wr, hwr]⟩
  · have hq : slot k < 24 := by simp only [slot]; omega
    have e := pv (slot k) hq l hl
    rw [slot_slot hk] at e
    rw [e]
    apply eq_hInvF
    rw [T _ hq l hl]
    congr 1; simp only [slot]; omega
  · have hR : ∀ {R : Region} {rs : List Region}, R ∈ rs → ∀ r ∈ [R], r ∈ rs := fun h r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact h
    have i₁ := hR (rs := [⟨C + BitVec.ofNat 64 256, 768⟩, ⟨S, 1024⟩]) (List.mem_cons_self ..)
    have i₂ := hR (rs := [⟨C + BitVec.ofNat 64 256, 768⟩, ⟨S, 1024⟩]) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    rw [← m₁, ← m₂]
    rw [m₄] at fr₅
    exact ((fr₃'.mono i₂).trans (fr₅.mono i₂)).trans (f'.mono i₁)
  · rw [E'.gpr, g₅, g₄, g₃, g₂ r h1, g₁ r h2 h3]

end VG.Proof.AesGcm.X86_64.PreparedZ

namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (blockAt)
open VG.Proof.AesGcm.X86_64.PreparedZ (powersZ_ok)

/-- `vg_aes_gcm_init_prepared` on 512-bit registers. -/
theorem initZ_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.initPreparedX86_64.pre s) :
    WP isa (Prepared.initZ v.callees) s fun s' =>
      gprPreserved s s' ∧ Proof.AesGcm.initPreparedX86_64.post s s' := by
  obtain ⟨L, pC, pW⟩ := IPLay.of hp
  have hl : (s.gpr .rsi).toNat = 16 ∨ (s.gpr .rsi).toNat = 24 ∨ (s.gpr .rsi).toNat = 32 :=
    hp.2.2.2.2.2.2.2.2.2.2.2.2
  refine initWith_wp v (by decide) hp fun s₅ D => ?_
  have pC₅ : Covers [⟨s.gpr .rdx, 1024⟩] s₅.wr := by rw [D.wr]; exact pC
  have pW₅ : Covers [⟨s.gpr .rcx, 2560⟩] s₅.wr := by rw [D.wr]; exact pW
  rw [WP.block_append_iff]
  refine WP.mono (powersZ_ok pC₅ pW₅ L.cw L.ww L.cs D.r13 D.r15 rfl rfl) fun t ⟨pw, fr, g, _, wr⟩ => ?_
  have dS : ∀ r ∈ [(⟨s.gpr .rdx + BitVec.ofNat 64 256, 768⟩ : Region), ⟨s.gpr .rcx + BitVec.ofNat 64 1024, 1024⟩],
      (savedR (s.gpr .rcx)).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((L.cs.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))).symm
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  have hret : t.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
    rw [ret_kept fr (fun r hr => ?_), D.ret]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.rc.sub_right (Offset.sub_base _ (by decide))
    · exact L.rs.sub_right (Offset.sub_base _ (by decide))
  refine WP.mono (exit_ok (by rw [g _ (by decide) (by decide) (by decide), D.r15])
    (by rw [g _ (by decide) (by decide) (by decide), D.rsp])
    (covers_left (by rw [wr]; exact pW₅)) (D.saved.frame fr dS) hret) fun s' ⟨hg, hm, _⟩ => ⟨hg, ?_⟩
  change Spec.Gcm.KeyRepr s'.mem (s.gpr .rdx) _ ∧ Spec.Gcm.PreparedPowersRepr s'.mem (s.gpr .rdx)
  rw [hm]
  have hC : ∀ r ∈ [(⟨s.gpr .rdx + BitVec.ofNat 64 256, 768⟩ : Region), ⟨s.gpr .rcx + BitVec.ofNat 64 1024, 1024⟩],
      (⟨s.gpr .rdx, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.base_disjoint _ (by decide) (by have := L.cw; omega)
    · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  have hH : Spec.Gcm.ctxH t.mem (s.gpr .rdx) = Spec.Gcm.ctxH s₅.mem (s.gpr .rdx) :=
    VG.Proof.Aes.X86_64.AesNi.blockAt_frame fr fun r hr =>
      (hC r hr).sub_left (Offset.sub_base _ (by decide))
  refine ⟨keyRepr_frame fr (by rw [length_bytesAt]; exact hl) hC D.key, fun k hk => ?_⟩
  rw [hH, Gcm.X86_64.StitchZR.preparedPower_eq, Gcm.X86_64.StitchZR.preparedPower_eq]
  have p0 := pw k hk 0 (by decide)
  have p1 := pw k hk 1 (by decide)
  rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at p0
  rw [show 256 + 32 * k + 16 * 1 = 272 + 32 * k by omega, show 2 * k + 2 - 1 = 2 * k + 1 by omega] at p1
  exact ⟨p0, p1⟩

end VG.Proof.AesGcm.X86_64
