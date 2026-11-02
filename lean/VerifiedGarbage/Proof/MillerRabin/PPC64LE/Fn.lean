module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Core
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Save
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFn
import VerifiedGarbage.Proof.MillerRabin.Representation
import VerifiedGarbage.Proof.Bignum.Minv32
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq

/-!
# The Miller–Rabin round on PPC64LE: the function

`vg_miller_rabin_round(ws = r3, ws_len = r4, scratch = r5)` (`fnContract`):
`round` saves the nonvolatile registers in the scratch buffer, sets up the
working space's registers (`setup_ok`), runs the round (`core_ok`), and
restores them (`fn_correct`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE
open VG.Proof.Bignum (slot slot_sep)
open VG.Proof.RsaKeyGen (mrE mrA)
open VG.Proof.Rsa.Mont (numAt wOf wordAt arrAt)

/-- The working space: `ws_len` words at `r3`. -/
abbrev wsR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat * 8⟩

/-- `vg_miller_rabin_round(ws = r3, ws_len = r4, scratch = r5)`, the scratch
buffer 144 bytes. -/
def fnContract : Contract isa where
  pre s :=
    let ws := s.gpr .r3
    let n := (s.gpr .r4).toNat
    s.rd = [] ∧ s.wr = [wsR s, Save.savR (s.gpr .r5)] ∧ (wsR s).Disjoint (Save.savR (s.gpr .r5)) ∧
      ws.toNat + n * 8 ≤ 2 ^ 64 ∧ Proof.MillerRabin.Round.Layout Proof.MillerRabin.Round.compact s.mem ws n ∧
      Proof.MillerRabin.Round.Prepared Proof.MillerRabin.Round.compact s.mem ws
  post s t :=
    let ws := s.gpr .r3
    let w := wOf s.mem ws
    let c := numAt s.mem ws w 0
    (∀ b, numAt s.mem ws w 5 = b % c * 2 ^ (64 * w) % c →
      ((t.gpr .r3).setWidth 32).toNat = if Proof.MillerRabin.Round.round c b then 1 else 0) ∧
      Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact ws (s.gpr .r4).toNat w s.mem t.mem
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      wOf s₁.mem (s₁.gpr .r3) = wOf s₂.mem (s₂.gpr .r3)

/-- A store to the scratch buffer leaves the working space. -/
theorem frame_outside {m m' : Mem} {B S : Addr} {Z : Nat} (hf : Frame [Save.savR S] m m')
    (hd : (⟨B, Z⟩ : Region).Disjoint (Save.savR S)) : Mont.Outside B Z (2 ^ 64) m m' := by
  intro x hx
  simp only [Mont.ofs] at hx
  refine hf x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr
  subst hr
  have := (x - B).isLt
  exact hd x (by simp only [Region.Contains]; omega_arith) hc

/-- The round leaves the scratch buffer. -/
theorem outs_scratch {m m' : Mem} {B S : Addr} {Z : Nat} {rs : List (Nat × Nat)} (h : Outs B rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ Z) (hd : (⟨B, Z⟩ : Region).Disjoint (Save.savR S)) {x : Addr}
    (hx : (Save.savR S).Contains x 1) : m' x = m x := by
  refine h x fun r hm => .inr ?_
  show r.1 + r.2 ≤ (x - B).toNat
  have := hr r hm
  by_contra hc
  exact hd x (by simp only [Region.Contains]; omega) hx

theorem roundRanges_le {w Z : Nat} (hZ : slot w 28 ≤ Z) : ∀ r ∈ roundRanges w, r.1 + r.2 ≤ Z := by
  have e : slot w 11 + 16 * (8 * (w + 2)) = slot w 27 := by simp only [slot]; omega_arith
  have h27 := slot_lt (w := w) (show 27 < 28 by decide)
  have l : ∀ j < 28, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_lt hj) hZ
  intro r hr
  simp only [roundRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h <;> rw [h]
  · exact l 2 (by decide)
  · exact l 3 (by decide)
  · exact l 5 (by decide)
  · exact l 6 (by decide)
  · show slot w 11 + 16 * (8 * (w + 2)) ≤ Z
    omega_arith

theorem shl1_ofNat (w : Nat) : BitVec.ofNat 64 w <<< 1 = BitVec.ofNat 64 (2 * w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.pow_one,
    Nat.mod_mul_mod, Nat.mul_comm]

theorem stride_ofNat (w : Nat) :
    BitVec.ofNat 64 w <<< 3 + BitVec.ofNat 64 16 = BitVec.ofNat 64 (8 * (w + 2)) := by
  rw [shl3_ofNat, ← BitVec.ofNat_add]
  congr 1

/-- The registers `setup` writes. -/
def setupRegs : List Reg := [.r10, .r11, .r12, .r29, .r31]

/-- `setup`: the working space's registers. -/
theorem setup_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (h3 : s.gpr .r3 = B)
    (hw : s.mem.readW (off B 48) 64 = BitVec.ofNat 64 w) (hw4 : 4 ≤ w) (hw' : w ≤ 128) (hZ : slot w 28 ≤ Z)
    (hinv : (w32 s.mem B (slot w 0) * w32 s.mem B 56 + 1) % 2 ^ 32 = 0) :
    WP isa (.block setup) s fun t => (MCtx t B Z w ∧ t.mem = s.mem) ∧ Keep setupRegs s t := by
  have h0 : slot w 0 = 256 := by simp [slot, Impl.Bignum.hdrBytes]
  have h28 : 256 ≤ slot w 28 := by simp only [slot, Impl.Bignum.hdrBytes]; omega_arith
  have hb : WP isa (.block setup) s fun t =>
      (t.gpr .r31 = B ∧ t.gpr .r10 = off B 256 ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧
        t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) ∧
        t.gpr .r12 = (s.mem.readW (off B 56) 32).setWidth 64 ∧ t.mem = s.mem) ∧ Keep setupRegs s t := by
    refine WP.keep _ ?_ (by decide)
    unfold setup
    prun [h3, hs.ld (show 48 + 8 ≤ Z by omega_arith), hs.ld (show 56 + 4 ≤ Z by omega_arith), sW, sMinv, hw,
      stride_ofNat, shl1_ofNat, Impl.Bignum.hdrBytes, BitVec.add_zero]
  refine WP.mono hb fun t ⟨⟨t31, t10, t11, t29, t12, tm⟩, k⟩ => ⟨⟨⟨⟨hs.congr k.wr, by rw [t10, h0], t29, t11, t31,
    hw4, hw', hZ⟩, ?_, ?_⟩, tm⟩, k⟩
  · rw [t12, BitVec.toNat_setWidth]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (BitVec.isLt _)
  · rw [t12, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)), tm]
    exact hinv

theorem ret_val (x : Bool) : ((BitVec.ofNat 64 1 &&& mask x).setWidth 32).toNat = if x then 1 else 0 := by
  cases x <;> decide

theorem pres_not_written : ∀ r ∈ preserved, (∀ i < 18, r ≠ Impl.MillerRabin.PPC64LE.saved i) →
    r ∉ setupRegs ++ coreRegs ++ ([.r3] : List Reg) ∧ r ≠ .r21 := by
  decide

theorem fn_correct (s : State) (h : fnContract.pre s) :
    ∃ tr t, Exec isa Impl.MillerRabin.PPC64LE.round s tr t ∧ abiPreserved s t ∧ fnContract.post s t := by
  obtain ⟨-, hwr, hdis, hnw, hL, hp⟩ := h
  have hsin : Save.savR (s.gpr .r5) ∈ s.wr := by rw [hwr]; simp
  show WP isa Impl.MillerRabin.PPC64LE.round s fun t => abiPreserved s t ∧ fnContract.post s t
  -- the layout and the prepared values
  dsimp only [Proof.MillerRabin.Round.Layout, Proof.MillerRabin.Round.compact] at hL
  obtain ⟨-, ⟨-, -, -, -⟩, h4, h128, hspace, -⟩ := hL
  dsimp only [Proof.MillerRabin.Round.Prepared, Proof.MillerRabin.Round.compact] at hp
  obtain ⟨h3, hodd, hinv, hx5, h9, h10, he, hl⟩ := hp
  simp only [wsR] at hdis
  generalize hBd : s.gpr .r3 = B at hdis hnw hspace h4 h128 h3 hodd hinv hx5 h9 h10 he hl
  generalize hZd : (s.gpr .r4).toNat * 8 = Z at hdis hnw
  generalize hwd : wOf s.mem B = w at hspace h4 h128 h3 hodd hinv hx5 h9 h10 he hl
  generalize hcd : numAt s.mem B w 0 = c at h3 hodd hx5 h9 h10 he hl
  have hZ : slot w 28 ≤ Z := by
    rw [← hZd]; change slot w 28 ≤ 8 * (s.gpr .r4).toNat at hspace; omega_arith
  have hs : Scr s B Z := Scr.of_mem (by rw [hwr, ← hBd, ← hZd]; simp) hnw
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  obtain ⟨b, -, hb⟩ := VG.Proof.MillerRabin.witness_exists hR hx5
  have sl : ∀ j < 28, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_lt hj) hZ
  unfold Impl.MillerRabin.PPC64LE.round
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Save.save_ok s hsin) fun s₁ hS => ?_
  have hout₁ := frame_outside (B := B) (Z := Z) hS.frame hdis
  have v₁ : ∀ {j}, j < 28 → val32 s₁.mem B (slot w j) (2 * w) = val32 s.mem B (slot w j) (2 * w) :=
    fun hj => hout₁.val32 (by have := sl _ hj; omega_arith) (by have := sl _ hj; omega_arith)
  have wd₁ : ∀ {d}, d + 8 ≤ Z → s₁.mem.readW (off B d) 64 = s.mem.readW (off B d) 64 :=
    fun hd => hout₁.word (by omega_arith) (by omega_arith)
  have h0 := slot_lt (w := w) (show 0 < 28 by decide)
  have h0' : slot w 0 = 256 := by simp [slot, Impl.Bignum.hdrBytes]
  refine WP.mono (setup_ok (hs.congr hS.keep.wr) (by rw [hS.keep.gpr .r3 (by decide), hBd])
    (by rw [wd₁ (by omega_arith), ← hwd]; simp [wOf, wordAt, Proof.Rsa.Mont.wWord])
    h4 h128 hZ (by
      rw [w32_eq_mod, w32_eq_mod]
      simp only [VG.Proof.Bignum.word]
      rw [wd₁ (by omega_arith), wd₁ (by omega_arith)]
      exact VG.Proof.Bignum.Minv32.minv_low hinv)) fun s₂ ⟨⟨hm2, m2⟩, k2⟩ => ?_
  have hc2 : Consts s₂.mem B w c := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [m2, show arr s₁.mem B w 0 = val32 s₁.mem B (slot w 0) (2 * w) from rfl, v₁ (by decide), ← numAt_eq,
        hcd]
    · rw [m2, show arr s₁.mem B w aOne = val32 s₁.mem B (slot w 9) (2 * w) from rfl, v₁ (by decide), ← numAt_eq]
      exact h9
    · rw [m2, show arr s₁.mem B w aMinus = val32 s₁.mem B (slot w 10) (2 * w) from rfl, v₁ (by decide),
        ← numAt_eq]
      exact h10
    · rw [m2, show arr s₁.mem B w aE = val32 s₁.mem B (slot w 27) (2 * w) from rfl, v₁ (by decide), ← numAt_eq]
      exact he
    · rw [m2]
      have := sl 27 (by decide)
      exact (wd₁ (d := slot w 27 + 8 * w) (by omega_arith)).trans hl
  have h52 : arr s₂.mem B w 5 = b % c * 2 ^ (64 * w) % c := by
    rw [m2, show arr s₁.mem B w 5 = val32 s₁.mem B (slot w 5) (2 * w) from rfl, v₁ (by decide), ← numAt_eq]
    exact hb
  refine WP.seq (WP.mono (core_ok hm2 hc2 h3 hodd h52) fun t ⟨_, t23, tmut, kt⟩ => ?_)
  rw [WP.block_append_iff]
  have hret : WP isa (.block [.li .r3 1, .logic .and .r3 .r3 .r23]) t fun t' =>
      (t'.gpr .r3 = BitVec.ofNat 64 1 &&& mask (Proof.MillerRabin.Round.round c b) ∧ t'.mem = t.mem) ∧ Keep [.r3] t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [t23]
  refine WP.mono hret fun t₃ ⟨⟨r3v, m3⟩, k3⟩ => ?_
  have kall := ((hS.keep.trans k2).trans kt).trans k3
  -- the registers back
  have hsav : ∀ i < 18, t₃.mem.readW (off (s.gpr .r5) (8 * i)) 64 = s.gpr (Impl.MillerRabin.PPC64LE.saved i) :=
      fun i hi => by
    rw [← hS.saved i hi, m3]
    exact Mem.readW_congr fun k hk => (outs_scratch tmut (roundRanges_le hZ) hdis
      (Region.Contains.byte (Save.sav_contains _ hi) (by
        rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; omega_arith))).trans (by rw [m2])
  have k23 := (k2.trans kt).trans k3
  refine WP.mono (Save.restore_ok t₃ ((k23.gpr .r21 (by decide)).trans hS.r21)
    (by rw [kall.wr]; exact hsin) hsav) fun u ⟨urs, uot, um, _, _, usp, ulr⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [usp, kall.sp], by rw [ulr, kall.lr]⟩, ?_, ?_⟩
  · by_cases hs' : ∃ i < 18, r = Impl.MillerRabin.PPC64LE.saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 18, r ≠ Impl.MillerRabin.PPC64LE.saved i := fun i hi e => hs' ⟨i, hi, e⟩
      obtain ⟨h1, h2⟩ := pres_not_written r hr hn
      rw [uot r hn, k23.gpr r h1, hS.keep.gpr r (by simpa using h2)]
  · intro b' hb'
    rw [uot .r3 (by decide), r3v, ret_val]
    rw [hBd, hwd, hcd] at hb'
    rw [hBd, hwd, hcd, VG.Proof.MillerRabin.round_eq_of_mont (b' := b') (by omega_arith) hR (hb.symm.trans hb')]
  · intro i hi hh ha ht
    simp only [hBd, hwd] at ha ht ⊢
    have hi' : i < Z := by rw [← hZd]; omega_arith
    have hofs : Mont.ofs B (B + BitVec.ofNat 64 i) = i := by
      show (B + BitVec.ofNat 64 i - B).toNat = i
      rw [Mem.sub_ofNat_toNat _ (by omega_arith)]
    rw [um, m3, tmut _ fun r hr => ?_, m2, hout₁ _ (by rw [hofs]; omega_arith)]
    simp only [roundRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hofs]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ha 2 (by simp)
    · exact ha 3 (by simp)
    · exact ha 5 (by simp)
    · exact ha 6 (by simp)
    · have e : slot w 11 + 16 * (8 * (w + 2)) = arrAt w (11 + 16) := by
        simp only [slot, arrAt, Impl.Bignum.hdrBytes, Proof.Rsa.Mont.hdrBytes]; omega_arith
      rw [e]; exact ht

end VG.Proof.MillerRabin.PPC64LE
