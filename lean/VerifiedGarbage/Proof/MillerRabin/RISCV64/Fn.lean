module

-- separate module: the function, which the round's `Verified` imports with the core's proof; the core's modules import only `Ctx`
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Ctx
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MillerRabin.Representation
import VerifiedGarbage.Proof.Bignum.PackedRead
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The Miller–Rabin round on RISC-V: the function

`vg_miller_rabin_round(ws = a0, ws_len = a1)`, from the shared contract's
precondition with the 96 bytes of stack of its frame (`PreR`, `preR_of`):
`round` allocates the frame, saves the callee-saved registers in it (`save`),
sets up the working space's registers (`setup_ok`), runs the round's core
(`CoreOk`, proven of `core` in `Core.lean`), and restores them
(`fn_correct`), with the result and what the working space keeps (`fnPost`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.MillerRabin.RISCV64
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot slot_sep Arrays)
open VG.Proof.Rsa.Mont (numAt wOf wordAt arrAt)
open VG.Proof.MillerRabin.Round (compact Layout Prepared Keeps roundContract)

/-! ## The precondition -/

/-- The working space: `ws_len` words at `a0`. -/
abbrev wsR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat * 8⟩

/-- The frame's base, and the frame. -/
abbrev fb (s : State) : Addr := s.sp - BitVec.ofNat 64 frameBytes
abbrev kR (s : State) : Region := ⟨fb s, frameBytes⟩

/-- What the code needs of `roundContract.pre`, by name. -/
structure PreR (s : State) : Prop where
  sp16 : s.sp.toNat % 16 = 0
  sp1 : frameBytes ≤ s.sp.toNat
  hrd : s.rd = []
  hwr : s.wr = [wsR s]
  kw : (kR s).Disjoint (wsR s)
  nw : (s.gpr .a0).toNat + (s.gpr .a1).toNat * 8 ≤ 2 ^ 64
  lay : Layout compact s.mem (s.gpr .a0) (s.gpr .a1).toNat
  prep : Prepared compact s.mem (s.gpr .a0)
  al : (s.gpr .a0).toNat % 8 = 0

theorem preR_of {s : State} (h : (roundContract RISCV64.abi compact frameBytes).pre s) : PreR s := by
  have e : frameBytes = 95 + 1 := rfl
  rw [e] at h
  sig_pre [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, RISCV64.abi,
    RISCV64.argRegs] at h
  obtain ⟨sp16, sp1, hrd, hwr, kw, nw, lay, prep, al⟩ := h
  exact ⟨sp16, sp1, hrd, hwr, kw, nw, lay, prep, al⟩

/-! ## The frame -/

/-- The callee-saved registers and their slots. -/
def savedL : List (Reg × Nat) := Spill.slots saved 12

theorem save_eq : save = Spill.saveCode .t2 savedL := rfl

theorem restore_eq : restore = .addSp .t2 0 :: Spill.restoreCode .t2 savedL := rfl

theorem savedL_fits : Spill.Fits savedL := by decide

theorem savedL_restorable : Spill.Restorable .t2 savedL := by decide

theorem savedL_le : ∀ p ∈ savedL, p.2 + 8 ≤ frameBytes := by decide

theorem savedL_saved : ∀ r ∈ preserved, (r, 8 * (preserved.idxOf r)) ∈ savedL := by decide

theorem savedL_t2 : ∀ p ∈ savedL, p.1 ≠ .t2 := by decide

/-- Memory that changes only in a region apart from the working space keeps
it. -/
theorem frame_outside {m m' : Mem} {B K : Addr} {Z n : Nat} (hf : Frame [⟨K, n⟩] m m')
    (hd : (⟨K, n⟩ : Region).Disjoint ⟨B, Z⟩) : Outside B Z (2 ^ 64) m m' := by
  intro x hx
  refine hf x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr
  subst hr
  have := (x - B).isLt
  exact hd x hc (by simp only [Region.Contains]; simp only [ofs] at hx; omega_arith)

/-- Changes only in arrays within the working space are within it. -/
theorem Arrays.frame {B : Addr} {w Z : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    (hjs : ∀ j ∈ js, slot w j + 8 * (w + 2) ≤ Z) : Frame [⟨B, Z⟩] m m' := by
  intro x hx
  refine h x fun j hj => .inr ?_
  have hc := hx _ (List.mem_singleton_self _)
  have := hjs j hj
  simp only [Region.Contains] at hc
  show slot w j + 8 * (w + 2) ≤ (x - B).toNat
  omega_arith

theorem mut_le {w Z : Nat} (hZ : slot w 28 ≤ Z) : ∀ j ∈ mutArrs, slot w j + 8 * (w + 2) ≤ Z := by
  intro j hj
  have : j < 28 := by simp only [mutArrs, List.mem_cons, List.not_mem_nil, or_false] at hj; omega_arith
  exact Nat.le_trans (slot_lt this) hZ

/-! ## The core -/

/-- The registers the round's core may write: all but `ctxRegs`, `ra`, `sp`,
`gp` and `tp`. -/
def coreRegs : List Reg :=
  [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4, .s6, .s7, .s8, .s9,
    .s10, .s11]

/-- What the core does (`Core.lean`'s `core_ok`). -/
def CoreOk : Prop :=
  ∀ {s : State} {B : Addr} {Z w c b : Nat}, MCtx s B Z w c → Consts s.mem B w c → 3 ≤ c → c % 2 = 1 →
    A s.mem B w 5 = b % c * 2 ^ (64 * w) % c →
    WP isa core s fun t => MCtx t B Z w c ∧ t.gpr .s6 = mask (Proof.MillerRabin.Round.round c b) ∧
      Mut B w s.mem t.mem ∧ Keep coreRegs s t

/-! ## The function -/

/-- The shared contract's postcondition on the registers. -/
def fnPost (s t : State) : Prop :=
  let ws := s.gpr .a0
  let w := wOf s.mem ws
  let c := numAt s.mem ws w 0
  (∀ b, numAt s.mem ws w 5 = b % c * 2 ^ (64 * w) % c →
    ((t.gpr .a0).setWidth 32).toNat = if Proof.MillerRabin.Round.round c b then 1 else 0) ∧
    Keeps compact ws (s.gpr .a1).toNat w s.mem t.mem

theorem ret_val (x : Bool) : ((BitVec.ofNat 64 1 &&& mask x).setWidth 32).toNat = if x then 1 else 0 := by
  cases x <;> decide

theorem numAt_A (m : Mem) (B : Addr) (w j : Nat) : numAt m B w j = A m B w j :=
  (VG.Proof.Bignum.wordsVal_read m B (slot w j) w).symm

theorem fn_correct (hcore : CoreOk) (s : State) (hpre : (roundContract RISCV64.abi compact frameBytes).pre s) :
    ∃ tr t, Exec isa Impl.MillerRabin.RISCV64.round s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  show WP isa Impl.MillerRabin.RISCV64.round s fun t => abiPreserved s t ∧ fnPost s t
  have h := preR_of hpre
  -- the layout and the prepared values
  have hL := h.lay
  dsimp only [Layout, compact] at hL
  obtain ⟨-, ⟨-, -, -, -⟩, h4, h128, hspace, -⟩ := hL
  have hp := h.prep
  dsimp only [Prepared, compact] at hp
  obtain ⟨h3, hodd, hinv, hx5, h9, h10, he, hl⟩ := hp
  have hkw := h.kw
  have hnw := h.nw
  generalize hBd : s.gpr .a0 = B at hkw hnw hspace h4 h128 h3 hodd hinv hx5 h9 h10 he hl
  generalize hZd : (s.gpr .a1).toNat * 8 = Z at hkw hnw
  generalize hwd : wOf s.mem B = w at hspace h4 h128 h3 hodd hinv hx5 h9 h10 he hl
  generalize hcd : numAt s.mem B w 0 = c at h3 hodd hx5 h9 h10 he hl
  have hZ64 : Z ≤ 2 ^ 64 := by omega_using [hnw]
  have hZ : slot w 28 ≤ Z := by
    rw [show max (11 + 16) (max (27 + 1) (max (9 + 1) (10 + 1))) = 28 from rfl] at hspace
    change slot w 28 ≤ 8 * (s.gpr .a1).toNat at hspace
    rw [← hZd]; omega_using [hspace]
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  obtain ⟨b, -, hb⟩ := VG.Proof.MillerRabin.witness_exists hR hx5
  have sl : ∀ j < 28, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_lt hj) hZ
  -- the frame
  unfold Impl.MillerRabin.RISCV64.round Impl.StackScratch.RISCV64.withStackScratch
  refine WP.alloc ⟨by decide, by decide, by decide⟩ h.sp1 ?_
  refine WP.seq (WP.block_cons_iff.mpr ⟨_, exec_addSp (imm := 0) (by decide), WP.block_nil ?_⟩)
  generalize hs0 : (allocd frameBytes s).write .t2 ((allocd frameBytes s).sp + BitVec.ofNat 64 0) = s₀
  have g0 : ∀ r, r ≠ .t2 → s₀.gpr r = s.gpr r := fun r hr => by
    rw [← hs0, gpr_write_of_ne _ _ hr]; rfl
  have t20 : s₀.gpr .t2 = fb s := by
    rw [← hs0, gpr_write_self]; simp only [allocd, BitVec.add_zero]
  have m0 : s₀.mem = s.mem := by rw [← hs0]; rfl
  have w0 : s₀.wr = kR s :: [wsR s] := by rw [← hs0, ← h.hwr]; rfl
  have sp0 : s₀.sp = fb s := by rw [← hs0]; rfl
  have rd0 : s₀.rd = [] := by rw [← hs0, ← h.hrd]; rfl
  have hsp : 96 ≤ s.sp.toNat := h.sp1
  have hal16 := h.sp16
  have fbN : (fb s).toNat = s.sp.toNat - 96 := by
    simp only [fb, frameBytes]; rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith)]
    simp only [BitVec.toNat_ofNat]
  have fbal : (fb s).toNat % 8 = 0 := by rw [fbN]; omega_arith
  -- the saves
  refine WP.seq ?_
  rw [save_eq]
  refine Spill.save_ok (b := .t2) (l := savedL) (by rw [t20]; exact fbal)
    (fun p hp => ⟨by have := savedL_fits.1 p hp; exact this.1, by have := savedL_fits.1 p hp; exact this.2⟩)
    (fun p hp => by
      rw [w0, t20]
      exact ⟨kR s, List.mem_cons_self .., Offset.contains_base _ (savedL_le p hp)
        (by have := savedL_le p hp; unfold frameBytes at this; omega_arith)⟩) ?_
  generalize hs1 : ({ s₀ with mem := Spill.saveMem s₀.mem (s₀.gpr .t2) s₀.gpr savedL } : State) = s₁
  have f1 : Frame [kR s] s.mem s₁.mem := by
    rw [← hs1, ← m0, t20]
    exact Spill.saveMem_frame_base savedL_le (by decide) _ _ _
  have sv1 : Spill.Saved (fb s) s₀.gpr savedL s₁.mem := by
    rw [← hs1, t20]; exact Spill.saveMem_saved savedL_fits _ _ _
  have o1 : Outside B Z (2 ^ 64) s.mem s₁.mem :=
    frame_outside f1 (by rw [← hBd, ← hZd]; exact hkw)
  have g1 : s₁.gpr = s₀.gpr := by rw [← hs1]
  have w1 : s₁.wr = s₀.wr := by rw [← hs1]
  have hs : Scr s₁ B Z := Scr.of_mem (by rw [w1, w0, ← hBd, ← hZd]; simp) hnw (by rw [← hBd]; exact h.al)
  have v1 : ∀ {j}, j < 28 → A s₁.mem B w j = A s.mem B w j := fun {j} hj => by
    have := sl j hj
    exact o1.wordsVal (.inl (by omega_using [this])) (by omega_using [this, hZ64])
  have wd1 : ∀ {d}, d + 8 ≤ Z → Mont.word s₁.mem B d = Mont.word s.mem B d :=
    fun hd => o1.word (.inl hd) (by omega_using [hd, hZ64])
  have h0 := slot_lt (w := w) (show 0 < 28 by decide)
  have h0' : slot w 0 = 256 := by simp [slot, Impl.Bignum.hdrBytes]
  -- the registers
  refine WP.mono (WP.rdwr (setup_ok (N := c) hs (by rw [g1, g0 _ (by decide), hBd])
    (by
      rw [wd1 (d := 8 * sW) (by simp only [sW]; omega_using [h0, h0', hZ]), ← hwd]
      simp only [wOf, wordAt, Proof.Rsa.Mont.wWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rfl)
    h4 h128 hZ (by
      rw [wd1 (d := slot w 0) (by omega_using [h0, sl 0 (by decide)]),
        wd1 (d := 8 * sMinv) (by simp only [sMinv]; omega_using [h0, h0', hZ])]
      exact hinv)
    (by rw [v1 (by decide), ← numAt_A, hcd]))) fun s₂ ⟨⟨⟨hm2, m2⟩, k2⟩, _, w2, sp2⟩ => ?_
  have hc2 : Consts s₂.mem B w c := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [m2, v1 (by decide), ← numAt_A]; exact h9
    · rw [m2, v1 (by decide), ← numAt_A]; exact h10
    · rw [m2, v1 (by decide), ← numAt_A]; exact he
    · rw [m2]
      have := sl 27 (by decide)
      exact (wd1 (d := slot w 27 + 8 * w) (by omega_arith)).trans hl
  have h52 : A s₂.mem B w 5 = b % c * 2 ^ (64 * w) % c := by
    rw [m2, v1 (by decide), ← numAt_A]; exact hb
  -- the core
  refine WP.seq (WP.mono (WP.rdwr (hcore hm2 hc2 h3 hodd h52)) fun t ⟨⟨_, t6, tmut, kt⟩, _, twr, tsp⟩ => ?_)
  -- the result
  rw [WP.block_append_iff]
  have hret : WP isa (.block [.li .a0 1, .logic .and .a0 .a0 .s6]) t fun t' =>
      (t'.gpr .a0 = BitVec.ofNat 64 1 &&& mask (Proof.MillerRabin.Round.round c b) ∧ t'.mem = t.mem) ∧
        Keep [.a0] t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li (show imm12 1 by decide), t6]
  refine WP.mono (WP.rdwr hret) fun t₃ ⟨⟨⟨r0, m3⟩, k3⟩, _, w3, sp3⟩ => ?_
  -- the restores
  have spt : t₃.sp = fb s := by rw [sp3, tsp, sp2, ← hs1]; exact sp0
  have wrt : t₃.wr = kR s :: [wsR s] := by rw [w3, twr, w2, w1, w0]
  have mt : Frame [⟨B, Z⟩] s₁.mem t₃.mem := by
    rw [m3, ← m2]; exact Arrays.frame tmut (mut_le hZ)
  have hsv : Spill.Saved (fb s) s₀.gpr savedL t₃.mem :=
    Spill.Saved.frame_in (lo := 0) (n := frameBytes) sv1 (fun p hp => ⟨Nat.zero_le _, savedL_le p hp⟩) mt
      (fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        rw [BitVec.add_zero, ← hBd, ← hZd]
        exact h.kw)
  rw [restore_eq]
  refine WP.block_cons_iff.mpr ⟨_, exec_addSp (imm := 0) (by decide), ?_⟩
  refine WP.mono (Spill.restore_wp (b := .t2) (B := fb s) fbal
    (by rw [gpr_write_self, spt, BitVec.add_zero])
    (fun p hp => savedL_fits.1 p hp) savedL_restorable
    (fun p hp => by
      rw [rd_write, wr_write, wrt]
      exact ⟨kR s, List.mem_append_right _ (List.mem_cons_self ..), Offset.contains_base _ (savedL_le p hp)
        (by have := savedL_le p hp; unfold frameBytes at this; omega_arith)⟩)
    (by rw [mem_write]; exact hsv)) fun u R => ?_
  have uother : ∀ r, r ∉ savedL.map Prod.fst → r ≠ .t2 → u.gpr r = t₃.gpr r := fun r hr h2 => by
    rw [R.other r hr, gpr_write_of_ne _ _ h2]
  have usp : u.sp = fb s := by rw [R.sp, sp_write, spt]
  have um : u.mem = t₃.mem := by rw [R.mem, mem_write]
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · show u.gpr r = s.gpr r
    have hp := savedL_saved r hr
    rw [R.gpr _ hp]
    exact g0 r (savedL_t2 _ hp)
  · show u.sp + BitVec.ofNat 64 frameBytes = s.sp
    rw [usp]; exact BitVec.sub_add_cancel _ _
  · show u.gpr .ra = s.gpr .ra
    rw [uother .ra (by decide) (by decide), k3.gpr (by decide), kt.gpr (by decide), k2.gpr (by decide), g1,
      g0 _ (by decide)]
  · intro b' hb'
    show ((u.gpr .a0).setWidth 32).toNat = _
    rw [uother .a0 (by decide) (by decide), r0, ret_val]
    rw [hBd, hwd, hcd] at hb'
    rw [hBd, hwd, hcd, VG.Proof.MillerRabin.round_eq_of_mont (b' := b') (by omega_arith) hR (hb.symm.trans hb')]
  · intro i hi hh ha ht
    show u.mem _ = _
    simp only [hBd, hwd] at ha ht ⊢
    have hi' : i < Z := by rw [← hZd]; omega_arith
    have hofs : VG.Proof.Bignum.ofs B (B + BitVec.ofNat 64 i) = i := by
      show (B + BitVec.ofNat 64 i - B).toNat = i
      rw [Mem.sub_ofNat_toNat _ (by omega_arith)]
    rw [um, m3, tmut _ fun j hj => ?_, m2]
    · refine f1 _ fun r hr hc => ?_
      simp only [List.mem_singleton] at hr
      subst hr
      exact h.kw _ hc (by
        simp only [Region.Contains, hBd, hZd]
        rw [Mem.sub_ofNat_toNat _ (by omega_arith)]
        omega_arith)
    · rw [hofs]
      simp only [mutArrs, List.mem_cons, List.not_mem_nil, or_false] at hj
      dsimp only [compact] at ha ht
      have h2 := ha 2 (by simp)
      have h3' := ha 3 (by simp)
      have h5 := ha 5 (by simp)
      have h6 := ha 6 (by simp)
      simp only [arrAt, slot, Proof.Rsa.Mont.hdrBytes, Impl.Bignum.hdrBytes] at h2 h3' h5 h6 ht ⊢
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;> omega_arith

end VG.Proof.MillerRabin.RISCV64
