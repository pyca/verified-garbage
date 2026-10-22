module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.SelWeave
public import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardFieldI
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacLay
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacSelect
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJP
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem

/-!
# The odd window method on x86-64: the selection woven into the addition

What the selection of digit `j - 1`'s entry keeps between the addition's
field operations (`SelP`): the broadcasts of its magnitude `a` and of one,
the counter and the accumulators after entries `1 … e` (`SelS`: 32 bytes at
a time with AVX2, `AccY`, else 16, `AccX`), of the table at `rdi + tbl` as
in the memory `mem` it started from, whose bytes the state still holds. The
field operations keep it (`SelP.stab`), writing neither the vector registers
nor the table; each part of the selection advances it (`selChunkO_ok`),
writing no register but `rdx` (`SideKeepF`); `selSetP_ok` starts it and
`storeP_ok` stores the accumulators to `T`, which then holds entry `a`
(`jselOut`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

variable {K : JacWinCfg} {size : Nat}

/-- The table's address. -/
abbrev tblX (K : JacWinCfg) (base : Addr) : Addr := base + BitVec.ofNat 64 K.tbl

/-- The selection's registers for the window method's five coordinates
(`SelSW`). -/
abbrev SelS (K : JacWinCfg) (base : Addr) (mem : Mem) (a e : Nat) (t : State) : Prop :=
  SelSW K.avx2 (tblX K base) K.st K.np16 mem a e t

/-- The selection between the addition's operations (`SelW`). -/
abbrev SelP (K : JacWinCfg) (base : Addr) (mem : Mem) (a e : Nat) (t : State) : Prop :=
  SelW K.avx2 K.tbl K.st K.np16 base mem a e t

/-- The table's entries: `16 st = 80 (8 n)` bytes. -/
theorem st16 (K : JacWinCfg) : 16 * K.st = 80 * (8 * K.M.n) := by
  unfold JacWinCfg.st; omega

/-- A range apart from the table's 80 slots is apart from each of its bytes. -/
theorem tbl_byte_apart (hL : JacWinLay K size) {w : Nat × Nat}
    (hw : ∀ i < 80, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i) {b : Nat} (hb : b < 16 * K.st) :
    K.tbl + b + 1 ≤ w.1 ∨ w.1 + w.2 ≤ K.tbl + b := by
  have h0 := hL.n0
  rw [st16] at hb
  have hi : b / (8 * K.M.n) < 80 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [Nat.mul_comm]; omega)
  have h1 := Nat.div_mul_le_self b (8 * K.M.n)
  have h2 := Nat.lt_div_mul_add (a := b) (show 0 < 8 * K.M.n by omega)
  have := hw _ hi
  unfold jg at this
  rw [Nat.mul_comm (8 * K.M.n)] at this
  generalize b / (8 * K.M.n) * (8 * K.M.n) = q at h1 h2 this
  omega

/-- Byte `b` of the table: `off base (tbl + b)`. -/
theorem tblX_off (K : JacWinCfg) (base : Addr) (b : Nat) :
    tblX K base + BitVec.ofNat 64 b = off base (K.tbl + b) := Offset.add_add base _ _

/-- The table's bytes survive a write that misses its slots. -/
theorem tblm_unch (hL : JacWinLay K size) {base : Addr} {W : List (Nat × Nat)} {m m' : Mem}
    (hU : Unch base W m m') (hn : base.toNat + size ≤ 2 ^ 64)
    (hW : ∀ w ∈ W, ∀ i < 80, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i) :
    ∀ b < 16 * K.st, m' (tblX K base + BitVec.ofNat 64 b) = m (tblX K base + BitVec.ofNat 64 b) := by
  intro b hb
  have hg := hL.grid_le
  have := st16 K
  rw [tblX_off]
  exact hU.byte (fun w hw => tbl_byte_apart hL (hW w hw) hb) (by omega)

/-- A slot but the grid's, and the temporary area, miss the table's slots. -/
theorem other_tbl_apart (hL : JacWinLay K size) {o : Nat} (ho : o ∈ jwOther K) :
    ∀ w ∈ [(o, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)], ∀ i < 80, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i := by
  intro w hw i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact (hL.jg_apart (List.mem_append_right _ ho) (i := i) (by omega)).symm
  · exact hL.lay.tmp _ (jg_mem (by omega))

/-- A field operation writing a slot but the grid's keeps the selection
(`programBI_ok`'s `hstab`). -/
theorem SelP.stab (hL : JacWinLay K size) {base : Addr} {mem : Mem} {a e o : Nat} (ho : o ∈ jwOther K)
    (hn : base.toNat + size ≤ 2 ^ 64) {t t' : State} (h : SelP K base mem a e t)
    (hk : OpKeep K.M base o t t') (hx : t'.xmm = t.xmm) (hy : t'.ymmHi = t.ymmHi) :
    SelP K base mem a e t' := by
  have hg := hL.grid_le
  have := st16 K
  exact SelW.stab h hk.unch (fun w hw b hb => tbl_byte_apart hL (other_tbl_apart hL ho w hw) hb) (by omega)
    hx hy hk.rd hk.wr (hk.gpr _ (rdi_not_clob _))

/-- An entry's pieces: ten for four words. -/
theorem np_four (hL : JacWinLay K size) (hn4 : K.M.n = 4) :
    K.np16 = 10 ∧ K.np32 = 5 ∧ K.st = 16 * K.np16 := by
  obtain ⟨-, hst, -⟩ := np16_eq hL
  unfold JacWinCfg.np32 JacWinCfg.np16 at *
  rw [hn4] at *
  exact ⟨rfl, rfl, hst⟩

theorem chunkO_le (K : JacWinCfg) {i : Nat} (hi : i < K.nAddO) :
    K.chunkO i ≤ K.chunkO (i + 1) ∧ K.chunkO (i + 1) ≤ 16 := chunkW_le hi

theorem np_bounds (hL : JacWinLay K size) (hn4 : K.M.n = 4) : 2 ≤ K.np16 ∧ K.np16 ≤ 10 := by
  have := (np_four hL hn4).1; omega

/-- A part of the selection (`programBI_ok`'s `hside`): from entry
`chunkO i` to `chunkO (i + 1)`. -/
theorem selChunkO_ok (hL : JacWinLay K size) (hn4 : K.M.n = 4) {base : Addr} {mem : Mem} {a : Nat} (i : Nat)
    (hi : i < K.nAddO) {t : State} (h : SelP K base mem a (K.chunkO i) t) :
    WP isa (.block (K.selChunkO i)) t fun t' => SelP K base mem a (K.chunkO (i + 1)) t' ∧
      ForwardField.SideKeepF t t' := by
  obtain ⟨h10, -, hst⟩ := np_four hL hn4
  have := st16 K
  exact selChunkW_ok (np_bounds hL hn4) (by omega) hL.tbl31 (by rw [this, hn4]; decide) i hi h

/-- The selection set up for the magnitude `r8 = a ≤ 16`, through `rcx`: no
entry kept yet, of any table. -/
theorem selSetP_ok (hL : JacWinLay K size) (hn4 : K.M.n = 4) (s : State) {base : Addr} (mem : Mem) {a : Nat}
    (ha : a ≤ 16) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) :
    WP isa (.block K.selSetP) s fun t => SelS K base mem a 0 t ∧ Keeps [.rcx] s t :=
  selSetW_ok (np_bounds hL hn4) s _ _ mem ha h8

/-- The accumulators after the sixteen entries stored to `T`. -/
theorem storeP_ok (hL : JacWinLay K size) (hn4 : K.M.n = 4) {base : Addr} {mem : Mem} {a : Nat} {t : State}
    (hs : Scr t base size) (h : SelS K base mem a 16 t) :
    WP isa (.block K.storeP) t fun t' =>
      (∀ c < K.np16, t'.mem.readW (off base (K.T + 16 * c)) 128 = accVal mem (tblX K base) K.st (16 * ·) a 16 c) ∧
      Outside base K.T (16 * K.np16) t.mem t'.mem ∧ t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain ⟨h10, h5, hst⟩ := np_four hL hn4
  have hT : K.T + 16 * K.np16 ≤ size := by
    have := hL.grid_le; rw [hL.T80]; unfold jg; rw [h10, hn4] at *; omega
  exact storeW_ok (np_bounds hL hn4) hs hT h

/-- `T`'s five coordinates after `storeP_ok`: entry `a`'s, as in `mem`. -/
theorem jselOut (hL : JacWinLay K size) (hn4 : K.M.n = 4) {base : Addr} {mem mem' : Mem} {a : Nat}
    (ha : 1 ≤ a ∧ a ≤ 16)
    (h : ∀ c < K.np16, mem'.readW (off base (K.T + 16 * c)) 128 = accVal mem (tblX K base) K.st (16 * ·) a 16 c) :
    ∀ c < 5, wordsVal mem' base (jg K (80 + c)) K.M.n = wordsVal mem base (jg K (5 * (a - 1) + c)) K.M.n := by
  obtain ⟨h10, -, hst⟩ := np_four hL hn4
  intro c hc
  rw [hst] at h
  have hw := accVal_word (mem := mem) (mem' := mem') (base := base) (n := K.np16) (o := K.T) h
  have hX : ∀ d, word mem (tblX K base) d = word mem base (K.tbl + d) := fun d => by
    rw [Mont.word, Mont.word, off, off, Offset.add_add]
  have h2n : 2 * K.np16 = 5 * K.M.n := by rw [h10, hn4]
  have hcn := Nat.mul_le_mul_left K.M.n (show c + 1 ≤ 5 by omega)
  rw [Nat.mul_succ] at hcn
  have eT : ∀ i, jg K (80 + c) + 8 * i = K.T + 8 * (K.M.n * c + i) := fun i => by
    rw [hL.T80]; unfold jg; rw [Nat.mul_add, Nat.mul_add, Nat.mul_assoc 8 K.M.n c]; omega
  refine wordsVal_congr₂ _ _ _ fun i hi => ?_
  have e := hw (K.M.n * c + i) (by omega)
  rw [ite_eq_left_of_eq_true _ _ (eq_true ha), hX] at e
  rw [eT, e, ← hst]
  congr 1; unfold jg JacWinCfg.st
  rw [show 40 * K.M.n * (a - 1) = 8 * K.M.n * (5 * (a - 1)) by
    rw [Nat.mul_assoc, Nat.mul_assoc, show 40 = 8 * 5 from rfl, Nat.mul_assoc, Nat.mul_left_comm 5],
    Nat.mul_add (8 * K.M.n), Nat.mul_assoc 8 K.M.n c]
  omega

end VG.Proof.Weierstrass.X86_64
