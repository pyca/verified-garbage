module

public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Finish
meta import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Finish
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCorrect
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCorrect
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.Spec
public import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Common
meta import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Common
public import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.Cmac.Block
public import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.AbsorbBlocks
meta import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.AbsorbBlocks

/-! ### `CmacAes.Stream.AArch64.Verified`, which only this module used -/

section

/-! ### `CmacAes.Stream.AArch64.AbsorbCorrect`, which only this module used -/

section

@[expose] public section

section

/-!
# Streaming AES-CMAC on AArch64: `vg_cmac_aes_absorb` up to the first call

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 16 - h)` bytes after them, and sets up the first call of
`vg_cmac_aes_update`, which chains the block held back if data is left
(`AMid₁`).
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.Stream.AArch64 VG.WriteBytes
open VG.Proof.Cmac.Stream (held held_le)

/-- The working space of the functions called, after the saved registers. -/
theorem scrC (S : Addr) (N : Nat) : Region.Sub ⟨S + BitVec.ofNat 64 64, N⟩ ⟨S, 64 + N⟩ :=
  Offset.sub_base S (Nat.le_refl _)

/-- The slots of the saved registers. -/
theorem scrS (S : Addr) (N : Nat) : Region.Sub ⟨S + BitVec.ofNat 64 8, 56⟩ ⟨S, 64 + N⟩ :=
  Offset.sub_base S (by omega_using [])

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`,
the scratch buffer `S` (`64 + N` bytes, for a chaining implementation that
needs `N`) and the rounds `R`. -/
structure APre (N : Nat) (s₀ : State) (St D S : Addr) (L R : Nat) : Prop where
  x0 : s₀.gpr .x0 = St
  x3 : s₀.gpr .x3 = D
  x4 : (s₀.gpr .x4).toNat = L
  x5 : s₀.gpr .x5 = S
  x1 : (s₀.gpr .x1).toNat = R
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 64 + N⟩]
  st_d : (⟨St, 304⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 64 + N⟩
  d_s : (⟨D, L⟩ : Region).Disjoint ⟨S, 64 + N⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : S.toNat + (64 + N) ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hN : N ≤ 2176

theorem APre.of {N : Nat} {s₀ : State} (h : (absorbAArch64 (64 + N)).pre s₀) (hN : N ≤ 2176) :
    APre N s₀ (s₀.gpr .x0) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, hN⟩

section
variable {N : Nat} {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre N s₀ St D S L R)
include hp

theorem APre.lt : L < 2 ^ 64 := by rw [← hp.x4]; exact BitVec.isLt _

theorem APre.x4' : s₀.gpr .x4 = BitVec.ofNat 64 L := ofNat_toNat_eq hp.x4

theorem APre.x1' : s₀.gpr .x1 = BitVec.ofNat 64 R := ofNat_toNat_eq hp.x1

theorem APre.inSt {d n : Nat} (h : d + n ≤ 304) : InRegions s₀.wr (St + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ h (by have := hp.wSt; omega_using [h])⟩

theorem APre.inS {d n : Nat} (h : d + n ≤ 64 + N) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨S, 64 + N⟩, by simp, Offset.contains_base _ h (by have := hp.hN; omega_using [h, this])⟩


theorem APre.wC : (S + BitVec.ofNat 64 64).toNat + N ≤ 2 ^ 64 := by
  have hw := hp.wS
  rcases Nat.eq_zero_or_pos N with h | h
  · rw [h]; have := (S + BitVec.ofNat 64 64).isLt; omega_using [this]
  · rw [toNat_add_lt S hw (by omega_using [h])]; omega_using [hw]

/-- The slots lie below the working space of the functions called. -/
theorem APre.sDisj : Region.Disjoint ⟨S + BitVec.ofNat 64 8, 56⟩ ⟨S + BitVec.ofNat 64 64, N⟩ :=
  Offset.disjoint S (Or.inl (by omega_using [])) (by omega_using []) (by have := hp.hN; omega_using [this])

theorem APre.inD {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ h (by have := hp.lt; omega_using [h, this])⟩

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the permissions of `s₀`. -/
theorem APre.uargs {s : State} {Dd : Addr} {n : Nat} (hx0 : s.gpr .x0 = St)
    (hx1 : s.gpr .x1 = s₀.gpr .x1) (hx2 : s.gpr .x2 = St + BitVec.ofNat 64 272) (hx3 : s.gpr .x3 = Dd)
    (hx4 : s.gpr .x4 = BitVec.ofNat 64 n) (hx5 : s.gpr .x5 = S + BitVec.ofNat 64 64)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 16 * n < 2 ^ 64)
    (hdc : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 64, N⟩) (hwrap : Dd.toNat + 16 * n ≤ 2 ^ 64)
    (hcov : ∃ r' ∈ ([⟨D, L⟩, ⟨St, 304⟩, ⟨S, 64 + N⟩] : List Region), ∃ off, Dd = r'.base + BitVec.ofNat 64 off ∧
      off + 16 * n ≤ r'.len) :
    UArgsW N s St (St + BitVec.ofNat 64 272) Dd (S + BitVec.ofNat 64 64) R n := by
  have hw := hp.wSt
  obtain c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  exact
  { x0 := hx0, x2 := hx2, x3 := hx3, x4 := hx4, x5 := hx5, rounds := hp.rounds, hn := hn
    x1 := by rw [hx1]; exact hp.x1'
    wc := Offset.base_disjoint St (by decide) (by omega_using [])
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (scrC S _)
    dc := hdc, ds := hds
    cs := (hp.st_s.sub_left c272).sub_right (scrC S _)
    wrapC := by rw [toNat_add_lt St hw (by decide)]; omega_using [hw]
    wrapD := hwrap
    wrapS := hp.wC
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact hcov
      · exact ⟨⟨St, 304⟩, by simp, 272, rfl, by simp⟩
      · exact ⟨⟨S, 64 + N⟩, by simp, 64, rfl, by simp⟩
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 272, rfl, by simp⟩
      · exact ⟨⟨S, 64 + N⟩, by simp, 64, rfl, by simp⟩ }

end

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) (St D S : Addr) (c L : Nat) : Mem :=
  writeBytes (absSavedMem s₀ S) (St + BitVec.ofNat 64 (288 + held c))
    (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf c L))

/-- What the code before the first call leaves. -/
structure AMid₁ (N : Nat) (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : UArgsW N s St (St + BitVec.ofNat 64 272) (St + BitVec.ofNat 64 288) (S + BitVec.ofNat 64 64) R
    (b1Of (s₀.gpr .x2).toNat L)
  x19 : s.gpr .x19 = St
  x20 : s.gpr .x20 = s₀.gpr .x1
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (leftOf (s₀.gpr .x2).toNat L)
  x23 : s.gpr .x23 = S
  other : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = m4 s₀ St D S (s₀.gpr .x2).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {N : Nat} {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre N s₀ St D S L R) :
    WP isa absorbPre s₀ (AMid₁ N s₀ St D S L R) := by
  generalize hc : (s₀.gpr .x2).toNat = c
  obtain hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  obtain hdx : s₀.gpr .x2 = BitVec.ofNat 64 c := ofNat_toNat_eq hc
  have hL := hp.lt
  have hw := hp.wSt
  have ⟨hfL, hfh⟩ := f_le c L
  obtain hh := held_le c
  obtain ⟨s₁, run₁, x19₁, x20₁, x21₁, x22₁, x23₁, x2₁, g₁, sp₁, m₁, rd₁, wr₁⟩ :=
    save_ok s₀ hp.x5 fun d _ h => hp.inS (by omega_using [h])
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (held_wp hcl (by rw [x2₁, hdx])) fun s₂ ⟨x9₂, g₂, sp₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (fill_wp (St := St) (D := D) hL x9₂ (by rw [g₂ _ (by decide) (by decide), x22₁, hp.x4'])
    (by rw [g₂ _ (by decide) (by decide), x19₁, hp.x0]) (by rw [g₂ _ (by decide) (by decide), x21₁, hp.x3]))
    fun s₃ ⟨x8₃, x10₃, x6₃, x7₃, g₃, sp₃, m₃, rd₃, wr₃⟩ => ?_)
  obtain dCp : Region.Sub ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_using [hfh])
  refine WP.seq (WP.mono (copy_ok s₃ (P := D) (C := St + BitVec.ofNat 64 (288 + held c)) (L := fOf c L)
    (by omega_using [hfh]) x7₃ x6₃ x8₃
    (fun i hi => by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact hp.inD (by omega_using [hfL, hi]))
    (fun i hi => by rw [wr₃, wr₂, wr₁, Offset.add_add]; exact hp.inSt (by omega_using [hfh, hi]))
    ((hp.st_d.sub_left dCp).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  -- The registers `chain1` reads, unchanged since `save`.
  have g (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x8) (d : r ≠ .x9) (e : r ≠ .x10) (f : r ≠ .x11) :
      s₄.gpr r = s₁.gpr r := by
    rw [h₄.other r a b c d, g₃ r a b c e f, g₂ r d e]
  refine WP.mono (chain1_wp (St := St) (S := S) hfL hL
    (by rw [g .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x21₁, hp.x3])
    (by rw [h₄.other _ (by decide) (by decide) (by decide) (by decide), x10₃])
    (by rw [g .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x22₁, hp.x4'])
    (by rw [g .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x19₁, hp.x0])
    (by rw [g .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x23₁]))
    fun s₅ h₅ => ?_
  obtain ⟨x21₅, x22₅, x4₅, x0₅, x1₅, x2₅, x3₅, x5₅, sv₅, sp₅, m₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (hr : r ∈ preserved) (a : r ≠ .x21) (b : r ≠ .x22) : s₅.gpr r = s₁.gpr r := by
    obtain hcc : ∀ r ∈ preserved, r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 := by decide
    obtain hc := hcc r hr
    rw [sv₅ r hr a b, g r hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2]
  obtain hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃, rd₂, rd₁]
  obtain hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃, wr₂, wr₁]
  obtain hb1 : 16 * b1Of c L ≤ 16 := by unfold b1Of; split <;> omega_using []
  obtain c288 : Region.Sub ⟨St + BitVec.ofNat 64 288, 16 * b1Of c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_using [hb1])
  obtain m₀ : s₅.mem = m4 s₀ St D S c L := by rw [m₅, h₄.mem, m₃, m₂, m₁, m4]
  subst hc
  refine ⟨hp.uargs x0₅
      (by rw [x1₅, g .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x20₁]) x2₅ x3₅
      (by rw [x4₅, b1Of, leftOf]) x5₅ hrd hwr (by omega_using [hb1])
      (Offset.disjoint St (by omega_using []) (by omega_using [hb1]) (by omega_using []))
      ((hp.st_s.sub_left c288).sub_right (scrC S _))
      (by rw [toNat_add_lt St hw (by decide)]; omega_using [hw, hb1])
      ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega_using [hb1]⟩,
    by rw [k .x19 (by simp [preserved]) (by decide) (by decide), x19₁, hp.x0],
    by rw [k .x20 (by simp [preserved]) (by decide) (by decide), x20₁],
    x21₅, by rw [x22₅]; rfl, by rw [k .x23 (by simp [preserved]) (by decide) (by decide), x23₁],
    fun r hr a b c d e => by rw [k r hr c d, g₁ r a b c d e],
    by rw [sp₅, h₄.sp, sp₃, sp₂, sp₁], m₀, hrd, hwr⟩

end VG.Proof.CmacAes.Stream.AArch64

end

/-!
# Streaming AES-CMAC on AArch64: `vg_cmac_aes_absorb` is correct

After `absorbPre`, the first call chains the block held back if data is left
(`b1`), the second the whole blocks of the data left but its last 1 to 16
bytes (`nb`), and the last copy holds those back. If no data is left (`len ≤
16 - h`), the calls chain nothing and the copy copies nothing, and the data is
appended to the bytes held back (`repr_fill`); otherwise `repr_chain`.
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.Stream.AArch64 VG.WriteBytes
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.Cmac (bytesAt_frame)
open VG.Proof.Cmac.Stream (held held_le)

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega_using [hi]) (by omega_using [hp, hi])) hc

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 16 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 16 1 = [Spec.Aes.bytesAt m p 16] := by
  simp [Spec.Cmac.blocksAt]

theorem absorb_wp (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀ : State}
    (h0 : (absorbAArch64 (64 + v.scratch)).pre s₀) :
    WP isa (absorb v.callee) s₀ fun s' => GprAbi s₀ s' ∧ (absorbAArch64 (64 + v.scratch)).post s₀ s' := by
  obtain hp := APre.of h0 (by rcases v.scratch_ok with h | h <;> omega_using [h])
  generalize s₀.gpr .x0 = St at hp
  generalize s₀.gpr .x3 = D at hp
  generalize s₀.gpr .x5 = S at hp
  generalize (s₀.gpr .x4).toNat = L at hp
  generalize (s₀.gpr .x1).toNat = R at hp
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .x2).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have hw := hp.wSt
  have hsw := hp.wS
  have ⟨hfL, hfh⟩ := f_le c L
  obtain hsum := nb_le c L
  obtain hh := held_le c
  refine WP.seq (WP.mono (absorbPre_wp hp) fun s₅ h₅ => ?_)
  obtain ⟨args₅, x19₅, x20₅, x21₅, x22₅, x23₅, o₅, sp₅, m₅, rd₅, wr₅⟩ := h₅
  rw [hc] at args₅ x21₅ x22₅ m₅
  refine WP.seq (WP.mono (upd_callW v _ args₅) fun s₆ h₆ => ?_)
  have k₆ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₆.gpr r = s₅.gpr r := h₆.saved r hr h30
  refine WP.seq (WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_using [hL])
    (by rw [k₆ .x22 (by simp [preserved]) (by decide), x22₅])) fun s₇ h₇ => ?_)
  obtain ⟨x24₇, x4₇, x0₇, x1₇, x2₇, x3₇, x5₇, sv₇, sp₇, m₇, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at x24₇ x4₇
  have k₇ (r : Reg) (hr : r ∈ preserved) (a : r ≠ .x24) (h30 : r ≠ .x30) : s₇.gpr r = s₅.gpr r := by
    rw [sv₇ r hr a, k₆ r hr h30]
  obtain dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L), 16 * nbOf c L⟩ ⟨D, L⟩ := Offset.sub_base D (by omega_using [hsum])
  obtain c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  obtain args₇ := hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf c L)) (n := nbOf c L)
    (by rw [x0₇, k₆ .x19 (by simp [preserved]) (by decide), x19₅])
    (by rw [x1₇, k₆ .x20 (by simp [preserved]) (by decide), x20₅])
    (by rw [x2₇, k₆ .x19 (by simp [preserved]) (by decide), x19₅])
    (by rw [x3₇, k₆ .x21 (by simp [preserved]) (by decide), x21₅]) x4₇
    (by rw [x5₇, k₆ .x23 (by simp [preserved]) (by decide), x23₅]) (by rw [rd₇, h₆.rd, rd₅])
    (by rw [wr₇, h₆.wr, wr₅]) (by omega_using [hL, hsum]) ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (scrC S _))
    (by
      by_cases h0 : nbOf c L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf c L)).isLt; omega_using []
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_arith)]; omega_using [hsum, this])
    ⟨⟨D, L⟩, by simp, fOf c L, rfl, by simp; omega_using [hsum]⟩
  refine WP.seq (WP.mono (upd_callW v _ args₇) fun s₈ h₈ => ?_)
  have k₈ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₈.gpr r = s₇.gpr r := h₈.saved r hr h30
  obtain ⟨s₉, run₉, x21₉, x22₉, x6₉, x7₉, x8₉, sv₉, sp₉, m₉, rd₉, wr₉⟩ := rest_ok (s := s₈) (D := D)
    (a := fOf c L) (x := leftOf c L) (n := nbOf c L) (by unfold leftOf; omega_using [hsum])
    (by rw [k₈ .x21 (by simp [preserved]) (by decide), k₇ .x21 (by simp [preserved]) (by decide) (by decide),
      x21₅])
    (by rw [k₈ .x24 (by simp [preserved]) (by decide), x24₇])
    (by rw [k₈ .x22 (by simp [preserved]) (by decide), k₇ .x22 (by simp [preserved]) (by decide) (by decide),
      x22₅])
  refine WP.seq (WP.of_runBlock ⟨s₉, run₉, ?_⟩)
  obtain rd₉' : s₉.rd = s₀.rd := by rw [rd₉, h₈.rd, rd₇, h₆.rd, rd₅]
  obtain wr₉' : s₉.wr = s₀.wr := by rw [wr₉, h₈.wr, wr₇, h₆.wr, wr₅]
  obtain dR : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L), restOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega_using [hsum])
  obtain hrr : restOf c L ≤ 16 := by unfold restOf nbOf leftOf; split <;> omega_arith
  obtain sR : Region.Sub ⟨St + BitVec.ofNat 64 288, restOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_using [hrr])
  refine WP.seq (WP.mono (copy_ok s₉ (P := D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L))
    (C := St + BitVec.ofNat 64 288) (L := restOf c L) (by omega_using [hrr]) x7₉
    (by rw [x6₉, k₈ .x19 (by simp [preserved]) (by decide), k₇ .x19 (by simp [preserved]) (by decide) (by decide),
      x19₅]) x8₉
    (fun i hi => by rw [rd₉', wr₉', Offset.add_add]; exact hp.inD (by omega_using [hsum, hi]))
    (fun i hi => by rw [wr₉', Offset.add_add]; exact hp.inSt (by omega_using [hrr, hi]))
    ((hp.st_d.sub_left sR).symm.sub_left dR)) fun s₁₀ h₁₀ => ?_)
  obtain x23₁₀ : s₁₀.gpr .x23 = S := by
    rw [h₁₀.other _ (by decide) (by decide) (by decide) (by decide),
      sv₉ _ (by simp [preserved]) (by decide) (by decide),
      k₈ .x23 (by simp [preserved]) (by decide), k₇ .x23 (by simp [preserved]) (by decide) (by decide), x23₅]
  obtain ⟨s₁₁, run₁₁, slot₁₁, keep₁₁, sp₁₁, m₁₁⟩ := restore_ok s₁₀ x23₁₀
    (fun d _ h => by
      rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉']
      obtain ⟨r, hr, hc⟩ := hp.inS (d := d) (n := 8) (by omega_using [h])
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
  refine WP.of_runBlock ⟨s₁₁, run₁₁, ?_⟩
  -- The frames.
  obtain hlf : (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf c L)).length = fOf c L := Proof.Cmac.bytesAt_length _ _ _
  obtain hlr : (Spec.Aes.bytesAt s₉.mem (D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L)) (restOf c L)).length =
    restOf c L := Proof.Cmac.bytesAt_length _ _ _
  obtain fS : Frame [⟨S + BitVec.ofNat 64 8, 56⟩] s₀.mem (absSavedMem s₀ S) := absSavedMem_frame _ _
  obtain fC1 : Frame [⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩] (absSavedMem s₀ S) s₅.mem := by
    rw [m₅, m4]; exact writeBytes_frame _ _ _ (by rw [hlf]; exact Region.contains_self _ _)
  have f6 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S + BitVec.ofNat 64 64, v.scratch⟩] s₅.mem s₆.mem := h₆.frame
  obtain f8 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S + BitVec.ofNat 64 64, v.scratch⟩] s₆.mem s₈.mem := by
    rw [← m₇]; exact h₈.frame
  obtain fC2 : Frame [⟨St + BitVec.ofNat 64 288, restOf c L⟩] s₈.mem s₁₁.mem := by
    rw [m₁₁, h₁₀.mem, m₉]
    exact writeBytes_frame _ _ _ (by rw [← m₉, hlr]; exact Region.contains_self _ _)
  let K : List Region := [⟨S + BitVec.ofNat 64 8, 56⟩, ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩,
    ⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S + BitVec.ofNat 64 64, v.scratch⟩, ⟨St + BitVec.ofNat 64 288, restOf c L⟩]
  obtain F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  obtain F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  obtain F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  obtain F11 : Frame K s₀.mem s₁₁.mem := F8.trans (fC2.mono (by simp [K]))
  -- The key and the data are in none of these.
  obtain dK : ∀ r ∈ K, (⟨St, 272⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (scrS S _)
    · exact Offset.base_disjoint St (by omega_using []) (by omega_using [hfh])
    · exact Offset.base_disjoint St (by omega_using []) (by omega_using [])
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (scrC S _)
    · exact Offset.base_disjoint St (by omega_using []) (by omega_using [hrr])
  obtain dDat : ∀ r ∈ K, (⟨D, L⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.d_s.sub_right (scrS S _)
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_using [hfh]))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by decide))
    · exact hp.d_s.sub_right (scrC S _)
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_using [hrr]))
  obtain k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
  refine ⟨⟨fun r hr => ?_, by rw [sp₁₁, h₁₀.sp, sp₉, h₈.sp, sp₇, h₆.sp, sp₅]⟩, ?_⟩
  · -- The registers, restored from their slots.
    obtain Fp : Frame K.tail (absSavedMem s₀ S) s₁₁.mem :=
      ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
        ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
    have slot (d : Nat) (h₁ : 8 ≤ d) (h₂ : d + 8 ≤ 64) :
        s₁₀.mem.readW (S + BitVec.ofNat 64 d) 64 = (absSavedMem s₀ S).readW (S + BitVec.ofNat 64 d) 64 := by
      rw [← m₁₁]
      obtain sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 64 + v.scratch⟩ := Offset.sub_base S (by omega_using [h₂])
      refine Fp.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hfh]))).symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
      · exact Offset.disjoint S (Or.inl (by omega_using [h₂])) (by omega_using [h₂])
          (by have := hp.hN; omega_using [this])
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hrr]))).symm.sub_left sub
    have sl {r : Reg} {d : Nat} (h : (r, d) ∈ saved) : s₁₁.gpr r = s₀.gpr r := by
      obtain hd : 8 ≤ d ∧ d + 8 ≤ 64 := by
        simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
        omega
      rw [slot₁₁ r d h, slot d hd.1 hd.2, absSaved_slot s₀ S h]
    obtain hc' : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x24 → r ≠ .x30 →
        r ≠ .x23 → r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 := by decide
    have oth (r : Reg) (hr : r ∈ preserved) (a : r ≠ .x19) (b : r ≠ .x20) (c : r ≠ .x21) (d : r ≠ .x22)
        (e : r ≠ .x24) (f : r ≠ .x30) (g : r ≠ .x23) : s₁₁.gpr r = s₀.gpr r := by
      obtain ⟨n6, n7, n8, n9⟩ := hc' r hr a b c d e f g
      rw [keep₁₁ r a b c d e f g, h₁₀.other r n6 n7 n8 n9, sv₉ r hr c d, k₈ r hr f, k₇ r hr e f,
        o₅ r hr a b c d g]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sl (d := 8) (by simp [saved])
    · exact sl (d := 16) (by simp [saved])
    · exact sl (d := 24) (by simp [saved])
    · exact sl (d := 32) (by simp [saved])
    · exact sl (d := 56) (by simp [saved])
    · exact sl (d := 40) (by simp [saved])
    · exact oth _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact oth _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact oth _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact oth _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact sl (d := 48) (by simp [saved])
  · intro key msg hr hR hcnt hlen
    rw [hp.x0] at hr ⊢
    rw [hp.x3, hp.x4]
    rw [hp.x4] at hlen
    obtain hcm : c = msg.length := by rw [← hc, hcnt, toNat_ofNat (by omega_using [hlen])]
    subst hcm
    obtain hRk : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.x1]; exact hR
    obtain hRb : 16 * (R + 1) ≤ 272 := by rcases hp.rounds with h | h | h <;> omega_using [h]
    obtain hsch := ((Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    rw [← hRk] at hsch
    obtain ciph : ∀ m : Mem, Frame K s₀.mem m →
        Spec.Cmac.aesWith R (Spec.Aes.bytesAt m St (16 * (R + 1))) = Spec.Cmac.aes key := fun m hf => by
      rw [bytesAt_frame hf (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega_using [hRb]), hsch,
        Spec.Cmac.aes, ← hRk]
    -- The data, wherever it is read.
    obtain dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem D L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m D hab, bytesAt_frame hf dDat (by omega_using [hlen])]
    obtain fS' : Frame K s₀.mem (absSavedMem s₀ S) := fS.mono (by simp [K])
    -- The chaining value.
    obtain cv5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 272) 16 := by
      rw [bytesAt_frame fC1 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_using []) (by omega_using []) (by omega_using [hfh]))
          (by decide),
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).sub_right (scrS S _))
          (by decide)]
    obtain cv11 : Spec.Aes.bytesAt s₁₁.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₈.mem (St + BitVec.ofNat 64 272) 16 :=
      bytesAt_frame fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_using []) (by omega_using []) (by omega_using [hrr]))
        (by decide)
    have out6 := h₆.out
    rw [ciph _ F5] at out6
    have out8 := h₈.out
    rw [m₇, ciph _ F6] at out8
    obtain hk : ∀ i < 272, s₁₁.mem (St + BitVec.ofNat 64 i) = s₀.mem (St + BitVec.ofNat 64 i) :=
      fun i hi => frame_at F11 dK (by omega_using [hw]) hi
    obtain hdl : (Spec.Aes.bytesAt s₀.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    obtain hb5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 288) (held msg.length + fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 288) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem D L).take (fOf msg.length L) := by
      obtain e := bytesAt_writeBytes (absSavedMem s₀ S) (St + BitVec.ofNat 64 288) (held msg.length)
        (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf msg.length L)) (by rw [hlf]; omega_using [hfh])
      rw [hlf] at e
      rw [m₅, m4, ← Offset.add_add, e,
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hh]))).sub_right (scrS S _))
          (by omega_using [hh])]
      refine congrArg (_ ++ ·) ?_
      have := dat _ fS' 0 (fOf msg.length L) (by omega_using [hsum])
      rwa [k0, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem D L = d at hdl hb5 dat ⊢
    by_cases hx : leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      obtain hfL' : fOf msg.length L = L := by unfold leftOf at hx; omega_using [hsum, hx]
      obtain hb : b1Of msg.length L = 0 := by simp [b1Of, hx]
      obtain hn : nbOf msg.length L = 0 := by simp [nbOf, hx]
      obtain hr0 : restOf msg.length L = 0 := by simp [restOf, hn, hx]
      obtain m118 : s₁₁.mem = s₈.mem := by
        rw [m₁₁, h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem
          (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L)) 0 = [] from rfl, writeBytes_nil]
      refine Proof.Cmac.Stream.repr_fill hr hk (by rw [hdl]; have := (f_le msg.length L).2; omega_using [hfL', this]) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _
        rw [cv11, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
        exact cv5
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _
        obtain sub : Region.Sub ⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ ⟨St, 304⟩ :=
          Offset.sub_base St (by omega_using [hfh, hfL'])
        obtain dj : ∀ r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S + BitVec.ofNat 64 64, v.scratch⟩],
            (⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ : Region).Disjoint r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega_using []) (by omega_using [hfh, hfL']) (by omega_using [])
          · exact (hp.st_s.sub_left sub).sub_right (scrC S _)
        have hb5' := hb5
        rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
        rw [m118, hdl, bytesAt_frame f8 dj (by omega_using [hfh, hfL']), bytesAt_frame f6 dj (by omega_using [hfh, hfL']), hb5']
    · -- The block held back is complete, and more blocks may follow.
      obtain hlt : 16 - held msg.length < L := by unfold leftOf fOf at hx; omega_using [hx]
      obtain hf' : fOf msg.length L = 16 - held msg.length := by unfold fOf; omega_using [hlt]
      obtain hb : b1Of msg.length L = 1 := by simp [b1Of, hx]
      obtain hn : nbOf msg.length L = Proof.Cmac.Stream.nblocks msg.length L := by
        simp only [nbOf, hx, ↓reduceIte]
        unfold leftOf Proof.Cmac.Stream.nblocks
        rw [hf']
      have hb5' := hb5
      rw [hf', Nat.add_sub_cancel' hh] at hb5'
      refine Proof.Cmac.Stream.repr_chain hr hk (by rw [hdl]; exact hlt) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ =
          Spec.Cmac.chain _ (Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _)
            ([Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _] ++ _)
        rw [cv11, out8, out6, hb, blocksAt_one, cv5, Proof.Cmac.chain_append, Proof.Cmac.Stream.blocksAt_eq,
          dat _ F6 _ _ (by omega_using [hsum]), hb5', hdl, hf', hn]
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = _
        obtain e := bytesAt_writeBytes_self s₈.mem (St + BitVec.ofNat 64 288)
          (xs := Spec.Aes.bytesAt s₈.mem (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L))
            (restOf msg.length L)) (by rw [Proof.Cmac.bytesAt_length]; omega_using [hrr])
        rw [Proof.Cmac.bytesAt_length] at e
        obtain hr' : d.length - (16 - held msg.length) - 16 * Proof.Cmac.Stream.nblocks msg.length d.length =
            restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        rw [hr', m₁₁, h₁₀.mem, m₉, e, dat _ F8 _ _ (by omega_using [hsum]),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega_using []),
          List.drop_drop, hdl, ← hn, hf']

end VG.Proof.CmacAes.Stream.AArch64

end

end

/-! ### `CmacAes.Stream.AArch64.Init`, which only this module used -/

section

/-!
# Streaming AES-CMAC on AArch64: `vg_cmac_aes_init`

The code saves `x19`, `x20`, `x21` and `x30` in the scratch buffer, expands
the key into the state, derives the subkeys after the schedule, zeroes the
chaining value and restores the registers: the state then represents the empty
message. The code between the calls is constant time by the taint analysis,
and the calls by their own proofs (`ek_rel`, `sub_rel`), their arguments
pinned by `IMid₁` and `IMid₂`.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.Stream.AArch64
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.CmacAes.AArch64 (k0 readW_writeW_other agree_of)
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- The precondition, by name: the state `St`, the key `Kp` of `KL` bytes
and the scratch buffer `S`, with `W` bytes of working space. -/
structure IPre (W : Nat) (s₀ : State) (St Kp S : Addr) (KL : Nat) : Prop where
  x0 : s₀.gpr .x0 = St
  x1 : s₀.gpr .x1 = Kp
  x2 : (s₀.gpr .x2).toNat = KL
  x3 : s₀.gpr .x3 = S
  rd : s₀.rd = [⟨Kp, KL⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 32 + W⟩]
  st_k : (⟨St, 304⟩ : Region).Disjoint ⟨Kp, KL⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 32 + W⟩
  k_s : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 32 + W⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wS : S.toNat + (32 + W) ≤ 2 ^ 64
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32
  big : 512 ≤ W

theorem IPre.of {W : Nat} {s₀ : State} (h : (initAArch64With W).pre s₀) (hW : 512 ≤ W) :
    IPre W s₀ (s₀.gpr .x0) (s₀.gpr .x1) (s₀.gpr .x3) (s₀.gpr .x2).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, hW⟩

theorem IPre.rounds {W : Nat} {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : IPre W s₀ St Kp S KL) :
    KL / 4 + 6 = 10 ∨ KL / 4 + 6 = 12 ∨ KL / 4 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

/-- The memory after saving the registers. -/
def initSavedMem (s : State) (S : Addr) : Mem :=
  (((s.mem.writeW (S + BitVec.ofNat 64 0) (s.gpr .x19)).writeW (S + BitVec.ofNat 64 8) (s.gpr .x20)).writeW
    (S + BitVec.ofNat 64 16) (s.gpr .x21)).writeW (S + BitVec.ofNat 64 24) (s.gpr .x30)

theorem initSavedMem_frame (s : State) (S : Addr) :
    Frame [⟨S + BitVec.ofNat 64 0, 32⟩] s.mem (initSavedMem s S) := by
  have c (d : Nat) (hd : d + 8 ≤ 32) : (⟨S + BitVec.ofNat 64 0, 32⟩ : Region).Contains
      (S + BitVec.ofNat 64 d) 8 :=
    Offset.contains S (Nat.zero_le _) (by omega_arith) (by omega_arith)
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 8 (by decide))).writeW (List.mem_singleton_self _) _
    (c 16 (by decide))).writeW (List.mem_singleton_self _) _ (c 24 (by decide))

theorem initSaved_read (s : State) (S : Addr) :
    (initSavedMem s S).readW (S + BitVec.ofNat 64 0) 64 = s.gpr .x19 ∧
      (initSavedMem s S).readW (S + BitVec.ofNat 64 8) 64 = s.gpr .x20 ∧
      (initSavedMem s S).readW (S + BitVec.ofNat 64 16) 64 = s.gpr .x21 ∧
      (initSavedMem s S).readW (S + BitVec.ofNat 64 24) 64 = s.gpr .x30 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [initSavedMem, readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [initSavedMem, readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [initSavedMem, readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [initSavedMem, Mem.readW_writeW_self64]

/-! ## Before the first call -/

theorem initPre_ok {W : Nat} {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : IPre W s₀ St Kp S KL) :
    ∃ s₁, runBlock isa initPre s₀ = some s₁ ∧ s₁.gpr .x0 = Kp ∧ s₁.gpr .x1 = BitVec.ofNat 64 KL ∧
      s₁.gpr .x2 = St ∧ s₁.gpr .x3 = S + BitVec.ofNat 64 32 ∧ s₁.gpr .x19 = St ∧ s₁.gpr .x20 = S ∧
      s₁.gpr .x21 = BitVec.ofNat 64 (KL / 4 + 6) ∧
      (∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → s₁.gpr r = s₀.gpr r) ∧ s₁.sp = s₀.sp ∧
      s₁.mem = initSavedMem s₀ S ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have inS (d : Nat) (hd : d + 8 ≤ 32 + W) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨S, 32 + W⟩, by simp, Offset.contains_base _ hd (by have := hp.wS; omega_arith)⟩
  obtain hKL : s₀.gpr .x2 = BitVec.ofNat 64 KL := ofNat_toNat_eq hp.x2
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, initPre, initSaved, initWOff, mov, List.map, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes,
      Size.bits, State.read, gpr_write, Option.bind_some,
      BitVec.setWidth_eq, hp.x3, inS 0 (by omega), inS 8 (by omega), inS 16 (by omega),
      inS 24 (by omega)]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, hp.x1], by simp [gpr_write, hKL], by simp [gpr_write, hp.x0],
    by simp [gpr_write], by simp [gpr_write, hp.x0], by simp [gpr_write],
    by simp [gpr_write, hKL, rounds_bv hp.klen], fun r hr h19 h20 h21 => ?_, rfl, ?_, rfl, rfl⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [gpr_write]
  · simp only [mem_write, initSavedMem, Mem.writeW, BitVec.setWidth_eq]

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ : State) (St Kp S : Addr) (KL : Nat) (s : State) : Prop where
  args : EArgs s Kp St (S + BitVec.ofNat 64 32) KL
  x19 : s.gpr .x19 = St
  x20 : s.gpr .x20 = S
  x21 : s.gpr .x21 = BitVec.ofNat 64 (KL / 4 + 6)
  other : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = initSavedMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initPre_wp {W : Nat} {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : IPre W s₀ St Kp S KL) :
    WP isa (.block initPre) s₀ (IMid₁ s₀ St Kp S KL) := by
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x19₁, x20₁, x21₁, o₁, sp₁, m₁, rd₁, wr₁⟩ := initPre_ok hp
  refine WP.of_runBlock ⟨s₁, run₁, ⟨?_, x19₁, x20₁, x21₁, o₁, sp₁, m₁, rd₁, wr₁⟩⟩
  have hb := hp.big
  obtain pS : Region.Sub ⟨S + BitVec.ofNat 64 32, 512⟩ ⟨S, 32 + W⟩ := Offset.sub_base S (by omega)
  exact
  { x0 := x0₁, x1 := x1₁, x2 := x2₁, x3 := x3₁, klen := hp.klen
    kw := hp.st_k.symm.sub_right (Region.sub_prefix (by decide))
    ks := hp.k_s.sub_right pS
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right pS
    reads := by
      rw [rd₁, wr₁, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨Kp, KL⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 32 + W⟩, by simp, 32, rfl, by dsimp only; omega⟩
    writes := by
      rw [wr₁, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 32 + W⟩, by simp, 32, rfl, by dsimp only; omega⟩ }

/-! ## Between the calls, and after them -/

theorem initMid_ok {s : State} {St S : Addr} {R : Nat} (h19 : s.gpr .x19 = St) (h20 : s.gpr .x20 = S)
    (h21 : s.gpr .x21 = BitVec.ofNat 64 R) :
    ∃ s', runBlock isa initMid s = some s' ∧ s'.gpr .x0 = St ∧ s'.gpr .x1 = BitVec.ofNat 64 R ∧
      s'.gpr .x2 = St + BitVec.ofNat 64 240 ∧ s'.gpr .x3 = S + BitVec.ofNat 64 32 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, initMid, initWOff, mov, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, h19], by simp [gpr_write, h21], by simp [gpr_write, h19],
    by simp [gpr_write, h20], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

/-- The memory after zeroing the chaining value. -/
def zeroCv (m : Mem) (St : Addr) : Mem :=
  (m.writeW (St + BitVec.ofNat 64 272) (0 : BitVec 64)).writeW (St + BitVec.ofNat 64 280) (0 : BitVec 64)

theorem zeroCv_eq (m : Mem) (St : Addr) : zeroCv m St = Proof.Cmac.zero2 m (St + BitVec.ofNat 64 272) := by
  rw [zeroCv, Proof.Cmac.zero2, Offset.add_add]

theorem initPost_ok {s : State} {St S : Addr} (h19 : s.gpr .x19 = St) (h20 : s.gpr .x20 = S)
    (w₁ : InRegions s.wr (St + BitVec.ofNat 64 272) 8) (w₂ : InRegions s.wr (St + BitVec.ofNat 64 280) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 0) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 8) 8)
    (r₃ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 16) 8)
    (r₄ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 24) 8) :
    ∃ s', runBlock isa initPost s = some s' ∧
      s'.gpr .x19 = (zeroCv s.mem St).readW (S + BitVec.ofNat 64 0) 64 ∧
      s'.gpr .x20 = (zeroCv s.mem St).readW (S + BitVec.ofNat 64 8) 64 ∧
      s'.gpr .x21 = (zeroCv s.mem St).readW (S + BitVec.ofNat 64 16) 64 ∧
      s'.gpr .x30 = (zeroCv s.mem St).readW (S + BitVec.ofNat 64 24) 64 ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x30 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = zeroCv s.mem St := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, initPost, runBlock_cons, runStep_some, runBlock_nil, exec,
      addr, State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write,
      wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq, h19, h20,
      w₁, w₂, r₁, r₂, r₃, r₄]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r a b c d f => by simp [gpr_write, a, b, c, d, f], rfl, ?_⟩
  all_goals simp [gpr_write, mem_write, zeroCv, Mem.readW, Mem.writeW]

/-- What the code between the calls leaves. -/
structure IMid₂ (W : Nat) (s₀ : State) (St S : Addr) (KL : Nat) (m : Mem) (s : State) : Prop where
  args : SArgs s St (St + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 32) (KL / 4 + 6) W
  x19 : s.gpr .x19 = St
  x20 : s.gpr .x20 = S
  keep : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x30 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = m
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initMid_wp {W : Nat} {s₀ s : State} {St Kp S : Addr} {KL : Nat} (hp : IPre W s₀ St Kp S KL)
    (h19 : s.gpr .x19 = St) (h20 : s.gpr .x20 = S) (h21 : s.gpr .x21 = BitVec.ofNat 64 (KL / 4 + 6))
    (hsp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hk : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x30 → s.gpr r = s₀.gpr r) :
    WP isa (.block initMid) s (IMid₂ W s₀ St S KL s.mem) := by
  obtain ⟨s', run, x0, x1, x2, x3, sv, sp, mem, rd, wr⟩ := initMid_ok h19 h20 h21
  have hw := hp.wSt
  have hb := hp.big
  have sw := hp.wS
  obtain pS : Region.Sub ⟨S + BitVec.ofNat 64 32, W⟩ ⟨S, 32 + W⟩ := Offset.sub_base S (by omega)
  obtain kSt : Region.Sub ⟨St + BitVec.ofNat 64 240, 32⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  refine WP.of_runBlock ⟨s', run, ⟨?_, by rw [sv _ (by simp [preserved]), h19],
    by rw [sv _ (by simp [preserved]), h20], fun r hr a b c d => by rw [sv r hr, hk r hr a b c d],
    by rw [sp, hsp], mem, by rw [rd, hrd], by rw [wr, hwr]⟩⟩
  exact
  { x0 := x0, x1 := x1, x2 := x2, x3 := x3, rounds := hp.rounds
    wk := Offset.base_disjoint St (by decide) (by omega_arith)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right pS
    ks := (hp.st_s.sub_left kSt).sub_right pS
    wrapK := by rw [toNat_add_lt St hw (by decide)]; omega_arith
    wrapS := by rw [toNat_add_lt S sw (by omega)]; omega
    reads := by
      rw [rd, wr, hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 304⟩, by simp, 240, rfl, by simp⟩
      · exact ⟨⟨S, 32 + W⟩, by simp, 32, rfl, by simp⟩
    writes := by
      rw [wr, hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 240, rfl, by simp⟩
      · exact ⟨⟨S, 32 + W⟩, by simp, 32, rfl, by simp⟩ }

/-! ## The whole function -/

theorem init_wp (v : Ctr32Impl) {W : Nat} (hW : 128 + v.scratch ≤ W) (hb : 512 ≤ W) {s₀ : State}
    (h0 : (initAArch64With W).pre s₀) :
    WP isa (init v.expand v.callee v.suffix) s₀ fun s' => GprAbi s₀ s' ∧ (initAArch64With W).post s₀ s' := by
  obtain hp := IPre.of h0 hb
  generalize s₀.gpr .x0 = St at hp
  generalize s₀.gpr .x1 = Kp at hp
  generalize s₀.gpr .x3 = S at hp
  generalize (s₀.gpr .x2).toNat = KL at hp
  have hw := hp.wSt
  have hsw := hp.wS
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ek_call v h₁.args) fun s₂ h₂ => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₂.gpr r = s₁.gpr r := h₂.saved r hr h30
  refine WP.seq (WP.mono (initMid_wp hp (by rw [g₂ _ (by simp [preserved]) (by decide), h₁.x19])
    (by rw [g₂ _ (by simp [preserved]) (by decide), h₁.x20])
    (by rw [g₂ _ (by simp [preserved]) (by decide), h₁.x21]) (by rw [h₂.sp, h₁.sp]) (by rw [h₂.rd, h₁.rd])
    (by rw [h₂.wr, h₁.wr]) (fun r hr a b c d => by rw [g₂ r hr d, h₁.other r hr a b c])) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (sub_callLe v _ hW h₃.args) fun s₄ h₄ => ?_)
  have g₄ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₄.gpr r = s₃.gpr r := h₄.saved r hr h30
  have inS (d : Nat) (hd : d + 8 ≤ 32 + W) : InRegions s₄.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [h₄.wr, h₃.wr, hp.wr]; exact ⟨⟨S, 32 + W⟩, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  have inSt (d : Nat) (hd : d + 8 ≤ 304) : InRegions s₄.wr (St + BitVec.ofNat 64 d) 8 := by
    rw [h₄.wr, h₃.wr, hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  have inR (d : Nat) (hd : d + 8 ≤ 32 + W) : InRegions (s₄.rd ++ s₄.wr) (S + BitVec.ofNat 64 d) 8 := by
    obtain ⟨r, hr, hc⟩ := inS d hd; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain ⟨s₅, run₅, x19₅, x20₅, x21₅, x30₅, keep₅, sp₅, m₅⟩ := initPost_ok (s := s₄) (St := St) (S := S)
    (by rw [g₄ _ (by simp [preserved]) (by decide), h₃.x19])
    (by rw [g₄ _ (by simp [preserved]) (by decide), h₃.x20])
    (inSt 272 (by decide)) (inSt 280 (by decide)) (inR 0 (by omega)) (inR 8 (by omega))
    (inR 16 (by omega)) (inR 24 (by omega))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  -- The memory, step by step.
  obtain fz : Frame [⟨St + BitVec.ofNat 64 272, 16⟩] s₄.mem (zeroCv s₄.mem St) := by
    rw [zeroCv_eq]; exact Proof.Cmac.frame_store2 _ _ _
  obtain f₁ : Frame [⟨S + BitVec.ofNat 64 0, 32⟩] s₀.mem s₁.mem := by
    rw [h₁.mem]; exact initSavedMem_frame _ _
  have f₂ : Frame [⟨St, 240⟩, ⟨S + BitVec.ofNat 64 32, 512⟩] s₁.mem s₂.mem := h₂.frame
  have f₄ : Frame [⟨St + BitVec.ofNat 64 240, 32⟩, ⟨S + BitVec.ofNat 64 32, W⟩] s₃.mem s₄.mem := h₄.frame
  have m₃ : s₃.mem = s₂.mem := h₃.mem
  -- The saved registers.
  have dSv (r : Region) (hr : r ∈ [⟨St, 240⟩, ⟨S + BitVec.ofNat 64 32, 512⟩, ⟨St + BitVec.ofNat 64 240, 32⟩,
      ⟨S + BitVec.ofNat 64 32, W⟩, ⟨St + BitVec.ofNat 64 272, 16⟩]) (d : Nat) (hd' : d + 8 ≤ 32) :
      (⟨S + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    obtain sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 32 + W⟩ := Offset.sub_base S (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact Offset.disjoint S (.inl hd') (by omega_arith) (by omega_arith)
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
    · exact Offset.disjoint S (.inl hd') (by omega_arith) (by omega_arith)
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
  have rd' (d : Nat) (hd' : d + 8 ≤ 32) :
      (zeroCv s₄.mem St).readW (S + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S + BitVec.ofNat 64 d) 64 := by
    obtain c := Region.contains_self (S + BitVec.ofNat 64 d) 8
    rw [fz.readW c (fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr]) d hd') (by decide),
      f₄.readW c (fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl <;> simp) d hd') (by decide), m₃,
      f₂.readW c (fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl <;> simp) d hd') (by decide)]
  obtain ⟨sv₁, sv₂, sv₃, sv₄⟩ := initSaved_read s₀ S
  have m₁ := h₁.mem
  -- The state, outside what the last block writes.
  have dSt (d n : Nat) (hd : d + n ≤ 272) (r : Region) (hr : r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩]) :
      (⟨St + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith)
  obtain hRb : 16 * (Spec.Aes.rounds (KL / 4) + 1) ≤ 240 := by
    have := hp.klen; simp only [Spec.Aes.rounds]; omega_arith
  refine ⟨⟨fun r hr => ?_, by rw [sp₅, h₄.sp, h₃.sp]⟩, ?_⟩
  · by_cases h19 : r = .x19
    · subst h19; rw [x19₅, rd' 0 (by decide), m₁]; exact sv₁
    by_cases h20 : r = .x20
    · subst h20; rw [x20₅, rd' 8 (by decide), m₁]; exact sv₂
    by_cases h21 : r = .x21
    · subst h21; rw [x21₅, rd' 16 (by decide), m₁]; exact sv₃
    by_cases h30 : r = .x30
    · subst h30; rw [x30₅, rd' 24 (by decide), m₁]; exact sv₄
    obtain h9 : r ≠ .x9 := by rintro rfl; simp [preserved] at hr
    rw [keep₅ r h19 h20 h21 h30 h9, g₄ r hr h30, h₃.keep r hr h19 h20 h21 h30]
  · show Spec.Cmac.Repr s₅.mem (s₀.gpr .x0) (Spec.Aes.bytesAt s₀.mem (s₀.gpr .x1) (s₀.gpr .x2).toNat) []
    rw [hp.x0, hp.x1, hp.x2, Proof.Cmac.Stream.repr_iff]
    obtain hkey : Spec.Aes.bytesAt s₁.mem Kp KL = Spec.Aes.bytesAt s₀.mem Kp KL :=
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.k_s.sub_right (Offset.sub_base S (by omega))) (by have := hp.wK; omega_arith)
    obtain hlen : (Spec.Aes.bytesAt s₀.mem Kp KL).length = KL := Proof.Cmac.bytesAt_length _ _ _
    -- The schedule, from the first call on.
    obtain sch : ∀ {d n : Nat}, d + n ≤ 240 → Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₂.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
      rw [m₅, Proof.Cmac.bytesAt_frame fz (dSt d n (by omega_arith)) (by omega_arith),
        Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith)
          · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_arith))).sub_right (Offset.sub_base S (by omega)))
          (by omega_arith), m₃]
    obtain hsch : Spec.Aes.bytesAt s₂.mem St (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem Kp KL) := by rw [h₂.out, hkey]
    refine ⟨⟨by rw [hlen]; exact hp.klen, ?_, ?_⟩, ?_, by simp [Proof.Cmac.Stream.held_zero, Spec.Aes.bytesAt]⟩
    · rw [hlen]
      have := sch (d := 0) (n := 16 * (Spec.Aes.rounds (KL / 4) + 1)) (by omega_arith)
      rw [k0] at this; rw [this, hsch]
    · have e : Spec.Aes.bytesAt s₅.mem (St + 240) 32 = Spec.Aes.bytesAt s₄.mem (St + 240) 32 := by
        rw [m₅]; exact Proof.Cmac.bytesAt_frame fz (dSt 240 32 (by decide)) (by decide)
      rw [e]
      refine h₄.out.trans ?_
      rw [m₃, show KL / 4 + 6 = Spec.Aes.rounds (KL / 4) from rfl, hsch]
      simp only [Spec.Cmac.aes, hlen]
    · rw [m₅, zeroCv_eq]; exact (Proof.Cmac.zero2_bytes _ _).trans rfl

/-! ## Constant time -/

/-- What the call of `vg_aes_expand_key_scratch` leaves, for `initMid`. -/
structure IAfter (s₀ : State) (St S : Addr) (KL : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = St
  x20 : s.gpr .x20 = S
  x21 : s.gpr .x21 = BitVec.ofNat 64 (KL / 4 + 6)
  sp : s.sp = s₀.sp
  keep : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x30 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ek_after (v : Ctr32Impl) {s₀ s : State} {St Kp S : Addr} {KL : Nat} (h : IMid₁ s₀ St Kp S KL s) :
    WP isa (.call v.expand.name v.expand.code) s (IAfter s₀ St S KL) :=
  WP.mono (ek_call v h.args) fun _ h₂ =>
    ⟨by rw [h₂.saved _ (by simp [preserved]) (by decide), h.x19],
      by rw [h₂.saved _ (by simp [preserved]) (by decide), h.x20],
      by rw [h₂.saved _ (by simp [preserved]) (by decide), h.x21], by rw [h₂.sp, h.sp],
      fun r hr a b c d => by rw [h₂.saved r hr d, h.other r hr a b c], by rw [h₂.rd, h.rd], by rw [h₂.wr, h.wr]⟩

theorem init_rel (v : Ctr32Impl) {W : Nat} (hW : 128 + v.scratch ≤ W) (hb : 512 ≤ W) {s₀ s₀' : State}
    (h0 : (initAArch64With W).pre s₀) (h0' : (initAArch64With W).pre s₀') (hq : (initAArch64With W).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (init v.expand v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q0, q1, q2, q3, q4⟩ := hq
  obtain hp := IPre.of h0 hb
  obtain hp' : IPre W s₀' (s₀.gpr .x0) (s₀.gpr .x1) (s₀.gpr .x3) (s₀.gpr .x2).toNat := by
    rw [q0, q1, q2, q3]; exact IPre.of h0' hb
  generalize s₀.gpr .x0 = St at hp hp'
  generalize s₀.gpr .x1 = Kp at hp hp'
  generalize s₀.gpr .x3 = S at hp hp'
  generalize (s₀.gpr .x2).toNat = KL at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3]) (.block initPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21]) (.block initMid) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20]) (.block initPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of q4 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := IMid₁ s₀ St Kp S KL) (F₂ := IMid₁ s₀' St Kp S KL) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨initPre_wp hp, initPre_wp hp'⟩
  obtain e := (ek_rel v (P := fun a b => IMid₁ s₀ St Kp S KL a ∧ IMid₁ s₀' St Kp S KL b)
    fun a b h => ⟨h.1.args, h.2.args, by rw [h.1.sp, h.2.sp, q4]⟩).wp
    (F₁ := IAfter s₀ St S KL) (F₂ := IAfter s₀' St S KL) fun a b h => ⟨ek_after v h.1, ek_after v h.2⟩
  obtain m := (RelCT.taint (A := taint) (P := fun a b => IAfter s₀ St S KL a ∧ IAfter s₀' St S KL b) _
    (fun a b h => by
      refine agree_of (by rw [h.1.sp, h.2.sp, q4]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.x19, h.2.x19]
      · rw [h.1.x20, h.2.x20]
      · rw [h.1.x21, h.2.x21]) hB).wp
    (F₁ := fun (s : State) => ∃ m, IMid₂ W s₀ St S KL m s) (F₂ := fun (s : State) => ∃ m, IMid₂ W s₀' St S KL m s)
    fun a b h => ⟨WP.mono (initMid_wp hp h.1.x19 h.1.x20 h.1.x21 h.1.sp h.1.rd h.1.wr h.1.keep)
        fun _ h => ⟨_, h⟩,
      WP.mono (initMid_wp hp' h.2.x19 h.2.x20 h.2.x21 h.2.sp h.2.rd h.2.wr h.2.keep) fun _ h => ⟨_, h⟩⟩
  obtain sk := (sub_relLe v ("vg_cmac_aes_subkeys" ++ v.suffix) hW
    (P := fun a b => (∃ m, IMid₂ W s₀ St S KL m a) ∧ ∃ m, IMid₂ W s₀' St S KL m b)
    fun a b ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ => ⟨h₁.args, h₂.args, by rw [h₁.sp, h₂.sp, q4]⟩).wp
    (F₁ := fun (s : State) => s.gpr .x19 = St ∧ s.gpr .x20 = S ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .x19 = St ∧ s.gpr .x20 = S ∧ s.sp = s₀'.sp)
    fun a b ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ =>
      ⟨WP.mono (sub_callLe v _ hW h₁.args) fun _ h => ⟨by rw [h.saved _ (by simp [preserved]) (by decide), h₁.x19],
          by rw [h.saved _ (by simp [preserved]) (by decide), h₁.x20], by rw [h.sp, h₁.sp]⟩,
        WP.mono (sub_callLe v _ hW h₂.args) fun _ h => ⟨by rw [h.saved _ (by simp [preserved]) (by decide), h₂.x19],
          by rw [h.saved _ (by simp [preserved]) (by decide), h₂.x20], by rw [h.sp, h₂.sp]⟩⟩
  obtain p := RelCT.taint (A := taint)
    (P := fun a b => (a.gpr .x19 = St ∧ a.gpr .x20 = S ∧ a.sp = s₀.sp) ∧
      b.gpr .x19 = St ∧ b.gpr .x20 = S ∧ b.sp = s₀'.sp) _
    (fun a b h => by
      refine agree_of (by rw [h.1.2.2, h.2.2.2, q4]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2.1, h.2.2.1]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((sk.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem init_ct (v : Ctr32Impl) {W : Nat} (hW : 128 + v.scratch ≤ W) (hb : 512 ≤ W) :
    ConstantTime isa (initAArch64With W).pre (initAArch64With W).pub (init v.expand v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel v hW hb h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.AArch64

end

end

@[expose] public section

section

/-!
# Streaming AES-CMAC on AArch64: `vg_cmac_aes_absorb` is constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
the registers the correctness proof pins to values of the public arguments
(`AMid₁`, `AAfter₁`, `AMid₂`, `AAfter₂`), and each call of
`vg_cmac_aes_update` is constant time by its own proof (`upd_rel`).
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.Stream.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.CmacAes.AArch64 (agree_of)

/-- What the first call leaves, for `chain2`. -/
structure AAfter₁ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = St
  x20 : s.gpr .x20 = s₀.gpr .x1
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (leftOf (s₀.gpr .x2).toNat L)
  x23 : s.gpr .x23 = S
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem call1_after (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : AMid₁ v.scratch s₀ St D S L R s) :
    WP isa (.call v.callee.name v.callee.code) s
      (AAfter₁ s₀ St D S L) :=
  WP.mono (upd_callW v _ h.args) fun _ h₆ =>
    ⟨by rw [h₆.saved .x19 (by simp [preserved]) (by decide), h.x19],
      by rw [h₆.saved .x20 (by simp [preserved]) (by decide), h.x20],
      by rw [h₆.saved .x21 (by simp [preserved]) (by decide), h.x21],
      by rw [h₆.saved .x22 (by simp [preserved]) (by decide), h.x22],
      by rw [h₆.saved .x23 (by simp [preserved]) (by decide), h.x23],
      by rw [h₆.sp, h.sp], by rw [h₆.rd, h.rd], by rw [h₆.wr, h.wr]⟩

/-- What `chain2` leaves, for the second call. -/
structure AMid₂ (N : Nat) (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : UArgsW N s St (St + BitVec.ofNat 64 272) (D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L))
    (S + BitVec.ofNat 64 64) R (nbOf (s₀.gpr .x2).toNat L)
  x19 : s.gpr .x19 = St
  x24 : s.gpr .x24 = BitVec.ofNat 64 (16 * nbOf (s₀.gpr .x2).toNat L)
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (leftOf (s₀.gpr .x2).toNat L)
  x23 : s.gpr .x23 = S
  sp : s.sp = s₀.sp

theorem chain2_mid {N : Nat} {s₀ s : State} {St D S : Addr} {L R : Nat} (hp : APre N s₀ St D S L R)
    (h : AAfter₁ s₀ St D S L s) : WP isa chain2 s (AMid₂ N s₀ St D S L R) := by
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .x2).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have ⟨hfL, _⟩ := f_le c L
  have hsum := nb_le c L
  obtain ⟨x19₆, x20₆, x21₆, x22₆, x23₆, sp₆, rd₆, wr₆⟩ := h
  rw [hc] at x21₆ x22₆
  refine WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_arith) x22₆) fun s₇ h₇ => ?_
  obtain ⟨x24₇, x4₇, x0₇, x1₇, x2₇, x3₇, x5₇, sv₇, sp₇, -, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at x24₇ x4₇
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  subst hc
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L), 16 * nbOf (s₀.gpr .x2).toNat L⟩
      ⟨D, L⟩ := Offset.sub_base D (by omega_arith)
  refine ⟨hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L))
    (n := nbOf (s₀.gpr .x2).toNat L)
    (by rw [x0₇, x19₆]) (by rw [x1₇, x20₆]) (by rw [x2₇, x19₆]) (by rw [x3₇, x21₆]) x4₇
    (by rw [x5₇, x23₆]) (by rw [rd₇, rd₆]) (by rw [wr₇, wr₆]) (by omega_arith) ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (scrC S _))
    (by
      by_cases h0 : nbOf (s₀.gpr .x2).toNat L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L)).isLt; omega_arith
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_arith)]; omega_arith)
    ⟨⟨D, L⟩, by simp, fOf (s₀.gpr .x2).toNat L, rfl, by simp; omega_arith⟩,
    by rw [sv₇ .x19 (by simp [preserved]) (by decide), x19₆], x24₇,
    by rw [sv₇ .x21 (by simp [preserved]) (by decide), x21₆],
    by rw [sv₇ .x22 (by simp [preserved]) (by decide), x22₆],
    by rw [sv₇ .x23 (by simp [preserved]) (by decide), x23₆], by rw [sp₇, sp₆]⟩

/-- What the second call leaves, for `absorbPost`. -/
structure AAfter₂ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = St
  x24 : s.gpr .x24 = BitVec.ofNat 64 (16 * nbOf (s₀.gpr .x2).toNat L)
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (leftOf (s₀.gpr .x2).toNat L)
  x23 : s.gpr .x23 = S
  sp : s.sp = s₀.sp

theorem call2_after (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : AMid₂ v.scratch s₀ St D S L R s) :
    WP isa (.call v.callee.name v.callee.code) s
      (AAfter₂ s₀ St D S L) :=
  WP.mono (upd_callW v _ h.args) fun _ h₈ =>
    ⟨by rw [h₈.saved .x19 (by simp [preserved]) (by decide), h.x19],
      by rw [h₈.saved .x24 (by simp [preserved]) (by decide), h.x24],
      by rw [h₈.saved .x21 (by simp [preserved]) (by decide), h.x21],
      by rw [h₈.saved .x22 (by simp [preserved]) (by decide), h.x22],
      by rw [h₈.saved .x23 (by simp [preserved]) (by decide), h.x23], by rw [h₈.sp, h.sp]⟩

theorem absorb_rel (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀ s₀' : State}
    (h0 : (absorbAArch64 (64 + v.scratch)).pre s₀) (h0' : (absorbAArch64 (64 + v.scratch)).pre s₀')
    (hq : (absorbAArch64 (64 + v.scratch)).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (absorb v.callee) fun _ _ => True := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6⟩ := hq
  obtain hN : v.scratch ≤ 2176 := by rcases v.scratch_ok with h | h <;> omega_using [h]
  have hp := APre.of h0 hN
  have hp' : APre v.scratch s₀' (s₀.gpr .x0) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat := by
    rw [q0, q1, q3, q4, q5]; exact APre.of h0' hN
  generalize s₀.gpr .x0 = St at hp hp'
  generalize s₀.gpr .x3 = D at hp hp'
  generalize s₀.gpr .x5 = S at hp hp'
  generalize (s₀.gpr .x4).toNat = L at hp hp'
  generalize (s₀.gpr .x1).toNat = R at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) absorbPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23]) chain2 h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x21, .x22, .x23, .x24]) absorbPost h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of q6 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := AMid₁ v.scratch s₀ St D S L R) (F₂ := AMid₁ v.scratch s₀' St D S L R) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨absorbPre_wp hp, absorbPre_wp hp'⟩
  have c₁ := (upd_relW v _ (P := fun a b => AMid₁ v.scratch s₀ St D S L R a ∧ AMid₁ v.scratch s₀' St D S L R b)
    fun a b h => ⟨h.1.args, by rw [q2]; exact h.2.args, by rw [h.1.sp, h.2.sp, q6]⟩).wp
    (F₁ := AAfter₁ s₀ St D S L) (F₂ := AAfter₁ s₀' St D S L) fun a b h => ⟨call1_after v h.1, call1_after v h.2⟩
  have m := (RelCT.taint (A := taint) (P := fun a b => AAfter₁ s₀ St D S L a ∧ AAfter₁ s₀' St D S L b) _
    (fun a b h => by
      refine agree_of (by rw [h.1.sp, h.2.sp, q6]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.x19, h.2.x19]
      · rw [h.1.x20, h.2.x20, q1]
      · rw [h.1.x21, h.2.x21, q2]
      · rw [h.1.x22, h.2.x22, q2]
      · rw [h.1.x23, h.2.x23]) hB).wp
    (F₁ := AMid₂ v.scratch s₀ St D S L R) (F₂ := AMid₂ v.scratch s₀' St D S L R) fun a b h => ⟨chain2_mid hp h.1, chain2_mid hp' h.2⟩
  have c₂ := (upd_relW v _ (P := fun a b => AMid₂ v.scratch s₀ St D S L R a ∧ AMid₂ v.scratch s₀' St D S L R b)
    fun a b h => ⟨h.1.args, by rw [q2]; exact h.2.args, by rw [h.1.sp, h.2.sp, q6]⟩).wp
    (F₁ := AAfter₂ s₀ St D S L) (F₂ := AAfter₂ s₀' St D S L) fun a b h =>
      ⟨call2_after v h.1, call2_after v h.2⟩
  have p := RelCT.taint (A := taint) (P := fun a b => AAfter₂ s₀ St D S L a ∧ AAfter₂ s₀' St D S L b) _
    (fun a b h => by
      refine agree_of (by rw [h.1.sp, h.2.sp, q6]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.x19, h.2.x19]
      · rw [h.1.x21, h.2.x21, q2]
      · rw [h.1.x22, h.2.x22, q2]
      · rw [h.1.x23, h.2.x23]
      · rw [h.1.x24, h.2.x24, q2]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem absorb_ct (v : Proof.CmacAes.AArch64.UpdateImpl) :
    ConstantTime isa (absorbAArch64 (64 + v.scratch)).pre (absorbAArch64 (64 + v.scratch)).pub (absorb v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.AArch64

end

/-!
# Streaming AES-CMAC on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of AES), a state
satisfying each precondition, and the shared contracts of
`Spec/Cmac/Contract.lean` (with no stack: the calls keep the return address in
`x30`, which each function saves in the scratch buffer).
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.Stream.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.CmacAes.AArch64 (update_keepsV subkeys_keepsV finalize_keepsV)

theorem init_keepsV (v : Ctr32Impl) : (init v.expand v.callee v.suffix).allInstrs keepsV = true := by
  simp only [init, Code.allInstrs, v.expandKeepsV, subkeys_keepsV v]; decide +kernel

theorem absorb_keepsV (v : Proof.CmacAes.AArch64.UpdateImpl) : (absorb v.callee).allInstrs keepsV = true := by
  simp only [absorb, absorbPre, absorbPost, held, clamp, fill, copy, chain1, chain2, Code.allInstrs,
    v.keepsV]
  decide +kernel

theorem finish_keepsV (v : Ctr32Impl) : (finish v.callee v.suffix).allInstrs keepsV = true := by
  simp only [finish, finPre, lastLen, Code.allInstrs, finalize_keepsV v]; decide +kernel

/-- The working space of `vg_cmac_aes_init` over `v`: the 512 bytes of the key
expansion, or what `vg_cmac_aes_subkeys` needs (`128 + v.scratch`), if more. -/
def initW (v : Ctr32Impl) : Nat := if v.scratch = 0 then 512 else 2176

/-- The working space of `vg_cmac_aes_finish` over `v`: what
`vg_cmac_aes_finalize` needs. -/
def finW (v : Ctr32Impl) : Nat := 128 + v.scratch

theorem initW_ok (v : Ctr32Impl) : 128 + v.scratch ≤ initW v ∧ 512 ≤ initW v := by
  rcases v.scratch_ok with h | h <;> simp only [initW, h] <;> decide

theorem init_correct (v : Ctr32Impl) (s : State) (hs : (initAArch64With (initW v)).pre s) :
    ∃ t s', Exec isa (init v.expand v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧
      (initAArch64With (initW v)).post s s' :=
  WP.withPreservedV (init_wp v (initW_ok v).1 (initW_ok v).2 hs) (init_keepsV v)

theorem absorb_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State)
    (hs : (absorbAArch64 (64 + v.scratch)).pre s) :
    ∃ t s', Exec isa (absorb v.callee) s t s' ∧ abiPreserved s s' ∧ (absorbAArch64 (64 + v.scratch)).post s s' :=
  WP.withPreservedV (absorb_wp v hs) (absorb_keepsV v)

theorem finish_correct (v : Ctr32Impl) (s : State) (hs : (finishAArch64With (finW v)).pre s) :
    ∃ t s', Exec isa (finish v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧
      (finishAArch64With (finW v)).post s s' :=
  WP.withPreservedV (finish_wp v (Nat.le_refl _) hs) (finish_keepsV v)

/-- A state satisfying `vg_cmac_aes_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 16 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

/-- `initSat` with `F` bytes of scratch. -/
def initSatW (F : Nat) : State := { initSat with wr := [⟨0x1000, 304⟩, ⟨0x4000, F⟩] }

/-- `vg_cmac_aes_init` with `scratch: *mut [u64; w]`. -/
def initScratchSigW (w : Nat) : Sig where
  params := [("state", .array true .u64 38), ("key", .slice false .u8 "key_len"),
    ("scratch", .array true .u64 w)]

/-- `aesInitContract`, whatever `scratch` is (of `w` words). -/
def initScratchContractW {M : ISA} (A : Abi M) (w : Nat) (stack : Nat := 0) : Contract M :=
  (initScratchSigW w).contract A
    (pre := fun state key keyLen _scratch => Spec.Cmac.aesInitPre A.ptrBits state key keyLen)
    (post := fun state key keyLen _scratch => Spec.Cmac.aesInitPost A.ptrBits state key keyLen)
    (stack := stack)

theorem init_verified (v : Ctr32Impl) :
    Verified AArch64.target (init v.expand v.callee v.suffix)
      (initScratchContractW AArch64.abi ((32 + initW v) / 8)) := by
  obtain hc := init_correct v
  obtain ht := init_ct v (initW_ok v).1 (initW_ok v).2
  rcases v.scratch_ok with h | h <;> simp only [initW, h, Nat.reduceAdd, Nat.reduceDiv, ite_true,
    show (2048 : Nat) ≠ 0 by decide, ite_false] at hc ht ⊢
  · exact Verified.of_correct hc ht (by
      sig_implies [initScratchContractW, initScratchSigW, Spec.Cmac.aesInitPre, Spec.Cmac.aesInitPost,
        initAArch64With, AArch64.abi, AArch64.argRegs] [initSatW, initSat] using initSatW 544)
  · exact Verified.of_correct hc ht (by
      sig_implies [initScratchContractW, initScratchSigW, Spec.Cmac.aesInitPre, Spec.Cmac.aesInitPost,
        initAArch64With, AArch64.abi, AArch64.argRegs] [initSatW, initSat] using initSatW 2208)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition (with no data). -/
def absorbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x3 => 0x3000 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

/-- `absorbSat` with `F` bytes of scratch. -/
def absorbSatW (F : Nat) : State := { absorbSat with wr := [⟨0x1000, 304⟩, ⟨0x4000, F⟩] }

/-- `vg_cmac_aes_absorb` with `scratch: *mut [u64; w]`: `w = 8 + n / 8` for a
chaining implementation that needs `n` bytes (`UpdateImpl.scratch`). -/
def absorbScratchSigW (w : Nat) : Sig where
  params := [("state", .array true .u64 38), ("rounds", .int .usize true),
    ("count", .int .u64 true), ("data", .slice false .u8 "len"),
    ("scratch", .array true .u64 w)]

/-- `aesAbsorbContract`, whatever `scratch` is (of `w` words). -/
def absorbScratchContractW {M : ISA} (A : Abi M) (w : Nat) (stack : Nat := 0) : Contract M :=
  (absorbScratchSigW w).contract A
    (pre := fun state rounds count data len _scratch =>
      Spec.Cmac.aesAbsorbPre A.ptrBits state rounds count data len)
    (post := fun state rounds count data len _scratch =>
      Spec.Cmac.aesAbsorbPost A.ptrBits state rounds count data len)
    (stack := stack)

theorem absorb_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target (absorb v.callee) (absorbScratchContractW AArch64.abi (8 + v.scratch / 8)) := by
  obtain hc := absorb_correct v
  obtain ht := absorb_ct v
  rcases v.scratch_ok with h | h <;> simp only [h, Nat.reduceAdd, Nat.reduceDiv] at hc ht ⊢
  · exact Verified.of_correct hc ht (by
      sig_implies [absorbScratchContractW, absorbScratchSigW, Spec.Cmac.aesAbsorbPre, Spec.Cmac.aesAbsorbPost,
        absorbAArch64, AArch64.abi, AArch64.argRegs] [absorbSatW, absorbSat] using absorbSatW 64)
  · exact Verified.of_correct hc ht (by
      sig_implies [absorbScratchContractW, absorbScratchSigW, Spec.Cmac.aesAbsorbPre, Spec.Cmac.aesAbsorbPost,
        absorbAArch64, AArch64.abi, AArch64.argRegs] [absorbSatW, absorbSat] using absorbSatW 2240)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition. -/
def finishSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x3 => 0x2000 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 2304⟩]

/-- `finishSat` with `F` bytes of scratch. -/
def finishSatW (F : Nat) : State := { finishSat with wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, F⟩] }

/-- `vg_cmac_aes_finish` with `scratch: *mut [u64; w]`. -/
def finishScratchSigW (w : Nat) : Sig where
  params := [("state", .array true .u64 38), ("rounds", .int .usize true),
    ("count", .int .u64 true), ("out", .array true .u8 16),
    ("scratch", .array true .u64 w)]

/-- `aesFinishContract`, whatever `scratch` is (of `w` words). -/
def finishScratchContractW {M : ISA} (A : Abi M) (w : Nat) (stack : Nat := 0) : Contract M :=
  (finishScratchSigW w).contract A
    (pre := fun state rounds count out _scratch => Spec.Cmac.aesFinishPre A.ptrBits state rounds count out)
    (post := fun state rounds count out _scratch => Spec.Cmac.aesFinishPost A.ptrBits state rounds count out)
    (stack := stack)

theorem finish_verified (v : Ctr32Impl) :
    Verified AArch64.target (finish v.callee v.suffix)
      (finishScratchContractW AArch64.abi ((16 + finW v) / 8)) := by
  obtain hc := finish_correct v
  obtain ht := finish_ct v (W := finW v) (Nat.le_refl _)
  rcases v.scratch_ok with h | h <;> simp only [finW, h, Nat.reduceAdd, Nat.reduceDiv] at hc ht ⊢
  · exact Verified.of_correct hc ht (by
      sig_implies [finishScratchContractW, finishScratchSigW, Spec.Cmac.aesFinishPre, Spec.Cmac.aesFinishPost,
        finishAArch64With, AArch64.abi, AArch64.argRegs] [finishSatW, finishSat] using finishSatW 144)
  · exact Verified.of_correct hc ht (by
      sig_implies [finishScratchContractW, finishScratchSigW, Spec.Cmac.aesFinishPre, Spec.Cmac.aesFinishPost,
        finishAArch64With, AArch64.abi, AArch64.argRegs] [finishSatW, finishSat] using finishSatW 2192)

end VG.Proof.CmacAes.Stream.AArch64

end

end

/-!
# Streaming AES-CMAC on AArch64, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackScratch`): 2304 bytes for `init` and `finish`, and for
`absorb` 64 more than the chaining implementation it calls needs. Their code uses no other stack: their calls keep
the return address in `x30`, which they save in the working space.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.Stream.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- A state satisfying `vg_cmac_aes_init`'s precondition, without the
working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 304⟩] }

theorem initFrameSat_pre544 : ∃ s, (Spec.Cmac.aesInitContract AArch64.abi 544).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, AArch64.abi, AArch64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem initFrameSat_pre2208 : ∃ s, (Spec.Cmac.aesInitContract AArch64.abi 2208).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, AArch64.abi, AArch64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, without the
working space (and with no data). -/
def absorbFrameSat : State := { absorbSat with wr := [⟨0x1000, 304⟩] }

theorem absorbFrameSat_pre64 : ∃ s, (Spec.Cmac.aesAbsorbContract AArch64.abi 64).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, AArch64.abi, AArch64.argRegs] [absorbFrameSat, absorbSat]
    using absorbFrameSat

theorem absorbFrameSat_pre2240 : ∃ s, (Spec.Cmac.aesAbsorbContract AArch64.abi 2240).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, AArch64.abi, AArch64.argRegs] [absorbFrameSat, absorbSat]
    using absorbFrameSat

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, without the
working space. -/
def finishFrameSat : State := { finishSat with wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩] }

theorem finishFrameSat_pre144 : ∃ s, (Spec.Cmac.aesFinishContract AArch64.abi 144).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, AArch64.abi, AArch64.argRegs] [finishFrameSat, finishSat]
    using finishFrameSat

theorem finishFrameSat_pre2192 : ∃ s, (Spec.Cmac.aesFinishContract AArch64.abi 2192).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, AArch64.abi, AArch64.argRegs] [finishFrameSat, finishSat]
    using finishFrameSat

/-- `vg_cmac_aes_init`, in a frame of `32 + initW v` bytes: its saved
registers and the working space of the functions it calls. -/
theorem init_framed (v : Ctr32Impl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch (32 + initW v) .x3 (init v.expand v.callee v.suffix))
      (Spec.Cmac.aesInitContract AArch64.abi (32 + initW v)) := by
  obtain hv := init_verified v
  rcases v.scratch_ok with h | h <;> simp only [initW, h, Nat.reduceAdd, Nat.reduceDiv, ite_true,
    show (2048 : Nat) ≠ 0 by decide, ite_false] at hv ⊢
  · exact AArch64.Verified.stackScratch (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64)
      (n := 68) (pre := Spec.Cmac.aesInitPre AArch64.abi.ptrBits)
      (post := Spec.Cmac.aesInitPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
      (bytes := 544) hv (by decide) (by decide)
      (fun vs m m₁ m₂ r hl _ => Proof.CmacAes.Stream.initPostOut_local _ vs m m₁ m₂ r hl) initFrameSat_pre544
  · exact AArch64.Verified.stackScratch (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64)
      (n := 276) (pre := Spec.Cmac.aesInitPre AArch64.abi.ptrBits)
      (post := Spec.Cmac.aesInitPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
      (bytes := 2208) hv (by decide) (by decide)
      (fun vs m m₁ m₂ r hl _ => Proof.CmacAes.Stream.initPostOut_local _ vs m m₁ m₂ r hl) initFrameSat_pre2208

/-- `vg_cmac_aes_absorb`, in a frame of `64 + n` bytes for a chaining
implementation that needs `n` (`UpdateImpl.scratch`): its saved registers
and the working space of the function it calls. -/
theorem absorb_framed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch (64 + v.scratch) .x5 (absorb v.callee))
      (Spec.Cmac.aesAbsorbContract AArch64.abi (64 + v.scratch)) := by
  obtain hv := absorb_verified v
  rcases v.scratch_ok with h | h <;> simp only [h, Nat.reduceAdd, Nat.reduceDiv] at hv ⊢
  · exact AArch64.Verified.stackScratch (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64)
      (n := 8) (pre := Spec.Cmac.aesAbsorbPre AArch64.abi.ptrBits)
      (post := Spec.Cmac.aesAbsorbPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
      (bytes := 64) hv (by decide) (by decide)
      (fun vs m m₁ m₂ r hl _ => Proof.CmacAes.Stream.absorbPostOut_local _ vs m m₁ m₂ r hl) absorbFrameSat_pre64
  · exact AArch64.Verified.stackScratch (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64)
      (n := 280) (pre := Spec.Cmac.aesAbsorbPre AArch64.abi.ptrBits)
      (post := Spec.Cmac.aesAbsorbPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
      (bytes := 2240) hv (by decide) (by decide)
      (fun vs m m₁ m₂ r hl _ => Proof.CmacAes.Stream.absorbPostOut_local _ vs m m₁ m₂ r hl) absorbFrameSat_pre2240

/-- `vg_cmac_aes_finish`, in a frame of `16 + finW v` bytes: its saved
registers and the working space of `vg_cmac_aes_finalize`. -/
theorem finish_framed (v : Ctr32Impl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch (16 + finW v) .x4 (finish v.callee v.suffix))
      (Spec.Cmac.aesFinishContract AArch64.abi (16 + finW v)) := by
  obtain hv := finish_verified v
  rcases v.scratch_ok with h | h <;> simp only [finW, h, Nat.reduceAdd, Nat.reduceDiv] at hv ⊢
  · exact AArch64.Verified.stackScratch (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64)
      (n := 18) (pre := Spec.Cmac.aesFinishPre AArch64.abi.ptrBits)
      (post := Spec.Cmac.aesFinishPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
      (bytes := 144) hv (by decide) (by decide)
      (fun vs m m₁ m₂ r hl _ => Proof.CmacAes.Stream.finishPostOut_local _ vs m m₁ m₂ r hl) finishFrameSat_pre144
  · exact AArch64.Verified.stackScratch (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64)
      (n := 274) (pre := Spec.Cmac.aesFinishPre AArch64.abi.ptrBits)
      (post := Spec.Cmac.aesFinishPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
      (bytes := 2192) hv (by decide) (by decide)
      (fun vs m m₁ m₂ r hl _ => Proof.CmacAes.Stream.finishPostOut_local _ vs m m₁ m₂ r hl) finishFrameSat_pre2192

/-! ## Without secret residue -/

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on a
region of at least `n` bytes there. -/
theorem agree_of {m₁ m₂ : Mem} {p : Addr} {L n : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    (hn : n ≤ L) : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact VG.Offset.contains_base _ (by omega_using [hn, hi]) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_using [hn, hi, hw]

/-- `vg_cmac_aes_absorb`'s postcondition reads the memory on return only
within the state's 304 bytes (`repr_congr_304`, as x86-64's
`Stream/X86_64/Scrub.lean` proves it), so it returns with every register it
may leave secret cleared and its whole frame zeroed
(`ScrubAll.withScrubAll`). -/
theorem absorbOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAll.ScrubAllOk (Spec.Cmac.aesAbsorbContract abi W) W (Spec.Cmac.aesAbsorbSig.retBits abi.ptrBits) :=
  ScrubAll.scrubAllOk_regs (sig := Spec.Cmac.aesAbsorbSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [st, _, _, _, _], _ =>
      simp only [Spec.Cmac.aesAbsorbSig, Sig.bufs, List.mem_cons, forall_eq_or_imp] at hb
      intro key msg hr hro hc hlt
      exact Proof.CmacAes.Stream.repr_congr_304 (agree_of hb.1 (by decide)) (h key msg hr hro hc hlt)

/-- `absorbOk` for the frame of `absorb_framed`. -/
theorem absorbOk_framed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    ScrubAll.ScrubAllOk (Spec.Cmac.aesAbsorbContract abi (64 + v.scratch)) (64 + v.scratch)
      (Spec.Cmac.aesAbsorbSig.retBits abi.ptrBits) :=
  absorbOk _ (by omega_using [])

/-- `vg_cmac_aes_absorb` in its frame (`absorb_framed`), scrubbed whole
(`ScrubAll.withScrubAll`): 64 bytes with a chaining implementation that needs
no working space, and 2240 with one that does, whose working space holds its
secrets (the cost of zeroing them is accepted). -/
def absorbReg (v : Proof.CmacAes.AArch64.UpdateImpl) : Registration Spec.Cmac.aesAbsorbApi AArch64.target :=
  let r : Registration Spec.Cmac.aesAbsorbApi AArch64.target :=
    { suffix := v.suffix
      code := Impl.StackScratch.AArch64.withStackScratch (64 + v.scratch) .x5 (absorb v.callee)
      verified := absorb_framed v
      consts := []
      stack := 64 + v.scratch }
  ScrubAll.withScrubAll r (absorbOk_framed v)

/-- `vg_cmac_aes_init`'s postcondition reads the memory on return only within
the state (`initPostOut_local`), so it returns with every register it may
leave secret cleared and its whole frame zeroed (`ScrubAll.withScrubAll`). -/
theorem initOk (W : Nat) (hW : 0 < W) :
    ScrubAll.ScrubAllOk (Spec.Cmac.aesInitContract abi W) W (Spec.Cmac.aesInitSig.retBits abi.ptrBits) :=
  ScrubAll.scrubAllOk_regs (sig := Spec.Cmac.aesInitSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.CmacAes.Stream.initPostOut_local _)

/-- `vg_cmac_aes_finish`'s postcondition reads the memory on return only within
`out` (`finishPostOut_local`), as `initOk`. -/
theorem finishOk (W : Nat) (hW : 0 < W) :
    ScrubAll.ScrubAllOk (Spec.Cmac.aesFinishContract abi W) W (Spec.Cmac.aesFinishSig.retBits abi.ptrBits) :=
  ScrubAll.scrubAllOk_regs (sig := Spec.Cmac.aesFinishSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.CmacAes.Stream.finishPostOut_local _)

/-- `vg_cmac_aes_init` over `v` in its frame (`init_framed`), scrubbed whole
(`ScrubAll.withScrubAll`): 544 bytes over an implementation that needs no
working space, else 2208. -/
def initReg (v : Ctr32Impl) : Registration Spec.Cmac.aesInitApi AArch64.target :=
  ScrubAll.withScrubAll
    { suffix := v.suffix
      code := Impl.StackScratch.AArch64.withStackScratch (32 + initW v) .x3 (init v.expand v.callee v.suffix)
      verified := init_framed v
      consts := []
      stack := 32 + initW v } (initOk _ (by omega_using []))

/-- `vg_cmac_aes_finish` over `v` in its frame (`finish_framed`), scrubbed
whole (`ScrubAll.withScrubAll`): 144 bytes over an implementation that needs
no working space, else 2192. -/
def finishReg (v : Ctr32Impl) : Registration Spec.Cmac.aesFinishApi AArch64.target :=
  ScrubAll.withScrubAll
    { suffix := v.suffix
      code := Impl.StackScratch.AArch64.withStackScratch (16 + finW v) .x4 (finish v.callee v.suffix)
      verified := finish_framed v
      consts := []
      stack := 16 + finW v } (finishOk _ (by omega_using []))

end VG.Proof.CmacAes.Stream.AArch64
