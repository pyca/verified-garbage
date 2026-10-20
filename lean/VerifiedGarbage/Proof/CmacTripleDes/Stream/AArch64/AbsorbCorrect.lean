module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.AbsorbBlocks
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Contract
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacTripleDes.Scratch
import VerifiedGarbage.Proof.CmacTripleDes.Stream.AArch64.Common
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.RoundLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

@[expose] public section

section

/-!
# Streaming TDEA-CMAC on AArch64: `vg_cmac_triple_des_absorb` up to the first `update`

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 8 - h)` bytes after them, and sets up the first run of `update`,
which chains the block held back if data is left (`AMid₁`).
-/

namespace VG.Proof.CmacTripleDes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacTripleDes.Stream.AArch64 VG.WriteBytes
open VG.Proof.CmacTripleDes.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`
and the scratch buffer `S`. -/
structure APre (s₀ : State) (St D S : Addr) (L : Nat) : Prop where
  x0 : s₀.gpr .x0 = St
  x2 : s₀.gpr .x2 = D
  x3 : (s₀.gpr .x3).toNat = L
  x4 : s₀.gpr .x4 = S
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 416⟩, ⟨S, 688⟩]
  st_d : (⟨St, 416⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 416⟩ : Region).Disjoint ⟨S, 688⟩
  d_s : (⟨D, L⟩ : Region).Disjoint ⟨S, 688⟩
  wSt : St.toNat + 416 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : S.toNat + 688 ≤ 2 ^ 64

theorem APre.of {s₀ : State} (h : absorbAArch64.pre s₀) :
    APre s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x4) (s₀.gpr .x3).toNat :=
  let ⟨a, b, c, d, e, f, g, h⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h⟩

section
variable {s₀ : State} {St D S : Addr} {L : Nat} (hp : APre s₀ St D S L)
include hp

theorem APre.lt : L < 2 ^ 64 := by rw [← hp.x3]; exact BitVec.isLt _

theorem APre.x3' : s₀.gpr .x3 = BitVec.ofNat 64 L := ofNat_toNat_eq hp.x3

theorem APre.inSt {d n : Nat} (h : d + n ≤ 416) : InRegions s₀.wr (St + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨St, 416⟩, by simp, Offset.contains_base _ h (by have := hp.wSt; omega_using [h])⟩

theorem APre.inS {d n : Nat} (h : d + n ≤ 688) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨S, 688⟩, by simp, Offset.contains_base _ h (by have := hp.wS; omega_using [h])⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ h (by have := hp.lt; omega_using [h, this])⟩

/-- The arguments of a run of `update` on `n` blocks at `Dd`, from a state
with the permissions of `s₀`. -/
theorem APre.uargs {s : State} {Dd : Addr} {n : Nat} (hx0 : s.gpr .x0 = St)
    (hx1 : s.gpr .x1 = St + BitVec.ofNat 64 400) (hx2 : s.gpr .x2 = Dd)
    (hx3 : s.gpr .x3 = BitVec.ofNat 64 n) (hx4 : s.gpr .x4 = S)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 8 * n < 2 ^ 64)
    (hdc : (⟨Dd, 8 * n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 400, 8⟩)
    (hds : (⟨Dd, 8 * n⟩ : Region).Disjoint ⟨S, 640⟩) (hwrap : Dd.toNat + 8 * n ≤ 2 ^ 64)
    (hcov : ∃ r' ∈ ([⟨D, L⟩, ⟨St, 416⟩, ⟨S, 688⟩] : List Region), ∃ off, Dd = r'.base + BitVec.ofNat 64 off ∧
      off + 8 * n ≤ r'.len) :
    UArgs s St (St + BitVec.ofNat 64 400) Dd S n := by
  have hw := hp.wSt
  have c400 : Region.Sub ⟨St + BitVec.ofNat 64 400, 8⟩ ⟨St, 416⟩ := Offset.sub_base St (by decide)
  have s640 : Region.Sub ⟨S, 640⟩ ⟨S, 688⟩ := Region.sub_prefix (by decide)
  exact
  { x0 := hx0, x1 := hx1, x2 := hx2, x3 := hx3, x4 := hx4, hn := hn
    wc := Offset.base_disjoint St (by decide) (by omega_using [])
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right s640
    dc := hdc, ds := hds
    cs := (hp.st_s.sub_left c400).sub_right s640
    wrapC := by rw [toNat_add_lt St hw (by decide)]; omega_using [hw]
    wrapD := hwrap
    wrapS := by have := hp.wS; omega_using [this]
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 416⟩, by simp, 0, by simp, by simp⟩
      · exact hcov
      · exact ⟨⟨St, 416⟩, by simp, 400, rfl, by simp⟩
      · exact ⟨⟨S, 688⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St, 416⟩, by simp, 400, rfl, by simp⟩
      · exact ⟨⟨S, 688⟩, by simp, 0, by simp, by simp⟩ }

end

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) (St D S : Addr) (c L : Nat) : Mem :=
  writeBytes (absSavedMem s₀ S) (St + BitVec.ofNat 64 (408 + held c))
    (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf c L))

/-- What the code before the first run of `update` leaves. -/
structure AMid₁ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 64 400) (St + BitVec.ofNat 64 408) S (b1Of (s₀.gpr .x1).toNat L)
  x19 : s.gpr .x19 = St
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (fOf (s₀.gpr .x1).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (leftOf (s₀.gpr .x1).toNat L)
  x23 : s.gpr .x23 = S
  other : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = m4 s₀ St D S (s₀.gpr .x1).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : Addr} {L : Nat} (hp : APre s₀ St D S L) :
    WP isa absorbPre s₀ (AMid₁ s₀ St D S L) := by
  generalize hc : (s₀.gpr .x1).toNat = c
  have hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  have hdx : s₀.gpr .x1 = BitVec.ofNat 64 c := ofNat_toNat_eq hc
  have hL := hp.lt
  have hw := hp.wSt
  have ⟨hfL, hfh⟩ := f_le c L
  have hh := held_le c
  obtain ⟨s₁, run₁, x19₁, x21₁, x22₁, x23₁, g₁, sp₁, m₁, rd₁, wr₁⟩ :=
    save_ok s₀ hp.x4 fun d _ h => hp.inS (by omega_using [h])
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (held_wp hcl (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), hdx]))
    fun s₂ ⟨x9₂, g₂, sp₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (fill_wp (St := St) (D := D) hL x9₂ (by rw [g₂ _ (by decide) (by decide), x22₁, hp.x3'])
    (by rw [g₂ _ (by decide) (by decide), x19₁, hp.x0]) (by rw [g₂ _ (by decide) (by decide), x21₁, hp.x2]))
    fun s₃ ⟨x8₃, x10₃, x6₃, x7₃, g₃, sp₃, m₃, rd₃, wr₃⟩ => ?_)
  have dCp : Region.Sub ⟨St + BitVec.ofNat 64 (408 + held c), fOf c L⟩ ⟨St, 416⟩ :=
    Offset.sub_base St (by omega_using [hfh])
  refine WP.seq (WP.mono (copy_ok s₃ (P := D) (C := St + BitVec.ofNat 64 (408 + held c)) (L := fOf c L)
    (by omega_using [hfh]) x7₃ x6₃ x8₃
    (fun i hi => by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact hp.inD (by omega_using [hfL, hi]))
    (fun i hi => by rw [wr₃, wr₂, wr₁, Offset.add_add]; exact hp.inSt (by omega_using [hfh, hi]))
    ((hp.st_d.sub_left dCp).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  -- The registers `chain1` reads, unchanged since `save`.
  have g (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x8) (d : r ≠ .x9) (e : r ≠ .x10) (f : r ≠ .x11) :
      s₄.gpr r = s₁.gpr r := by
    rw [h₄.other r a b c d, g₃ r a b c e f, g₂ r d e]
  refine WP.mono (chain1_wp (St := St) (S := S) hfL hL
    (by rw [g .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x21₁, hp.x2])
    (by rw [h₄.other _ (by decide) (by decide) (by decide) (by decide), x10₃])
    (by rw [g .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x22₁, hp.x3'])
    (by rw [g .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x19₁, hp.x0])
    (by rw [g .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x23₁]))
    fun s₅ h₅ => ?_
  obtain ⟨x21₅, x22₅, x3₅, x0₅, x1₅, x2₅, x4₅, sv₅, sp₅, m₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (hr : r ∈ preserved) (a : r ≠ .x21) (b : r ≠ .x22) : s₅.gpr r = s₁.gpr r := by
    have hcc : ∀ r ∈ preserved, r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 := by decide
    have hc := hcc r hr
    rw [sv₅ r hr a b, g r hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2]
  have hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃, rd₂, rd₁]
  have hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃, wr₂, wr₁]
  have hb1 : 8 * b1Of c L ≤ 8 := by unfold b1Of; split <;> omega_using []
  have c408 : Region.Sub ⟨St + BitVec.ofNat 64 408, 8 * b1Of c L⟩ ⟨St, 416⟩ :=
    Offset.sub_base St (by omega_using [hb1])
  have m₀ : s₅.mem = m4 s₀ St D S c L := by rw [m₅, h₄.mem, m₃, m₂, m₁, m4]
  subst hc
  refine ⟨hp.uargs x0₅ x1₅ x2₅ (by rw [x3₅, b1Of, leftOf]) x4₅ hrd hwr (by omega_using [hb1])
      (Offset.disjoint St (by omega_using []) (by omega_using [hb1]) (by omega_using []))
      ((hp.st_s.sub_left c408).sub_right (Region.sub_prefix (by decide)))
      (by rw [toNat_add_lt St hw (by decide)]; omega_using [hw, hb1])
      ⟨⟨St, 416⟩, by simp, 408, rfl, by simp; omega_using [hb1]⟩,
    by rw [k .x19 (by simp [preserved]) (by decide) (by decide), x19₁, hp.x0],
    x21₅, by rw [x22₅]; rfl, by rw [k .x23 (by simp [preserved]) (by decide) (by decide), x23₁],
    fun r hr a b c d => by rw [k r hr b c, g₁ r a b c d],
    by rw [sp₅, h₄.sp, sp₃, sp₂, sp₁], m₀, hrd, hwr⟩

end VG.Proof.CmacTripleDes.Stream.AArch64

end

/-!
# Streaming TDEA-CMAC on AArch64: `vg_cmac_triple_des_absorb` is correct

After `absorbPre`, the first run of `update` chains the block held back if
data is left (`b1`), the second the whole blocks of the data left but its
last 1 to 8 bytes (`nb`), and the last copy holds those back. If no data is
left (`len ≤ 8 - h`), the runs chain nothing and the copy copies nothing,
and the data is appended to the bytes held back (`repr_fill`); otherwise
`repr_chain`.
-/

namespace VG.Proof.CmacTripleDes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacTripleDes.Stream.AArch64 VG.WriteBytes
open VG.Proof.Cmac (bytesAt_frame)
open VG.Proof.CmacTripleDes.Stream (held held_le)

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega_using [hi]) (by omega_using [hp, hi])) hc

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 8 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 8 1 = [Spec.Aes.bytesAt m p 8] := by
  simp [Spec.Cmac.blocksAt]

/-- What the first part of `absorb` (up to and with the first run of `update`)
leaves, for the second. -/
structure AAfter₁ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = St
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (fOf (s₀.gpr .x1).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (leftOf (s₀.gpr .x1).toNat L)
  x23 : s.gpr .x23 = S
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorb₁_after {s₀ : State} {St D S : Addr} {L : Nat} (hp : APre s₀ St D S L) :
    WP isa absorb₁ s₀ (AAfter₁ s₀ St D S L) :=
  WP.seq (WP.mono (absorbPre_wp hp) fun _ h =>
    WP.mono (upd_wp h.args) fun _ h₆ =>
      ⟨by rw [h₆.saved _ (by simp [preserved]), h.x19], by rw [h₆.saved _ (by simp [preserved]), h.x21],
        by rw [h₆.saved _ (by simp [preserved]), h.x22], by rw [h₆.saved _ (by simp [preserved]), h.x23],
        by rw [h₆.sp, h.sp], by rw [h₆.rd, h.rd], by rw [h₆.wr, h.wr]⟩)

/-- What the second part (`chain2` and the second run of `update`) leaves,
for `absorbPost`. -/
structure AAfter₂ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = St
  x20 : s.gpr .x20 = BitVec.ofNat 64 (8 * nbOf (s₀.gpr .x1).toNat L)
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (fOf (s₀.gpr .x1).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (leftOf (s₀.gpr .x1).toNat L)
  x23 : s.gpr .x23 = S
  sp : s.sp = s₀.sp

theorem absorb₂_after {s₀ s : State} {St D S : Addr} {L : Nat} (hp : APre s₀ St D S L)
    (h : AAfter₁ s₀ St D S L s) : WP isa absorb₂ s (AAfter₂ s₀ St D S L) := by
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .x1).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have hsum := nb_le c L
  obtain ⟨x19₆, x21₆, x22₆, x23₆, sp₆, rd₆, wr₆⟩ := h
  rw [hc] at x21₆ x22₆
  refine WP.seq (WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_using [hL]) x22₆) fun s₇ h₇ => ?_)
  obtain ⟨x20₇, x3₇, x0₇, x1₇, x2₇, x4₇, sv₇, sp₇, m₇, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 8) = nbOf c L := rfl
  rw [hnb] at x20₇ x3₇
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L), 8 * nbOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega_using [hsum])
  have c400 : Region.Sub ⟨St + BitVec.ofNat 64 400, 8⟩ ⟨St, 416⟩ := Offset.sub_base St (by decide)
  have args₇ := hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf c L)) (n := nbOf c L)
    (by rw [x0₇, x19₆]) (by rw [x1₇, x19₆]) (by rw [x2₇, x21₆]) x3₇ (by rw [x4₇, x23₆])
    (by rw [rd₇, rd₆]) (by rw [wr₇, wr₆]) (by omega_using [hL, hsum]) ((hp.st_d.sub_left c400).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : nbOf c L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf c L)).isLt; omega_using []
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_arith)]; omega_using [hsum, this])
    ⟨⟨D, L⟩, by simp, fOf c L, rfl, by simp; omega_using [hsum]⟩
  refine WP.mono (upd_wp args₇) fun s₈ h₈ => ?_
  subst hc
  exact ⟨by rw [h₈.saved _ (by simp [preserved]), sv₇ _ (by simp [preserved]) (by decide), x19₆],
    by rw [h₈.saved _ (by simp [preserved]), x20₇],
    by rw [h₈.saved _ (by simp [preserved]), sv₇ _ (by simp [preserved]) (by decide), x21₆],
    by rw [h₈.saved _ (by simp [preserved]), sv₇ _ (by simp [preserved]) (by decide), x22₆],
    by rw [h₈.saved _ (by simp [preserved]), sv₇ _ (by simp [preserved]) (by decide), x23₆],
    by rw [h₈.sp, sp₇, sp₆]⟩

theorem absorb_wp {s₀ : State} (h0 : absorbAArch64.pre s₀) :
    WP isa absorb s₀ fun s' => ((∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp) ∧
      absorbAArch64.post s₀ s' := by
  have hp := APre.of h0
  generalize s₀.gpr .x0 = St at hp
  generalize s₀.gpr .x2 = D at hp
  generalize s₀.gpr .x4 = S at hp
  generalize (s₀.gpr .x3).toNat = L at hp
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .x1).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have hw := hp.wSt
  have hsw := hp.wS
  have ⟨hfL, hfh⟩ := f_le c L
  have hsum := nb_le c L
  have hh := held_le c
  refine WP.seq (WP.seq (WP.mono (absorbPre_wp hp) fun s₅ h₅ => ?_))
  obtain ⟨args₅, x19₅, x21₅, x22₅, x23₅, o₅, sp₅, m₅, rd₅, wr₅⟩ := h₅
  rw [hc] at args₅ x21₅ x22₅ m₅
  refine WP.mono (upd_wp args₅) fun s₆ h₆ => ?_
  have k₆ (r : Reg) (hr : r ∈ preserved) : s₆.gpr r = s₅.gpr r := h₆.saved r hr
  refine WP.seq (WP.seq (WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_using [hL])
    (by rw [k₆ .x22 (by simp [preserved]), x22₅])) fun s₇ h₇ => ?_))
  obtain ⟨x20₇, x3₇, x0₇, x1₇, x2₇, x4₇, sv₇, sp₇, m₇, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 8) = nbOf c L := rfl
  rw [hnb] at x20₇ x3₇
  have k₇ (r : Reg) (hr : r ∈ preserved) (a : r ≠ .x20) : s₇.gpr r = s₅.gpr r := by
    rw [sv₇ r hr a, k₆ r hr]
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L), 8 * nbOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega_using [hsum])
  have c400 : Region.Sub ⟨St + BitVec.ofNat 64 400, 8⟩ ⟨St, 416⟩ := Offset.sub_base St (by decide)
  have args₇ := hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf c L)) (n := nbOf c L)
    (by rw [x0₇, k₆ .x19 (by simp [preserved]), x19₅])
    (by rw [x1₇, k₆ .x19 (by simp [preserved]), x19₅])
    (by rw [x2₇, k₆ .x21 (by simp [preserved]), x21₅]) x3₇
    (by rw [x4₇, k₆ .x23 (by simp [preserved]), x23₅]) (by rw [rd₇, h₆.rd, rd₅])
    (by rw [wr₇, h₆.wr, wr₅]) (by omega_using [hL, hsum]) ((hp.st_d.sub_left c400).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : nbOf c L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf c L)).isLt; omega_using []
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_arith)]; omega_using [hsum, this])
    ⟨⟨D, L⟩, by simp, fOf c L, rfl, by simp; omega_using [hsum]⟩
  refine WP.mono (upd_wp args₇) fun s₈ h₈ => ?_
  have k₈ (r : Reg) (hr : r ∈ preserved) : s₈.gpr r = s₇.gpr r := h₈.saved r hr
  obtain ⟨s₉, run₉, x21₉, x22₉, x6₉, x7₉, x8₉, sv₉, sp₉, m₉, rd₉, wr₉⟩ := rest_ok (s := s₈) (D := D)
    (a := fOf c L) (x := leftOf c L) (n := nbOf c L) (by unfold leftOf; omega_using [hsum])
    (by rw [k₈ .x21 (by simp [preserved]), k₇ .x21 (by simp [preserved]) (by decide), x21₅])
    (by rw [k₈ .x20 (by simp [preserved]), x20₇])
    (by rw [k₈ .x22 (by simp [preserved]), k₇ .x22 (by simp [preserved]) (by decide), x22₅])
  refine WP.seq (WP.of_runBlock ⟨s₉, run₉, ?_⟩)
  have rd₉' : s₉.rd = s₀.rd := by rw [rd₉, h₈.rd, rd₇, h₆.rd, rd₅]
  have wr₉' : s₉.wr = s₀.wr := by rw [wr₉, h₈.wr, wr₇, h₆.wr, wr₅]
  have dR : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L + 8 * nbOf c L), restOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega_using [hsum])
  have hrr : restOf c L ≤ 8 := by unfold restOf nbOf leftOf; split <;> omega_arith
  have sR : Region.Sub ⟨St + BitVec.ofNat 64 408, restOf c L⟩ ⟨St, 416⟩ :=
    Offset.sub_base St (by omega_using [hrr])
  refine WP.seq (WP.mono (copy_ok s₉ (P := D + BitVec.ofNat 64 (fOf c L + 8 * nbOf c L))
    (C := St + BitVec.ofNat 64 408) (L := restOf c L) (by omega_using [hrr]) x7₉
    (by rw [x6₉, k₈ .x19 (by simp [preserved]), k₇ .x19 (by simp [preserved]) (by decide), x19₅]) x8₉
    (fun i hi => by rw [rd₉', wr₉', Offset.add_add]; exact hp.inD (by omega_using [hsum, hi]))
    (fun i hi => by rw [wr₉', Offset.add_add]; exact hp.inSt (by omega_using [hrr, hi]))
    ((hp.st_d.sub_left sR).symm.sub_left dR)) fun s₁₀ h₁₀ => ?_)
  have x23₁₀ : s₁₀.gpr .x23 = S := by
    rw [h₁₀.other _ (by decide) (by decide) (by decide) (by decide),
      sv₉ _ (by simp [preserved]) (by decide) (by decide),
      k₈ .x23 (by simp [preserved]), k₇ .x23 (by simp [preserved]) (by decide), x23₅]
  obtain ⟨s₁₁, run₁₁, slot₁₁, keep₁₁, sp₁₁, m₁₁⟩ := restore_ok s₁₀ x23₁₀
    (fun d _ h => by
      rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉']
      obtain ⟨r, hr, hc⟩ := hp.inS (d := d) (n := 8) (by omega_using [h])
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
  refine WP.of_runBlock ⟨s₁₁, run₁₁, ?_⟩
  -- The frames.
  have hlf : (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf c L)).length = fOf c L :=
    Proof.Cmac.bytesAt_length _ _ _
  have hlr : (Spec.Aes.bytesAt s₉.mem (D + BitVec.ofNat 64 (fOf c L + 8 * nbOf c L)) (restOf c L)).length =
    restOf c L := Proof.Cmac.bytesAt_length _ _ _
  have fS : Frame [⟨S + BitVec.ofNat 64 640, 40⟩] s₀.mem (absSavedMem s₀ S) := absSavedMem_frame _ _
  have fC1 : Frame [⟨St + BitVec.ofNat 64 (408 + held c), fOf c L⟩] (absSavedMem s₀ S) s₅.mem := by
    rw [m₅, m4]; exact writeBytes_frame _ _ _ (by rw [hlf]; exact Region.contains_self _ _)
  have f6 : Frame [⟨St + BitVec.ofNat 64 400, 8⟩, ⟨S, 640⟩] s₅.mem s₆.mem := h₆.frame
  have f8 : Frame [⟨St + BitVec.ofNat 64 400, 8⟩, ⟨S, 640⟩] s₆.mem s₈.mem := by
    rw [← m₇]; exact h₈.frame
  have fC2 : Frame [⟨St + BitVec.ofNat 64 408, restOf c L⟩] s₈.mem s₁₁.mem := by
    rw [m₁₁, h₁₀.mem, m₉]
    exact writeBytes_frame _ _ _ (by rw [← m₉, hlr]; exact Region.contains_self _ _)
  let K : List Region := [⟨S + BitVec.ofNat 64 640, 40⟩, ⟨St + BitVec.ofNat 64 (408 + held c), fOf c L⟩,
    ⟨St + BitVec.ofNat 64 400, 8⟩, ⟨S, 640⟩, ⟨St + BitVec.ofNat 64 408, restOf c L⟩]
  have F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  have F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  have F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  have F11 : Frame K s₀.mem s₁₁.mem := F8.trans (fC2.mono (by simp [K]))
  -- The key and the data are in none of these.
  have dK : ∀ r ∈ K, (⟨St, 400⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base S (by decide))
    · exact Offset.base_disjoint St (by omega_using []) (by omega_using [hfh])
    · exact Offset.base_disjoint St (by omega_using []) (by omega_using [])
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    · exact Offset.base_disjoint St (by omega_using []) (by omega_using [hrr])
  have dDat : ∀ r ∈ K, (⟨D, L⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.d_s.sub_right (Offset.sub_base S (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_using [hfh]))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by decide))
    · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_using [hrr]))
  have k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
  refine ⟨⟨fun r hr => ?_, by rw [sp₁₁, h₁₀.sp, sp₉, h₈.sp, sp₇, h₆.sp, sp₅]⟩, ?_⟩
  · -- The registers, restored from their slots.
    have Fp : Frame K.tail (absSavedMem s₀ S) s₁₁.mem :=
      ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
        ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
    have slot (d : Nat) (h₁ : 640 ≤ d) (h₂ : d + 8 ≤ 680) :
        s₁₀.mem.readW (S + BitVec.ofNat 64 d) 64 = (absSavedMem s₀ S).readW (S + BitVec.ofNat 64 d) 64 := by
      rw [← m₁₁]
      have sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 688⟩ := Offset.sub_base S (by omega_using [h₂])
      refine Fp.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hfh]))).symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
      · exact Offset.disjoint_base S (by omega_using [h₁]) (by omega_using [h₂])
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hrr]))).symm.sub_left sub
    have sl {r : Reg} {d : Nat} (h : (r, d) ∈ saved) : s₁₁.gpr r = s₀.gpr r := by
      have hd : 640 ≤ d ∧ d + 8 ≤ 680 := by
        simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
        omega
      rw [slot₁₁ r d h, slot d hd.1 hd.2, absSaved_slot s₀ S h]
    have hc' : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 →
        r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 := by decide
    have oth (r : Reg) (hr : r ∈ preserved) (a : r ≠ .x19) (b : r ≠ .x20) (c : r ≠ .x21) (d : r ≠ .x22)
        (e : r ≠ .x23) : s₁₁.gpr r = s₀.gpr r := by
      obtain ⟨n6, n7, n8, n9⟩ := hc' r hr a b c d e
      rw [keep₁₁ r a b c d e, h₁₀.other r n6 n7 n8 n9, sv₉ r hr c d, k₈ r hr, k₇ r hr b,
        o₅ r hr a c d e]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sl (d := 640) (by simp [saved])
    · exact sl (d := 648) (by simp [saved])
    · exact sl (d := 656) (by simp [saved])
    · exact sl (d := 664) (by simp [saved])
    · exact sl (d := 672) (by simp [saved])
    all_goals exact oth _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro key msg hr hcnt hlen
    rw [hp.x0] at hr ⊢
    rw [hp.x2, hp.x3]
    rw [hp.x3] at hlen
    have hcm : c = msg.length := by rw [← hc, hcnt, toNat_ofNat (by omega_using [hlen])]
    subst hcm
    have hsch := ((Proof.CmacTripleDes.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    have ciph : ∀ m : Mem, Frame K s₀.mem m →
        Proof.CmacTripleDes.AArch64.ciphAt m St = Spec.Cmac.tdes key := fun m hf => by
      simp only [Proof.CmacTripleDes.AArch64.ciphAt, Spec.Cmac.tdes]
      rw [Proof.CmacTripleDes.scheduleAt_congr fun i hi => frame_at hf dK (by omega_using [hw]) (by omega_using [hi]),
        hsch]
    -- The data, wherever it is read.
    have dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem D L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m D hab, bytesAt_frame hf dDat (by omega_using [hlen])]
    have fS' : Frame K s₀.mem (absSavedMem s₀ S) := fS.mono (by simp [K])
    -- The chaining value.
    have cv5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 400) 8 =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 400) 8 := by
      rw [bytesAt_frame fC1 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint St (by omega_using []) (by omega_using []) (by omega_using [hfh]))
          (by decide),
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).sub_right (Offset.sub_base S (by decide)))
          (by decide)]
    have cv11 : Spec.Aes.bytesAt s₁₁.mem (St + BitVec.ofNat 64 400) 8 =
        Spec.Aes.bytesAt s₈.mem (St + BitVec.ofNat 64 400) 8 :=
      bytesAt_frame fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint St (by omega_using []) (by omega_using []) (by omega_using [hrr]))
        (by decide)
    have out6 := h₆.out
    rw [ciph _ F5] at out6
    have out8 := h₈.out
    rw [m₇, ciph _ F6] at out8
    have hk : ∀ i < 400, s₁₁.mem (St + BitVec.ofNat 64 i) = s₀.mem (St + BitVec.ofNat 64 i) :=
      fun i hi => frame_at F11 dK (by omega_using [hw]) hi
    have hdl : (Spec.Aes.bytesAt s₀.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    have hb5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 408) (held msg.length + fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 408) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem D L).take (fOf msg.length L) := by
      have e := bytesAt_writeBytes (absSavedMem s₀ S) (St + BitVec.ofNat 64 408) (held msg.length)
        (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf msg.length L)) (by rw [hlf]; omega_using [hfh])
      rw [hlf] at e
      rw [m₅, m4, ← Offset.add_add, e,
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hh]))).sub_right
            (Offset.sub_base S (by decide)))
          (by omega_using [hh])]
      refine congrArg (_ ++ ·) ?_
      have := dat _ fS' 0 (fOf msg.length L) (by omega_using [hsum])
      rwa [k0, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem D L = d at hdl hb5 dat ⊢
    by_cases hx : leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      have hfL' : fOf msg.length L = L := by unfold leftOf at hx; omega_using [hsum, hx]
      have hb : b1Of msg.length L = 0 := by simp [b1Of, hx]
      have hn : nbOf msg.length L = 0 := by simp [nbOf, hx]
      have hr0 : restOf msg.length L = 0 := by simp [restOf, hn, hx]
      have m118 : s₁₁.mem = s₈.mem := by
        rw [m₁₁, h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem
          (D + BitVec.ofNat 64 (fOf msg.length L + 8 * nbOf msg.length L)) 0 = [] from rfl, writeBytes_nil]
      refine Proof.CmacTripleDes.Stream.repr_fill hr hk
        (by rw [hdl]; have := (f_le msg.length L).2; omega_using [hfL', this]) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 400) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 400) _
        rw [cv11, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
        exact cv5
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 408) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 408) _ ++ _
        have sub : Region.Sub ⟨St + BitVec.ofNat 64 408, held msg.length + L⟩ ⟨St, 416⟩ :=
          Offset.sub_base St (by omega_using [hfh, hfL'])
        have dj : ∀ r ∈ [⟨St + BitVec.ofNat 64 400, 8⟩, ⟨S, 640⟩],
            (⟨St + BitVec.ofNat 64 408, held msg.length + L⟩ : Region).Disjoint r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega_using []) (by omega_using [hfh, hfL']) (by omega_using [])
          · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
        have hb5' := hb5
        rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
        rw [m118, hdl, bytesAt_frame f8 dj (by omega_using [hfh, hfL']),
          bytesAt_frame f6 dj (by omega_using [hfh, hfL']), hb5']
    · -- The block held back is complete, and more blocks may follow.
      have hlt : 8 - held msg.length < L := by unfold leftOf fOf at hx; omega_using [hx]
      have hf' : fOf msg.length L = 8 - held msg.length := by unfold fOf; omega_using [hlt]
      have hb : b1Of msg.length L = 1 := by simp [b1Of, hx]
      have hn : nbOf msg.length L = Proof.CmacTripleDes.Stream.nblocks msg.length L := by
        simp only [nbOf, hx, ↓reduceIte]
        unfold leftOf Proof.CmacTripleDes.Stream.nblocks
        rw [hf']
      have hb5' := hb5
      rw [hf', Nat.add_sub_cancel' hh] at hb5'
      refine Proof.CmacTripleDes.Stream.repr_chain hr hk (by rw [hdl]; exact hlt) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 400) _ =
          Spec.Cmac.chain _ (Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 400) _)
            ([Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 408) _ ++ _] ++ _)
        rw [cv11, out8, out6, hb, blocksAt_one, cv5, Proof.Cmac.chain_append,
          Proof.CmacTripleDes.Stream.blocksAt_eq, dat _ F6 _ _ (by omega_using [hsum]), hb5', hdl, hf', hn]
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 408) _ = _
        have e := bytesAt_writeBytes_self s₈.mem (St + BitVec.ofNat 64 408)
          (xs := Spec.Aes.bytesAt s₈.mem (D + BitVec.ofNat 64 (fOf msg.length L + 8 * nbOf msg.length L))
            (restOf msg.length L)) (by rw [Proof.Cmac.bytesAt_length]; omega_using [hrr])
        rw [Proof.Cmac.bytesAt_length] at e
        have hr' : d.length - (8 - held msg.length) - 8 * Proof.CmacTripleDes.Stream.nblocks msg.length d.length =
            restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        rw [hr', m₁₁, h₁₀.mem, m₉, e, dat _ F8 _ _ (by omega_using [hsum]),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega_using []),
          List.drop_drop, hdl, ← hn, hf']

end VG.Proof.CmacTripleDes.Stream.AArch64
