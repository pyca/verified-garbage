import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.AbsorbBlocks

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

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`,
the scratch buffer `S` and the rounds `R`. -/
structure APre (s₀ : State) (St D S : Addr) (L R : Nat) : Prop where
  x0 : s₀.gpr .x0 = St
  x3 : s₀.gpr .x3 = D
  x4 : (s₀.gpr .x4).toNat = L
  x5 : s₀.gpr .x5 = S
  x1 : (s₀.gpr .x1).toNat = R
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 2304⟩]
  st_d : (⟨St, 304⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  d_s : (⟨D, L⟩ : Region).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem APre.of {s₀ : State} (h : absorbAArch64.pre s₀) :
    APre s₀ (s₀.gpr .x0) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

section
variable {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R)
include hp

theorem APre.lt : L < 2 ^ 64 := by rw [← hp.x4]; exact BitVec.isLt _

theorem APre.x4' : s₀.gpr .x4 = BitVec.ofNat 64 L := ofNat_toNat_eq hp.x4

theorem APre.x1' : s₀.gpr .x1 = BitVec.ofNat 64 R := ofNat_toNat_eq hp.x1

theorem APre.inSt {d n : Nat} (h : d + n ≤ 304) : InRegions s₀.wr (St + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ h (by have := hp.wSt; omega_arith)⟩

theorem APre.inS {d n : Nat} (h : d + n ≤ 2304) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ h (by have := hp.wS; omega_arith)⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ h (by have := hp.lt; omega_arith)⟩

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the permissions of `s₀`. -/
theorem APre.uargs {s : State} {Dd : Addr} {n : Nat} (hx0 : s.gpr .x0 = St)
    (hx1 : s.gpr .x1 = s₀.gpr .x1) (hx2 : s.gpr .x2 = St + BitVec.ofNat 64 272) (hx3 : s.gpr .x3 = Dd)
    (hx4 : s.gpr .x4 = BitVec.ofNat 64 n) (hx5 : s.gpr .x5 = S)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 16 * n < 2 ^ 64)
    (hdc : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨S, 2176⟩) (hwrap : Dd.toNat + 16 * n ≤ 2 ^ 64)
    (hcov : ∃ r' ∈ ([⟨D, L⟩, ⟨St, 304⟩, ⟨S, 2304⟩] : List Region), ∃ off, Dd = r'.base + BitVec.ofNat 64 off ∧
      off + 16 * n ≤ r'.len) :
    UArgs s St (St + BitVec.ofNat 64 272) Dd S R n := by
  have hw := hp.wSt
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  exact
  { x0 := hx0, x2 := hx2, x3 := hx3, x4 := hx4, x5 := hx5, rounds := hp.rounds, hn := hn
    x1 := by rw [hx1]; exact hp.x1'
    wc := Offset.base_disjoint St (by decide) (by omega_arith)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    dc := hdc, ds := hds
    cs := (hp.st_s.sub_left c272).sub_right (Region.sub_prefix (by decide))
    wrapC := by rw [toNat_add_lt St hw (by decide)]; omega_arith
    wrapD := hwrap
    wrapS := by have := hp.wS; omega_arith
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact hcov
      · exact ⟨⟨St, 304⟩, by simp, 272, rfl, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 272, rfl, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩ }

end

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) (St D S : Addr) (c L : Nat) : Mem :=
  writeBytes (absSavedMem s₀ S) (St + BitVec.ofNat 64 (288 + held c))
    (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf c L))

/-- What the code before the first call leaves. -/
structure AMid₁ (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 64 272) (St + BitVec.ofNat 64 288) S R (b1Of (s₀.gpr .x2).toNat L)
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

theorem absorbPre_wp {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R) :
    WP isa absorbPre s₀ (AMid₁ s₀ St D S L R) := by
  generalize hc : (s₀.gpr .x2).toNat = c
  have hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  have hdx : s₀.gpr .x2 = BitVec.ofNat 64 c := ofNat_toNat_eq hc
  have hL := hp.lt
  have hw := hp.wSt
  have ⟨hfL, hfh⟩ := f_le c L
  have hh := held_le c
  obtain ⟨s₁, run₁, x19₁, x20₁, x21₁, x22₁, x23₁, x2₁, g₁, sp₁, m₁, rd₁, wr₁⟩ :=
    save_ok s₀ hp.x5 fun d _ h => hp.inS (by omega_arith)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (held_wp hcl (by rw [x2₁, hdx])) fun s₂ ⟨x9₂, g₂, sp₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (fill_wp (St := St) (D := D) hL x9₂ (by rw [g₂ _ (by decide) (by decide), x22₁, hp.x4'])
    (by rw [g₂ _ (by decide) (by decide), x19₁, hp.x0]) (by rw [g₂ _ (by decide) (by decide), x21₁, hp.x3]))
    fun s₃ ⟨x8₃, x10₃, x6₃, x7₃, g₃, sp₃, m₃, rd₃, wr₃⟩ => ?_)
  have dCp : Region.Sub ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_arith)
  refine WP.seq (WP.mono (copy_ok s₃ (P := D) (C := St + BitVec.ofNat 64 (288 + held c)) (L := fOf c L)
    (by omega_arith) x7₃ x6₃ x8₃
    (fun i hi => by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact hp.inD (by omega_arith))
    (fun i hi => by rw [wr₃, wr₂, wr₁, Offset.add_add]; exact hp.inSt (by omega_arith))
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
    have hcc : ∀ r ∈ preserved, r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 := by decide
    have hc := hcc r hr
    rw [sv₅ r hr a b, g r hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2]
  have hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃, rd₂, rd₁]
  have hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃, wr₂, wr₁]
  have hb1 : 16 * b1Of c L ≤ 16 := by unfold b1Of; split <;> omega_arith
  have c288 : Region.Sub ⟨St + BitVec.ofNat 64 288, 16 * b1Of c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_arith)
  have m₀ : s₅.mem = m4 s₀ St D S c L := by rw [m₅, h₄.mem, m₃, m₂, m₁, m4]
  subst hc
  refine ⟨hp.uargs x0₅
      (by rw [x1₅, g .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x20₁]) x2₅ x3₅
      (by rw [x4₅, b1Of, leftOf]) x5₅ hrd hwr (by omega_arith)
      (Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith))
      ((hp.st_s.sub_left c288).sub_right (Region.sub_prefix (by decide)))
      (by rw [toNat_add_lt St hw (by decide)]; omega_arith)
      ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega_arith⟩,
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
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega_arith) (by omega_arith)) hc

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 16 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 16 1 = [Spec.Aes.bytesAt m p 16] := by
  simp [Spec.Cmac.blocksAt]

theorem absorb_wp (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀ : State} (h0 : absorbAArch64.pre s₀) :
    WP isa (absorb v.callee) s₀ fun s' => GprAbi s₀ s' ∧ absorbAArch64.post s₀ s' := by
  have hp := APre.of h0
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
  have hsum := nb_le c L
  have hh := held_le c
  refine WP.seq (WP.mono (absorbPre_wp hp) fun s₅ h₅ => ?_)
  obtain ⟨args₅, x19₅, x20₅, x21₅, x22₅, x23₅, o₅, sp₅, m₅, rd₅, wr₅⟩ := h₅
  rw [hc] at args₅ x21₅ x22₅ m₅
  refine WP.seq (WP.mono (upd_call v _ args₅) fun s₆ h₆ => ?_)
  have k₆ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₆.gpr r = s₅.gpr r := h₆.saved r hr h30
  refine WP.seq (WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_arith)
    (by rw [k₆ .x22 (by simp [preserved]) (by decide), x22₅])) fun s₇ h₇ => ?_)
  obtain ⟨x24₇, x4₇, x0₇, x1₇, x2₇, x3₇, x5₇, sv₇, sp₇, m₇, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at x24₇ x4₇
  have k₇ (r : Reg) (hr : r ∈ preserved) (a : r ≠ .x24) (h30 : r ≠ .x30) : s₇.gpr r = s₅.gpr r := by
    rw [sv₇ r hr a, k₆ r hr h30]
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L), 16 * nbOf c L⟩ ⟨D, L⟩ := Offset.sub_base D (by omega_arith)
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  have args₇ := hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf c L)) (n := nbOf c L)
    (by rw [x0₇, k₆ .x19 (by simp [preserved]) (by decide), x19₅])
    (by rw [x1₇, k₆ .x20 (by simp [preserved]) (by decide), x20₅])
    (by rw [x2₇, k₆ .x19 (by simp [preserved]) (by decide), x19₅])
    (by rw [x3₇, k₆ .x21 (by simp [preserved]) (by decide), x21₅]) x4₇
    (by rw [x5₇, k₆ .x23 (by simp [preserved]) (by decide), x23₅]) (by rw [rd₇, h₆.rd, rd₅])
    (by rw [wr₇, h₆.wr, wr₅]) (by omega_arith) ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : nbOf c L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf c L)).isLt; omega_arith
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_arith)]; omega_arith)
    ⟨⟨D, L⟩, by simp, fOf c L, rfl, by simp; omega_arith⟩
  refine WP.seq (WP.mono (upd_call v _ args₇) fun s₈ h₈ => ?_)
  have k₈ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₈.gpr r = s₇.gpr r := h₈.saved r hr h30
  obtain ⟨s₉, run₉, x21₉, x22₉, x6₉, x7₉, x8₉, sv₉, sp₉, m₉, rd₉, wr₉⟩ := rest_ok (s := s₈) (D := D)
    (a := fOf c L) (x := leftOf c L) (n := nbOf c L) (by unfold leftOf; omega_arith)
    (by rw [k₈ .x21 (by simp [preserved]) (by decide), k₇ .x21 (by simp [preserved]) (by decide) (by decide),
      x21₅])
    (by rw [k₈ .x24 (by simp [preserved]) (by decide), x24₇])
    (by rw [k₈ .x22 (by simp [preserved]) (by decide), k₇ .x22 (by simp [preserved]) (by decide) (by decide),
      x22₅])
  refine WP.seq (WP.of_runBlock ⟨s₉, run₉, ?_⟩)
  have rd₉' : s₉.rd = s₀.rd := by rw [rd₉, h₈.rd, rd₇, h₆.rd, rd₅]
  have wr₉' : s₉.wr = s₀.wr := by rw [wr₉, h₈.wr, wr₇, h₆.wr, wr₅]
  have dR : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L), restOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega_arith)
  have hrr : restOf c L ≤ 16 := by unfold restOf nbOf leftOf; split <;> omega_arith
  have sR : Region.Sub ⟨St + BitVec.ofNat 64 288, restOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_arith)
  refine WP.seq (WP.mono (copy_ok s₉ (P := D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L))
    (C := St + BitVec.ofNat 64 288) (L := restOf c L) (by omega_arith) x7₉
    (by rw [x6₉, k₈ .x19 (by simp [preserved]) (by decide), k₇ .x19 (by simp [preserved]) (by decide) (by decide),
      x19₅]) x8₉
    (fun i hi => by rw [rd₉', wr₉', Offset.add_add]; exact hp.inD (by omega_arith))
    (fun i hi => by rw [wr₉', Offset.add_add]; exact hp.inSt (by omega_arith))
    ((hp.st_d.sub_left sR).symm.sub_left dR)) fun s₁₀ h₁₀ => ?_)
  have x23₁₀ : s₁₀.gpr .x23 = S := by
    rw [h₁₀.other _ (by decide) (by decide) (by decide) (by decide),
      sv₉ _ (by simp [preserved]) (by decide) (by decide),
      k₈ .x23 (by simp [preserved]) (by decide), k₇ .x23 (by simp [preserved]) (by decide) (by decide), x23₅]
  obtain ⟨s₁₁, run₁₁, slot₁₁, keep₁₁, sp₁₁, m₁₁⟩ := restore_ok s₁₀ x23₁₀
    (fun d _ h => by
      rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉']
      obtain ⟨r, hr, hc⟩ := hp.inS (d := d) (n := 8) (by omega_arith)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
  refine WP.of_runBlock ⟨s₁₁, run₁₁, ?_⟩
  -- The frames.
  have hlf : (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf c L)).length = fOf c L := Proof.Cmac.bytesAt_length _ _ _
  have hlr : (Spec.Aes.bytesAt s₉.mem (D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L)) (restOf c L)).length =
    restOf c L := Proof.Cmac.bytesAt_length _ _ _
  have fS : Frame [⟨S + BitVec.ofNat 64 2176, 56⟩] s₀.mem (absSavedMem s₀ S) := absSavedMem_frame _ _
  have fC1 : Frame [⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩] (absSavedMem s₀ S) s₅.mem := by
    rw [m₅, m4]; exact writeBytes_frame _ _ _ (by rw [hlf]; exact Region.contains_self _ _)
  have f6 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩] s₅.mem s₆.mem := h₆.frame
  have f8 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩] s₆.mem s₈.mem := by
    rw [← m₇]; exact h₈.frame
  have fC2 : Frame [⟨St + BitVec.ofNat 64 288, restOf c L⟩] s₈.mem s₁₁.mem := by
    rw [m₁₁, h₁₀.mem, m₉]
    exact writeBytes_frame _ _ _ (by rw [← m₉, hlr]; exact Region.contains_self _ _)
  let K : List Region := [⟨S + BitVec.ofNat 64 2176, 56⟩, ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩,
    ⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩, ⟨St + BitVec.ofNat 64 288, restOf c L⟩]
  have F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  have F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  have F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  have F11 : Frame K s₀.mem s₁₁.mem := F8.trans (fC2.mono (by simp [K]))
  -- The key and the data are in none of these.
  have dK : ∀ r ∈ K, (⟨St, 272⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base S (by decide))
    · exact Offset.base_disjoint St (by omega_arith) (by omega_arith)
    · exact Offset.base_disjoint St (by omega_arith) (by omega_arith)
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    · exact Offset.base_disjoint St (by omega_arith) (by omega_arith)
  have dDat : ∀ r ∈ K, (⟨D, L⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.d_s.sub_right (Offset.sub_base S (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_arith))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by decide))
    · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_arith))
  have k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
  refine ⟨⟨fun r hr => ?_, by rw [sp₁₁, h₁₀.sp, sp₉, h₈.sp, sp₇, h₆.sp, sp₅]⟩, ?_⟩
  · -- The registers, restored from their slots.
    have Fp : Frame K.tail (absSavedMem s₀ S) s₁₁.mem :=
      ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
        ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
    have slot (d : Nat) (h₁ : 2176 ≤ d) (h₂ : d + 8 ≤ 2232) :
        s₁₀.mem.readW (S + BitVec.ofNat 64 d) 64 = (absSavedMem s₀ S).readW (S + BitVec.ofNat 64 d) 64 := by
      rw [← m₁₁]
      have sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 2304⟩ := Offset.sub_base S (by omega_arith)
      refine Fp.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_arith))).symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
      · exact Offset.disjoint_base S (by omega_arith) (by omega_arith)
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_arith))).symm.sub_left sub
    have sl {r : Reg} {d : Nat} (h : (r, d) ∈ saved) : s₁₁.gpr r = s₀.gpr r := by
      have hd : 2176 ≤ d ∧ d + 8 ≤ 2232 := by
        simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
        omega
      rw [slot₁₁ r d h, slot d hd.1 hd.2, absSaved_slot s₀ S h]
    have hc' : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x24 → r ≠ .x30 →
        r ≠ .x23 → r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 := by decide
    have oth (r : Reg) (hr : r ∈ preserved) (a : r ≠ .x19) (b : r ≠ .x20) (c : r ≠ .x21) (d : r ≠ .x22)
        (e : r ≠ .x24) (f : r ≠ .x30) (g : r ≠ .x23) : s₁₁.gpr r = s₀.gpr r := by
      obtain ⟨n6, n7, n8, n9⟩ := hc' r hr a b c d e f g
      rw [keep₁₁ r a b c d e f g, h₁₀.other r n6 n7 n8 n9, sv₉ r hr c d, k₈ r hr f, k₇ r hr e f,
        o₅ r hr a b c d g]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sl (d := 2176) (by simp [saved])
    · exact sl (d := 2184) (by simp [saved])
    · exact sl (d := 2192) (by simp [saved])
    · exact sl (d := 2200) (by simp [saved])
    · exact sl (d := 2224) (by simp [saved])
    · exact sl (d := 2208) (by simp [saved])
    · exact oth _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact oth _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact oth _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact oth _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact sl (d := 2216) (by simp [saved])
  · intro key msg hr hR hcnt hlen
    rw [hp.x0] at hr ⊢
    rw [hp.x3, hp.x4]
    rw [hp.x4] at hlen
    have hcm : c = msg.length := by rw [← hc, hcnt, toNat_ofNat (by omega_arith)]
    subst hcm
    have hRk : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.x1]; exact hR
    have hRb : 16 * (R + 1) ≤ 272 := by rcases hp.rounds with h | h | h <;> omega_arith
    have hsch := ((Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    rw [← hRk] at hsch
    have ciph : ∀ m : Mem, Frame K s₀.mem m →
        Spec.Cmac.aesWith R (Spec.Aes.bytesAt m St (16 * (R + 1))) = Spec.Cmac.aes key := fun m hf => by
      rw [bytesAt_frame hf (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega_arith), hsch,
        Spec.Cmac.aes, ← hRk]
    -- The data, wherever it is read.
    have dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem D L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m D hab, bytesAt_frame hf dDat (by omega_arith)]
    have fS' : Frame K s₀.mem (absSavedMem s₀ S) := fS.mono (by simp [K])
    -- The chaining value.
    have cv5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 272) 16 := by
      rw [bytesAt_frame fC1 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith))
          (by decide),
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).sub_right (Offset.sub_base S (by decide)))
          (by decide)]
    have cv11 : Spec.Aes.bytesAt s₁₁.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₈.mem (St + BitVec.ofNat 64 272) 16 :=
      bytesAt_frame fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith))
        (by decide)
    have out6 := h₆.out
    rw [ciph _ F5] at out6
    have out8 := h₈.out
    rw [m₇, ciph _ F6] at out8
    have hk : ∀ i < 272, s₁₁.mem (St + BitVec.ofNat 64 i) = s₀.mem (St + BitVec.ofNat 64 i) :=
      fun i hi => frame_at F11 dK (by omega_arith) hi
    have hdl : (Spec.Aes.bytesAt s₀.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    have hb5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 288) (held msg.length + fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 288) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem D L).take (fOf msg.length L) := by
      have e := bytesAt_writeBytes (absSavedMem s₀ S) (St + BitVec.ofNat 64 288) (held msg.length)
        (Spec.Aes.bytesAt (absSavedMem s₀ S) D (fOf msg.length L)) (by rw [hlf]; omega_arith)
      rw [hlf] at e
      rw [m₅, m4, ← Offset.add_add, e,
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by omega_arith))).sub_right (Offset.sub_base S (by decide)))
          (by omega_arith)]
      refine congrArg (_ ++ ·) ?_
      have := dat _ fS' 0 (fOf msg.length L) (by omega_arith)
      rwa [k0, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem D L = d at hdl hb5 dat ⊢
    by_cases hx : leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      have hfL' : fOf msg.length L = L := by unfold leftOf at hx; omega_arith
      have hb : b1Of msg.length L = 0 := by simp [b1Of, hx]
      have hn : nbOf msg.length L = 0 := by simp [nbOf, hx]
      have hr0 : restOf msg.length L = 0 := by simp [restOf, hn, hx]
      have m118 : s₁₁.mem = s₈.mem := by
        rw [m₁₁, h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem
          (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L)) 0 = [] from rfl, writeBytes_nil]
      refine Proof.Cmac.Stream.repr_fill hr hk (by rw [hdl]; have := (f_le msg.length L).2; omega_arith) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _
        rw [cv11, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
        exact cv5
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _
        have sub : Region.Sub ⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ ⟨St, 304⟩ :=
          Offset.sub_base St (by omega_arith)
        have dj : ∀ r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩],
            (⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ : Region).Disjoint r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith)
          · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
        have hb5' := hb5
        rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
        rw [m118, hdl, bytesAt_frame f8 dj (by omega_arith), bytesAt_frame f6 dj (by omega_arith), hb5']
    · -- The block held back is complete, and more blocks may follow.
      have hlt : 16 - held msg.length < L := by unfold leftOf fOf at hx; omega_arith
      have hf' : fOf msg.length L = 16 - held msg.length := by unfold fOf; omega_arith
      have hb : b1Of msg.length L = 1 := by simp [b1Of, hx]
      have hn : nbOf msg.length L = Proof.Cmac.Stream.nblocks msg.length L := by
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
          dat _ F6 _ _ (by omega_arith), hb5', hdl, hf', hn]
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = _
        have e := bytesAt_writeBytes_self s₈.mem (St + BitVec.ofNat 64 288)
          (xs := Spec.Aes.bytesAt s₈.mem (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L))
            (restOf msg.length L)) (by rw [Proof.Cmac.bytesAt_length]; omega_arith)
        rw [Proof.Cmac.bytesAt_length] at e
        have hr' : d.length - (16 - held msg.length) - 16 * Proof.Cmac.Stream.nblocks msg.length d.length =
            restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        rw [hr', m₁₁, h₁₀.mem, m₉, e, dat _ F8 _ _ (by omega_arith),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega_arith),
          List.drop_drop, hdl, ← hn, hf']

end VG.Proof.CmacAes.Stream.AArch64
