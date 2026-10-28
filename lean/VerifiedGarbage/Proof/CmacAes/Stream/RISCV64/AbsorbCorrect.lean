module

public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.AbsorbBlocks
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Streaming AES-CMAC on RISCV64: `vg_cmac_aes_absorb` is correct

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 16 - h)` bytes after them, and sets up the first call of
`vg_cmac_aes_update`, which chains the block held back if data is left
(`AMid₁`, `absorbPre_wp`). The second call chains the whole blocks of the
data left but its last 1 to 16 bytes (`nb`), and the last copy holds those
back. If no data is left (`len ≤ 16 - h`), the calls chain nothing and the
copy copies nothing, and the data is appended to the bytes held back
(`repr_fill`); otherwise `repr_chain`. As on PPC64LE (`Proof/CmacAes/Stream/PPC64LE/AbsorbCorrect.lean`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacAes.Stream.RISCV64 VG.WriteBytes
open VG.Proof.Cmac (bytesAt_frame)
open VG.Proof.AesCbc.RISCV64 (wp_sp)
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`,
the scratch buffer `S` and the rounds `R`. -/
structure APre (s₀ : State) (St D S : Addr) (L R : Nat) : Prop where
  a0 : s₀.gpr .a0 = St
  a3 : s₀.gpr .a3 = D
  a4 : (s₀.gpr .a4).toNat = L
  a5 : s₀.gpr .a5 = S
  a1 : (s₀.gpr .a1).toNat = R
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 2304⟩]
  st_d : (⟨St, 304⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  d_s : (⟨D, L⟩ : Region).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem APre.of {s₀ : State} (h : absorbRISCV64.pre s₀) :
    APre s₀ (s₀.gpr .a0) (s₀.gpr .a3) (s₀.gpr .a5) (s₀.gpr .a4).toNat (s₀.gpr .a1).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

section
variable {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R)
include hp

theorem APre.lt : L < 2 ^ 64 := by rw [← hp.a4]; exact BitVec.isLt _

theorem APre.a4' : s₀.gpr .a4 = BitVec.ofNat 64 L := ofNat_toNat_eq hp.a4

theorem APre.a1' : s₀.gpr .a1 = BitVec.ofNat 64 R := ofNat_toNat_eq hp.a1

theorem APre.inSt {d n : Nat} (h : d + n ≤ 304) : InRegions s₀.wr (St + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ h (by have := hp.wSt; omega)⟩

theorem APre.inS {d n : Nat} (h : d + n ≤ 2304) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ h (by have := hp.wS; omega)⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ h (by have := hp.lt; omega)⟩

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the permissions of `s₀`. -/
theorem APre.uargs {s : State} {Dd : Addr} {n : Nat} (h3 : s.gpr .a0 = St)
    (h4 : s.gpr .a1 = s₀.gpr .a1) (h5 : s.gpr .a2 = St + BitVec.ofNat 64 272) (h6 : s.gpr .a3 = Dd)
    (h7 : s.gpr .a4 = BitVec.ofNat 64 n) (h8 : s.gpr .a5 = S)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 16 * n < 2 ^ 64)
    (hdc : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨S, 2176⟩) (hwrap : Dd.toNat + 16 * n ≤ 2 ^ 64)
    (hcov : ∃ r' ∈ ([⟨D, L⟩, ⟨St, 304⟩, ⟨S, 2304⟩] : List Region), ∃ off, Dd = r'.base + BitVec.ofNat 64 off ∧
      off + 16 * n ≤ r'.len) :
    UArgs s St (St + BitVec.ofNat 64 272) Dd S R n := by
  have hw := hp.wSt
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  exact
  { a0 := h3, a2 := h5, a3 := h6, a4 := h7, a5 := h8, rounds := hp.rounds, hn := hn
    a1 := by rw [h4]; exact hp.a1'
    wc := Offset.base_disjoint St (by decide) (by omega)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    dc := hdc, ds := hds
    cs := (hp.st_s.sub_left c272).sub_right (Region.sub_prefix (by decide))
    wrapC := by rw [toNat_add_lt St hw (by decide)]; omega
    wrapD := hwrap
    wrapS := by have := hp.wS; omega
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

/-! ## Up to the first call -/

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) (St D S : Addr) (c L : Nat) : Mem :=
  writeBytes (absMem s₀ S) (St + BitVec.ofNat 64 (288 + held c))
    (Spec.Aes.bytesAt (absMem s₀ S) D (fOf c L))

/-- What the code before the first call leaves. -/
structure AMid₁ (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 64 272) (St + BitVec.ofNat 64 288) S R (b1Of (s₀.gpr .a2).toNat L)
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = s₀.gpr .a1
  s3 : s.gpr .s3 = D + BitVec.ofNat 64 (fOf (s₀.gpr .a2).toNat L)
  s4 : s.gpr .s4 = BitVec.ofNat 64 (leftOf (s₀.gpr .a2).toNat L)
  s6 : s.gpr .s6 = S
  other : ∀ r ∈ preserved, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → r ≠ .s6 → s.gpr r = s₀.gpr r
  mem : s.mem = m4 s₀ St D S (s₀.gpr .a2).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R) :
    WP isa absorbPre s₀ (AMid₁ s₀ St D S L R) := by
  generalize hc : (s₀.gpr .a2).toNat = c
  have hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  have hdx : s₀.gpr .a2 = BitVec.ofNat 64 c := ofNat_toNat_eq hc
  have hL := hp.lt
  have hw := hp.wSt
  have ⟨hfL, hfh⟩ := f_le c L
  have hh := held_le c
  refine WP.seq (WP.mono (save_wp s₀ hp.a5 fun d h => by
    rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, sv2_contains S (by omega)⟩) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (held_wp hcl (by
    rw [h₁.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hdx]))
    fun s₂ ⟨x1₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (fill_wp (St := St) (D := D) hL x1₂
    (by rw [g₂ _ (by decide), h₁.s4, hp.a4'])
    (by rw [g₂ _ (by decide), h₁.s1, hp.a0]) (by rw [g₂ _ (by decide), h₁.s3, hp.a3]))
    fun s₃ ⟨x2₃, x7₃, x5₃, x6₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  have dCp : Region.Sub ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩ ⟨St, 304⟩ :=
    Offset.sub_base St (by omega)
  refine WP.seq (WP.mono (copy_ok s₃ (P := D) (C := St + BitVec.ofNat 64 (288 + held c)) (L := fOf c L)
    (by omega) x6₃ x5₃ x2₃
    (fun i hi => by rw [rd₃, wr₃, rd₂, wr₂, h₁.rd, h₁.wr]; exact hp.inD (by omega))
    (fun i hi => by rw [wr₃, wr₂, h₁.wr, Offset.add_add]; exact hp.inSt (by omega))
    ((hp.st_d.sub_left dCp).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  -- The registers `chain1` reads, unchanged since `save`.
  have g (r : Reg) (a : r ≠ .a7) (b : r ≠ .t1) (c : r ≠ .t2) (d : r ≠ .t3) (e : r ≠ .t4) (f : r ≠ .t5)
      (h : r ≠ .t6) : s₄.gpr r = s₁.gpr r := by
    rw [h₄.other r c d f h, g₃ r a c d e f h, g₂ r b]
  refine WP.mono (chain1_wp (St := St) (S := S) hfL hL
    (by rw [g .s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.s3,
      hp.a3])
    (by rw [h₄.other _ (by decide) (by decide) (by decide) (by decide), x7₃])
    (by rw [g .s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.s4,
      hp.a4'])
    (by rw [g .s1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.s1,
      hp.a0])
    (by rw [g .s6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.s6]))
    fun s₅ h₅ => ?_
  obtain ⟨x3₅, x4₅, xa4₅, xa0₅, xa1₅, xa2₅, xa3₅, xa5₅, sv₅, m₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (hr : r ∈ preserved) (a : r ≠ .s3) (b : r ≠ .s4) : s₅.gpr r = s₁.gpr r := by
    obtain ⟨-, n1, n2, n3, n4, n5, n6, -, -, -, -, -, -, -, -, n7⟩ := preserved_ne r hr
    rw [sv₅ r hr a b, g r n7 n1 n2 n3 n4 n5 n6]
  have hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃, rd₂, h₁.rd]
  have hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃, wr₂, h₁.wr]
  have hb1 : 16 * b1Of c L ≤ 16 := by unfold b1Of; split <;> omega
  have c288 : Region.Sub ⟨St + BitVec.ofNat 64 288, 16 * b1Of c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  have m₀ : s₅.mem = m4 s₀ St D S c L := by rw [m₅, h₄.mem, m₃, m₂, h₁.mem, m4]
  subst hc
  refine ⟨hp.uargs xa0₅
      (by rw [xa1₅, g .s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        h₁.s2]) xa2₅ xa3₅
      (by rw [xa4₅, b1Of, leftOf]) xa5₅ hrd hwr (by omega)
      (Offset.disjoint St (by omega) (by omega) (by omega))
      ((hp.st_s.sub_left c288).sub_right (Region.sub_prefix (by decide)))
      (by rw [toNat_add_lt St hw (by decide)]; omega)
      ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega⟩,
    by rw [k .s1 (by decide) (by decide) (by decide), h₁.s1, hp.a0],
    by rw [k .s2 (by decide) (by decide) (by decide), h₁.s2],
    x3₅, by rw [x4₅]; rfl, by rw [k .s6 (by decide) (by decide) (by decide), h₁.s6],
    fun r hr a b c d e => by
      rw [k r hr c d, h₁.other r (preserved_ne r hr).1 a b c d e],
    m₀, hrd, hwr⟩

/-! ## The whole function -/

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega) (by omega)) hc

/-- The slots, within the scratch buffer. -/
theorem slots_sub (S : Addr) : Region.Sub ⟨sv2 S, 56⟩ ⟨S, 2304⟩ := by
  have := sv2_sub S (d := 0) (n := 56) (by decide); rwa [BitVec.add_zero] at this

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 16 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 16 1 = [Spec.Aes.bytesAt m p 16] := by
  simp [Spec.Cmac.blocksAt]

theorem absorb_wp {s₀ : State} (h0 : absorbRISCV64.pre s₀) :
    WP isa absorb s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.sp = s₀.sp ∧ absorbRISCV64.post s₀ s' := by
  have hp := APre.of h0
  generalize s₀.gpr .a0 = St at hp
  generalize s₀.gpr .a3 = D at hp
  generalize s₀.gpr .a5 = S at hp
  generalize (s₀.gpr .a4).toNat = L at hp
  generalize (s₀.gpr .a1).toNat = R at hp
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .a2).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have hw := hp.wSt
  have hsw := hp.wS
  have ⟨hfL, hfh⟩ := f_le c L
  have hsum := nb_le c L
  have hh := held_le c
  refine WP.seq (WP.mono (wp_sp (absorbPre_wp hp)) fun s₅ ⟨h₅, sp₅⟩ => ?_)
  obtain ⟨args₅, x1₅, x2₅, x3₅, x4₅, x6₅, o₅, m₅, rd₅, wr₅⟩ := h₅
  rw [hc] at args₅ x3₅ x4₅ m₅
  refine WP.seq (WP.mono (upd_call args₅) fun s₆ h₆ => ?_)
  have k₆ (r : Reg) (hr : r ∈ preserved) : s₆.gpr r = s₅.gpr r := h₆.saved r hr
  refine WP.seq (WP.mono (wp_sp (chain2_wp (x := leftOf c L) (by unfold leftOf; omega)
    (by rw [k₆ .s4 (by decide), x4₅]))) fun s₇ ⟨h₇, sp₇⟩ => ?_)
  obtain ⟨x5₇, xa4₇, xa0₇, xa1₇, xa2₇, xa3₇, xa5₇, sv₇, m₇, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at x5₇ xa4₇
  have k₇ (r : Reg) (hr : r ∈ preserved) (a : r ≠ .s5) : s₇.gpr r = s₅.gpr r := by
    rw [sv₇ r hr a, k₆ r hr]
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L), 16 * nbOf c L⟩ ⟨D, L⟩ := Offset.sub_base D (by omega)
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  have args₇ := hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf c L)) (n := nbOf c L)
    (by rw [xa0₇, k₆ .s1 (by decide), x1₅])
    (by rw [xa1₇, k₆ .s2 (by decide), x2₅])
    (by rw [xa2₇, k₆ .s1 (by decide), x1₅])
    (by rw [xa3₇, k₆ .s3 (by decide), x3₅]) xa4₇
    (by rw [xa5₇, k₆ .s6 (by decide), x6₅]) (by rw [rd₇, h₆.rd, rd₅])
    (by rw [wr₇, h₆.wr, wr₅]) (by omega) ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : nbOf c L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf c L)).isLt; omega
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega)]; omega)
    ⟨⟨D, L⟩, by simp, fOf c L, rfl, by simp; omega⟩
  refine WP.seq (WP.mono (upd_call args₇) fun s₈ h₈ => ?_)
  have k₈ (r : Reg) (hr : r ∈ preserved) : s₈.gpr r = s₇.gpr r := h₈.saved r hr
  refine WP.seq (WP.mono (wp_sp (rest_wp (s := s₈) (D := D) (a := fOf c L) (x := leftOf c L) (n := nbOf c L)
    (by unfold leftOf; omega)
    (by rw [k₈ .s3 (by decide), k₇ .s3 (by decide) (by decide), x3₅])
    (by rw [k₈ .s5 (by decide), x5₇])
    (by rw [k₈ .s4 (by decide), k₇ .s4 (by decide) (by decide), x4₅]))) fun s₉ ⟨h₉, sp₉⟩ => ?_)
  obtain ⟨x3₉, x4₉, x5₉, x6₉, x2₉, sv₉, m₉, rd₉, wr₉⟩ := h₉
  have rd₉' : s₉.rd = s₀.rd := by rw [rd₉, h₈.rd, rd₇, h₆.rd, rd₅]
  have wr₉' : s₉.wr = s₀.wr := by rw [wr₉, h₈.wr, wr₇, h₆.wr, wr₅]
  have dR : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L), restOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega)
  have hrr : restOf c L ≤ 16 := by unfold restOf nbOf leftOf; split <;> omega
  have sR : Region.Sub ⟨St + BitVec.ofNat 64 288, restOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  refine WP.seq (WP.mono (wp_sp (copy_ok s₉ (P := D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L))
    (C := St + BitVec.ofNat 64 288) (L := restOf c L) (by omega) x6₉
    (by rw [x5₉, k₈ .s1 (by decide), k₇ .s1 (by decide) (by decide), x1₅]) x2₉
    (fun i hi => by rw [rd₉', wr₉', Offset.add_add]; exact hp.inD (by omega))
    (fun i hi => by rw [wr₉', Offset.add_add]; exact hp.inSt (by omega))
    ((hp.st_d.sub_left sR).symm.sub_left dR))) fun s₁₀ ⟨h₁₀, sp₁₀⟩ => ?_)
  have x6₁₀ : s₁₀.gpr .s6 = S := by
    rw [h₁₀.other _ (by decide) (by decide) (by decide) (by decide), sv₉ _ (by decide) (by decide) (by decide),
      k₈ .s6 (by decide), k₇ .s6 (by decide) (by decide), x6₅]
  -- The frames.
  have hlf : (Spec.Aes.bytesAt (absMem s₀ S) D (fOf c L)).length = fOf c L := Proof.Cmac.bytesAt_length _ _ _
  have hlr : (Spec.Aes.bytesAt s₉.mem (D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L)) (restOf c L)).length =
    restOf c L := Proof.Cmac.bytesAt_length _ _ _
  have fS : Frame [⟨sv2 S, 56⟩] s₀.mem (absMem s₀ S) := absMem_frame _ _
  have fC1 : Frame [⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩] (absMem s₀ S) s₅.mem := by
    rw [m₅, m4]; exact writeBytes_frame _ _ _ (by rw [hlf]; exact Region.contains_self _ _)
  have f6 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩] s₅.mem s₆.mem := h₆.frame
  have f8 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩] s₆.mem s₈.mem := by
    rw [← m₇]; exact h₈.frame
  have fC2 : Frame [⟨St + BitVec.ofNat 64 288, restOf c L⟩] s₈.mem s₁₀.mem := by
    rw [h₁₀.mem, m₉]
    exact writeBytes_frame _ _ _ (by rw [← m₉, hlr]; exact Region.contains_self _ _)
  let K : List Region := [⟨sv2 S, 56⟩, ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩,
    ⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩, ⟨St + BitVec.ofNat 64 288, restOf c L⟩]
  have F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  have F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  have F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  have F10 : Frame K s₀.mem s₁₀.mem := F8.trans (fC2.mono (by simp [K]))
  -- The slots, which only the saves write.
  have Fp : Frame K.tail (absMem s₀ S) s₁₀.mem :=
    ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
      ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
  have sv₁₀ : Spill.Saved (sv2 S) (absG s₀ S) absSaved s₁₀.mem :=
    (Spill.saveMem_saved (by decide) s₀.mem (sv2 S) _).frame Fp fun p hp' r hr => by
      have hb := abs_bound p hp'
      have sub : Region.Sub ⟨sv2 S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 2304⟩ := sv2_sub S (by omega)
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
      · exact sv2_ws S (by omega)
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).symm.sub_left sub
  rw [restore, WP.block_append_iff]
  refine WP.mono (savePtr2_ok .s6) fun s₁₁ e => ?_
  subst e
  rw [x6₁₀, show absSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 absSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := absSaved) (B := sv2 S) (Align.align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) sv₁₀) fun s₁₂ r₁₂ => ?_
  · have := abs_bound p hp'
    show InRegions (s₁₀.rd ++ s₁₀.wr) _ 8
    rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉', hp.rd, hp.wr]
    exact ⟨⟨S, 2304⟩, by simp, sv2_contains S (by omega)⟩
  have g₀ (r : Reg) (hr : r ≠ .t0) : absG s₀ S r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · -- The registers, restored from their slots or never written.
    have h0 := (preserved_ne r hr).1
    rw [r₁₂.gpr_of (r := r) ?_, g₀ r h0]
    by_cases hv : r ∈ absSaved.map Prod.fst
    · left; exact hv
    · right
      have n1 : r ≠ .s1 := fun e => hv (by subst e; decide)
      have n2 : r ≠ .s2 := fun e => hv (by subst e; decide)
      have n3 : r ≠ .s3 := fun e => hv (by subst e; decide)
      have n4 : r ≠ .s4 := fun e => hv (by subst e; decide)
      have n5 : r ≠ .s5 := fun e => hv (by subst e; decide)
      have n6 : r ≠ .s6 := fun e => hv (by subst e; decide)
      obtain ⟨-, -, t2, t3, -, t5, t6, -⟩ := preserved_ne r hr
      rw [RegUpd.gpr_write_of_ne _ _ h0, h₁₀.other r t2 t3 t5 t6, sv₉ r hr n3 n4, k₈ r hr, k₇ r hr n5,
        o₅ r hr n1 n2 n3 n4 n6, g₀ r h0]
  · rw [r₁₂.gpr (.ra, 0) (by decide), g₀ .ra (by decide)]
  · rw [r₁₂.sp, RegUpd.sp_write, sp₁₀, sp₉, h₈.sp, sp₇, h₆.sp, sp₅]
  · intro key msg hr hR hcnt hlen
    rw [hp.a0] at hr
    show Spec.Cmac.Repr s₁₂.mem (s₀.gpr .a0) key (msg ++ Spec.Aes.bytesAt s₀.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat)
    rw [hp.a0, hp.a3, hp.a4, r₁₂.mem, RegUpd.mem_write]
    rw [hp.a4] at hlen
    have hcm : c = msg.length := by rw [← hc, hcnt, toNat_ofNat (by omega)]
    subst hcm
    have hRk : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.a1]; exact hR
    have hRb : 16 * (R + 1) ≤ 272 := by rcases hp.rounds with h | h | h <;> omega
    have hsch := ((Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    rw [← hRk] at hsch
    -- The key and the data are in none of the regions written.
    have dK : ∀ r ∈ K, (⟨St, 272⟩ : Region).Disjoint r := by
      intro r hr
      simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (slots_sub S)
      · exact Offset.base_disjoint St (by omega) (by omega)
      · exact Offset.base_disjoint St (by omega) (by omega)
      · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      · exact Offset.base_disjoint St (by omega) (by omega)
    have dDat : ∀ r ∈ K, (⟨D, L⟩ : Region).Disjoint r := by
      intro r hr
      simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hp.d_s.sub_right (slots_sub S)
      · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega))
      · exact hp.st_d.symm.sub_right (Offset.sub_base St (by decide))
      · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
      · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega))
    have ciph : ∀ m : Mem, Frame K s₀.mem m →
        Spec.Cmac.aesWith R (Spec.Aes.bytesAt m St (16 * (R + 1))) = Spec.Cmac.aes key := fun m hf => by
      rw [bytesAt_frame hf (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega), hsch,
        Spec.Cmac.aes, ← hRk]
    -- The data, wherever it is read.
    have dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem D L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m D hab, bytesAt_frame hf dDat (by omega)]
    have fS' : Frame K s₀.mem (absMem s₀ S) := fS.mono (by simp [K])
    -- The chaining value.
    have cv5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 272) 16 := by
      rw [bytesAt_frame fC1 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega) (by omega) (by omega))
          (by decide),
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).sub_right (slots_sub S))
          (by decide)]
    have cv10 : Spec.Aes.bytesAt s₁₀.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₈.mem (St + BitVec.ofNat 64 272) 16 :=
      bytesAt_frame fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega) (by omega) (by omega))
        (by decide)
    have out6 := h₆.out
    rw [ciph _ F5] at out6
    have out8 := h₈.out
    rw [m₇, ciph _ F6] at out8
    have hk : ∀ i < 272, s₁₀.mem (St + BitVec.ofNat 64 i) = s₀.mem (St + BitVec.ofNat 64 i) :=
      fun i hi => frame_at F10 dK (by omega) hi
    have hdl : (Spec.Aes.bytesAt s₀.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    have hb5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 288) (held msg.length + fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 288) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem D L).take (fOf msg.length L) := by
      have e := bytesAt_writeBytes (absMem s₀ S) (St + BitVec.ofNat 64 288) (held msg.length)
        (Spec.Aes.bytesAt (absMem s₀ S) D (fOf msg.length L)) (by rw [hlf]; omega)
      rw [hlf] at e
      rw [m₅, m4, ← Offset.add_add, e,
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).sub_right (slots_sub S))
          (by omega)]
      refine congrArg (_ ++ ·) ?_
      have := dat _ fS' 0 (fOf msg.length L) (by omega)
      rwa [BitVec.add_zero, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem D L = d at hdl hb5 dat ⊢
    by_cases hx : leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      have hfL' : fOf msg.length L = L := by unfold leftOf at hx; omega
      have hb : b1Of msg.length L = 0 := by simp [b1Of, hx]
      have hn : nbOf msg.length L = 0 := by simp [nbOf, hx]
      have hr0 : restOf msg.length L = 0 := by simp [restOf, hn, hx]
      have m108 : s₁₀.mem = s₈.mem := by
        rw [h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem
          (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L)) 0 = [] from rfl, writeBytes_nil]
      refine Proof.Cmac.Stream.repr_fill hr hk (by rw [hdl]; have := (f_le msg.length L).2; omega) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _
        rw [cv10, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
        exact cv5
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _
        have sub : Region.Sub ⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ ⟨St, 304⟩ :=
          Offset.sub_base St (by omega)
        have dj : ∀ r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩],
            (⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ : Region).Disjoint r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega) (by omega) (by omega)
          · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
        have hb5' := hb5
        rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
        rw [m108, hdl, bytesAt_frame f8 dj (by omega), bytesAt_frame f6 dj (by omega), hb5']
    · -- The block held back is complete, and more blocks may follow.
      have hlt : 16 - held msg.length < L := by unfold leftOf fOf at hx; omega
      have hf' : fOf msg.length L = 16 - held msg.length := by unfold fOf; omega
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
        rw [cv10, out8, out6, hb, blocksAt_one, cv5, Proof.Cmac.chain_append, Proof.Cmac.Stream.blocksAt_eq,
          dat _ F6 _ _ (by omega), hb5', hdl, hf', hn]
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = _
        have e := bytesAt_writeBytes_self s₈.mem (St + BitVec.ofNat 64 288)
          (xs := Spec.Aes.bytesAt s₈.mem (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L))
            (restOf msg.length L)) (by rw [Proof.Cmac.bytesAt_length]; omega)
        rw [Proof.Cmac.bytesAt_length] at e
        have hr' : d.length - (16 - held msg.length) - 16 * Proof.Cmac.Stream.nblocks msg.length d.length =
            restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        rw [hr', h₁₀.mem, m₉, e, dat _ F8 _ _ (by omega),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega),
          List.drop_drop, hdl, ← hn, hf']

end VG.Proof.CmacAes.Stream.RISCV64
