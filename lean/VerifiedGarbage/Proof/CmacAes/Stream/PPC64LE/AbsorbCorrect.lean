module

public import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.AbsorbBlocks
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Streaming AES-CMAC on PPC64LE: `vg_cmac_aes_absorb` is correct

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 16 - h)` bytes after them, and sets up the first call of
`vg_cmac_aes_update`, which chains the block held back if data is left
(`AMid₁`, `absorbPre_wp`). The second call chains the whole blocks of the
data left but its last 1 to 16 bytes (`nb`), and the last copy holds those
back. If no data is left (`len ≤ 16 - h`), the calls chain nothing and the
copy copies nothing, and the data is appended to the bytes held back
(`repr_fill`); otherwise `repr_chain`. As on AArch64.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.Stream.PPC64LE VG.WriteBytes
open VG.Proof.Cmac (bytesAt_frame)
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`,
the scratch buffer `S` and the rounds `R`. -/
structure APre (s₀ : State) (St D S : Addr) (L R : Nat) : Prop where
  r3 : s₀.gpr .r3 = St
  r6 : s₀.gpr .r6 = D
  r7 : (s₀.gpr .r7).toNat = L
  r8 : s₀.gpr .r8 = S
  r4 : (s₀.gpr .r4).toNat = R
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 2304⟩]
  st_d : (⟨St, 304⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  d_s : (⟨D, L⟩ : Region).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem APre.of {s₀ : State} (h : absorbPPC64LE.pre s₀) :
    APre s₀ (s₀.gpr .r3) (s₀.gpr .r6) (s₀.gpr .r8) (s₀.gpr .r7).toNat (s₀.gpr .r4).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

section
variable {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R)
include hp

theorem APre.lt : L < 2 ^ 64 := by rw [← hp.r7]; exact BitVec.isLt _

theorem APre.r7' : s₀.gpr .r7 = BitVec.ofNat 64 L := ofNat_toNat_eq hp.r7

theorem APre.r4' : s₀.gpr .r4 = BitVec.ofNat 64 R := ofNat_toNat_eq hp.r4

theorem APre.inSt {d n : Nat} (h : d + n ≤ 304) : InRegions s₀.wr (St + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ h (by have := hp.wSt; omega_arith)⟩

theorem APre.inS {d n : Nat} (h : d + n ≤ 2304) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ h (by have := hp.wS; omega_arith)⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ h (by have := hp.lt; omega_arith)⟩

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the permissions of `s₀`. -/
theorem APre.uargs {s : State} {Dd : Addr} {n : Nat} (h3 : s.gpr .r3 = St)
    (h4 : s.gpr .r4 = s₀.gpr .r4) (h5 : s.gpr .r5 = St + BitVec.ofNat 64 272) (h6 : s.gpr .r6 = Dd)
    (h7 : s.gpr .r7 = BitVec.ofNat 64 n) (h8 : s.gpr .r8 = S)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 16 * n < 2 ^ 64)
    (hdc : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨S, 2176⟩) (hwrap : Dd.toNat + 16 * n ≤ 2 ^ 64)
    (hcov : ∃ r' ∈ ([⟨D, L⟩, ⟨St, 304⟩, ⟨S, 2304⟩] : List Region), ∃ off, Dd = r'.base + BitVec.ofNat 64 off ∧
      off + 16 * n ≤ r'.len) :
    UArgs s St (St + BitVec.ofNat 64 272) Dd S R n := by
  have hw := hp.wSt
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  exact
  { r3 := h3, r5 := h5, r6 := h6, r7 := h7, r8 := h8, rounds := hp.rounds, hn := hn
    r4 := by rw [h4]; exact hp.r4'
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

/-! ## Up to the first call -/

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) (St D S : Addr) (c L : Nat) : Mem :=
  writeBytes (absMem s₀ S) (St + BitVec.ofNat 64 (288 + held c))
    (Spec.Aes.bytesAt (absMem s₀ S) D (fOf c L))

/-- What the code before the first call leaves. -/
structure AMid₁ (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 64 272) (St + BitVec.ofNat 64 288) S R (b1Of (s₀.gpr .r5).toNat L)
  r14 : s.gpr .r14 = St
  r15 : s.gpr .r15 = s₀.gpr .r4
  r16 : s.gpr .r16 = D + BitVec.ofNat 64 (fOf (s₀.gpr .r5).toNat L)
  r17 : s.gpr .r17 = BitVec.ofNat 64 (leftOf (s₀.gpr .r5).toNat L)
  r19 : s.gpr .r19 = S
  other : ∀ r ∈ preserved, r ≠ .r14 → r ≠ .r15 → r ≠ .r16 → r ≠ .r17 → r ≠ .r19 → s.gpr r = s₀.gpr r
  mem : s.mem = m4 s₀ St D S (s₀.gpr .r5).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R) :
    WP isa absorbPre s₀ (AMid₁ s₀ St D S L R) := by
  generalize hc : (s₀.gpr .r5).toNat = c
  have hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  have hdx : s₀.gpr .r5 = BitVec.ofNat 64 c := ofNat_toNat_eq hc
  have hL := hp.lt
  have hw := hp.wSt
  have ⟨hfL, hfh⟩ := f_le c L
  have hh := held_le c
  refine WP.seq (WP.mono (save_wp s₀ hp.r8 fun d _ h => hp.inS (by omega_arith)) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (held_wp hcl (by
    rw [h₁.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hdx]))
    fun s₂ ⟨x9₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (fill_wp (St := St) (D := D) hL x9₂
    (by rw [g₂ _ (by decide) (by decide), h₁.r17, hp.r7'])
    (by rw [g₂ _ (by decide) (by decide), h₁.r14, hp.r3]) (by rw [g₂ _ (by decide) (by decide), h₁.r16, hp.r6]))
    fun s₃ ⟨x12₃, x8₃, x10₃, x11₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  have dCp : Region.Sub ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩ ⟨St, 304⟩ :=
    Offset.sub_base St (by omega_arith)
  refine WP.seq (WP.mono (copy_ok s₃ (P := D) (C := St + BitVec.ofNat 64 (288 + held c)) (L := fOf c L)
    (by omega_arith) x11₃ x10₃ x12₃
    (fun i hi => by rw [rd₃, wr₃, rd₂, wr₂, h₁.rd, h₁.wr]; exact hp.inD (by omega_arith))
    (fun i hi => by rw [wr₃, wr₂, h₁.wr, Offset.add_add]; exact hp.inSt (by omega_arith))
    ((hp.st_d.sub_left dCp).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  -- The registers `chain1` reads, unchanged since `save`.
  have g (r : Reg) (a : r ≠ .r8) (b : r ≠ .r9) (c : r ≠ .r10) (d : r ≠ .r11) (e : r ≠ .r12) :
      s₄.gpr r = s₁.gpr r := by
    rw [h₄.other r b c d e, g₃ r a c d e, g₂ r b c]
  refine WP.mono (chain1_wp (St := St) (S := S) hfL hL
    (by rw [g .r16 (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r16, hp.r6])
    (by rw [h₄.other _ (by decide) (by decide) (by decide) (by decide), x8₃])
    (by rw [g .r17 (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r17, hp.r7'])
    (by rw [g .r14 (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r14, hp.r3])
    (by rw [g .r19 (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r19]))
    fun s₅ h₅ => ?_
  obtain ⟨x16₅, x17₅, x7₅, x3₅, x4₅, x5₅, x6₅, x8₅, sv₅, m₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (hr : r ∈ preserved) (a : r ≠ .r16) (b : r ≠ .r17) : s₅.gpr r = s₁.gpr r := by
    obtain ⟨-, -, -, -, -, -, n8, n9, n10, n11, n12⟩ := preserved_ne r hr
    rw [sv₅ r hr a b, g r n8 n9 n10 n11 n12]
  have hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃, rd₂, h₁.rd]
  have hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃, wr₂, h₁.wr]
  have hb1 : 16 * b1Of c L ≤ 16 := by unfold b1Of; split <;> omega_arith
  have c288 : Region.Sub ⟨St + BitVec.ofNat 64 288, 16 * b1Of c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_arith)
  have m₀ : s₅.mem = m4 s₀ St D S c L := by rw [m₅, h₄.mem, m₃, m₂, h₁.mem, m4]
  subst hc
  refine ⟨hp.uargs x3₅
      (by rw [x4₅, g .r15 (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r15]) x5₅ x6₅
      (by rw [x7₅, b1Of, leftOf]) x8₅ hrd hwr (by omega_arith)
      (Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith))
      ((hp.st_s.sub_left c288).sub_right (Region.sub_prefix (by decide)))
      (by rw [toNat_add_lt St hw (by decide)]; omega_arith)
      ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega_arith⟩,
    by rw [k .r14 (by decide) (by decide) (by decide), h₁.r14, hp.r3],
    by rw [k .r15 (by decide) (by decide) (by decide), h₁.r15],
    x16₅, by rw [x17₅]; rfl, by rw [k .r19 (by decide) (by decide) (by decide), h₁.r19],
    fun r hr a b c d e => by
      rw [k r hr c d, h₁.other r (preserved_ne r hr).1 a b c d e],
    m₀, hrd, hwr⟩

/-! ## The whole function -/

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega_arith) (by omega_arith)) hc

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 16 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 16 1 = [Spec.Aes.bytesAt m p 16] := by
  simp [Spec.Cmac.blocksAt]

theorem absorb_wp {s₀ : State} (h0 : absorbPPC64LE.pre s₀) :
    WP isa absorb s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧
      absorbPPC64LE.post s₀ s' := by
  have hp := APre.of h0
  generalize s₀.gpr .r3 = St at hp
  generalize s₀.gpr .r6 = D at hp
  generalize s₀.gpr .r8 = S at hp
  generalize (s₀.gpr .r7).toNat = L at hp
  generalize (s₀.gpr .r4).toNat = R at hp
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .r5).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have hw := hp.wSt
  have hsw := hp.wS
  have ⟨hfL, hfh⟩ := f_le c L
  have hsum := nb_le c L
  have hh := held_le c
  refine WP.seq (WP.mono (absorbPre_wp hp) fun s₅ h₅ => ?_)
  obtain ⟨args₅, x14₅, x15₅, x16₅, x17₅, x19₅, o₅, m₅, rd₅, wr₅⟩ := h₅
  rw [hc] at args₅ x16₅ x17₅ m₅
  refine WP.seq (WP.mono (upd_call args₅) fun s₆ h₆ => ?_)
  have k₆ (r : Reg) (hr : r ∈ preserved) : s₆.gpr r = s₅.gpr r := h₆.saved r hr
  refine WP.seq (WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_arith)
    (by rw [k₆ .r17 (by decide), x17₅])) fun s₇ h₇ => ?_)
  obtain ⟨x18₇, x7₇, x3₇, x4₇, x5₇, x6₇, x8₇, sv₇, m₇, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at x18₇ x7₇
  have k₇ (r : Reg) (hr : r ∈ preserved) (a : r ≠ .r18) : s₇.gpr r = s₅.gpr r := by
    rw [sv₇ r hr a, k₆ r hr]
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L), 16 * nbOf c L⟩ ⟨D, L⟩ := Offset.sub_base D (by omega_arith)
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  have args₇ := hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf c L)) (n := nbOf c L)
    (by rw [x3₇, k₆ .r14 (by decide), x14₅])
    (by rw [x4₇, k₆ .r15 (by decide), x15₅])
    (by rw [x5₇, k₆ .r14 (by decide), x14₅])
    (by rw [x6₇, k₆ .r16 (by decide), x16₅]) x7₇
    (by rw [x8₇, k₆ .r19 (by decide), x19₅]) (by rw [rd₇, h₆.rd, rd₅])
    (by rw [wr₇, h₆.wr, wr₅]) (by omega_arith) ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : nbOf c L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf c L)).isLt; omega_arith
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_arith)]; omega_arith)
    ⟨⟨D, L⟩, by simp, fOf c L, rfl, by simp; omega_arith⟩
  refine WP.seq (WP.mono (upd_call args₇) fun s₈ h₈ => ?_)
  have k₈ (r : Reg) (hr : r ∈ preserved) : s₈.gpr r = s₇.gpr r := h₈.saved r hr
  refine WP.seq (WP.mono (rest_wp (s := s₈) (D := D) (a := fOf c L) (x := leftOf c L) (n := nbOf c L)
    (by unfold leftOf; omega_arith)
    (by rw [k₈ .r16 (by decide), k₇ .r16 (by decide) (by decide), x16₅])
    (by rw [k₈ .r18 (by decide), x18₇])
    (by rw [k₈ .r17 (by decide), k₇ .r17 (by decide) (by decide), x17₅])) fun s₉ h₉ => ?_)
  obtain ⟨x16₉, x17₉, x10₉, x11₉, x12₉, sv₉, m₉, rd₉, wr₉⟩ := h₉
  have rd₉' : s₉.rd = s₀.rd := by rw [rd₉, h₈.rd, rd₇, h₆.rd, rd₅]
  have wr₉' : s₉.wr = s₀.wr := by rw [wr₉, h₈.wr, wr₇, h₆.wr, wr₅]
  have dR : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L), restOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega_arith)
  have hrr : restOf c L ≤ 16 := by unfold restOf nbOf leftOf; split <;> omega_arith
  have sR : Region.Sub ⟨St + BitVec.ofNat 64 288, restOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_arith)
  refine WP.seq (WP.mono (copy_ok s₉ (P := D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L))
    (C := St + BitVec.ofNat 64 288) (L := restOf c L) (by omega_arith) x11₉
    (by rw [x10₉, k₈ .r14 (by decide), k₇ .r14 (by decide) (by decide), x14₅]) x12₉
    (fun i hi => by rw [rd₉', wr₉', Offset.add_add]; exact hp.inD (by omega_arith))
    (fun i hi => by rw [wr₉', Offset.add_add]; exact hp.inSt (by omega_arith))
    ((hp.st_d.sub_left sR).symm.sub_left dR)) fun s₁₀ h₁₀ => ?_)
  have x19₁₀ : s₁₀.gpr .r19 = S := by
    rw [h₁₀.other _ (by decide) (by decide) (by decide) (by decide), sv₉ _ (by decide) (by decide) (by decide),
      k₈ .r19 (by decide), k₇ .r19 (by decide) (by decide), x19₅]
  -- The frames.
  have hlf : (Spec.Aes.bytesAt (absMem s₀ S) D (fOf c L)).length = fOf c L := Proof.Cmac.bytesAt_length _ _ _
  have hlr : (Spec.Aes.bytesAt s₉.mem (D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L)) (restOf c L)).length =
    restOf c L := Proof.Cmac.bytesAt_length _ _ _
  have fS : Frame [⟨S + BitVec.ofNat 64 2176, 56⟩] s₀.mem (absMem s₀ S) := absMem_frame _ _
  have fC1 : Frame [⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩] (absMem s₀ S) s₅.mem := by
    rw [m₅, m4]; exact writeBytes_frame _ _ _ (by rw [hlf]; exact Region.contains_self _ _)
  have f6 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩] s₅.mem s₆.mem := h₆.frame
  have f8 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩] s₆.mem s₈.mem := by
    rw [← m₇]; exact h₈.frame
  have fC2 : Frame [⟨St + BitVec.ofNat 64 288, restOf c L⟩] s₈.mem s₁₀.mem := by
    rw [h₁₀.mem, m₉]
    exact writeBytes_frame _ _ _ (by rw [← m₉, hlr]; exact Region.contains_self _ _)
  let K : List Region := [⟨S + BitVec.ofNat 64 2176, 56⟩, ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩,
    ⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩, ⟨St + BitVec.ofNat 64 288, restOf c L⟩]
  have F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  have F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  have F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  have F10 : Frame K s₀.mem s₁₀.mem := F8.trans (fC2.mono (by simp [K]))
  -- The slots, which only the saves write.
  have Fp : Frame K.tail (absMem s₀ S) s₁₀.mem :=
    ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
      ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
  have sv₁₀ : Spill.Saved S (saveG s₀) saved s₁₀.mem :=
    (Spill.saveMem_saved (by decide) s₀.mem S _).frame Fp fun p hp' r hr => by
      have hb := abs_bound p hp'
      have sub : Region.Sub ⟨S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 2304⟩ := Offset.sub_base S (by omega_arith)
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_arith))).symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
      · exact Offset.disjoint_base S (by omega_arith) (by omega_arith)
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_arith))).symm.sub_left sub
  rw [restore, show saved.map (fun (r, d) => Instr.load .d r .r19 d) = Spill.restoreCode .r19 saved from rfl]
  refine Spill.restore_ok (b := .r19) (l := saved) (by decide) x19₁₀ (by decide) (by decide)
    (fun p hp' => ?_) sv₁₀ fun s₁₁ r₁₁ => WP.cons exec_mtlr (wp_nil ⟨fun r hr => ?_, ?_, ?_⟩)
  · have := abs_bound p hp'
    rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉']; exact in_wr (hp.inS (by omega_arith))
  · -- The registers, restored from their slots or never written.
    show s₁₁.gpr r = _
    rw [r₁₁.gpr_of (r := r) ?_, saveG_ne (preserved_ne r hr).1]
    by_cases hv : r ∈ saved.map Prod.fst
    · left; exact hv
    · right
      have n14 : r ≠ .r14 := fun e => hv (by subst e; decide)
      have n15 : r ≠ .r15 := fun e => hv (by subst e; decide)
      have n16 : r ≠ .r16 := fun e => hv (by subst e; decide)
      have n17 : r ≠ .r17 := fun e => hv (by subst e; decide)
      have n18 : r ≠ .r18 := fun e => hv (by subst e; decide)
      have n19 : r ≠ .r19 := fun e => hv (by subst e; decide)
      obtain ⟨h0, -, -, -, -, -, -, n9, n10, n11, n12⟩ := preserved_ne r hr
      rw [h₁₀.other r n9 n10 n11 n12, sv₉ r hr n16 n17, k₈ r hr, k₇ r hr n18, o₅ r hr n14 n15 n16 n17 n19,
        saveG_ne h0]
  · show s₁₁.gpr .r0 = _
    rw [r₁₁.gpr (.r0, 2176) (by decide)]; exact saveG_r0 s₀
  · intro key msg hr hR hcnt hlen
    rw [hp.r3] at hr
    show Spec.Cmac.Repr s₁₁.mem (s₀.gpr .r3) key (msg ++ Spec.Aes.bytesAt s₀.mem (s₀.gpr .r6) (s₀.gpr .r7).toNat)
    rw [hp.r3, hp.r6, hp.r7, r₁₁.mem]
    rw [hp.r7] at hlen
    have hcm : c = msg.length := by rw [← hc, hcnt, toNat_ofNat (by omega_arith)]
    subst hcm
    have hRk : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.r4]; exact hR
    have hRb : 16 * (R + 1) ≤ 272 := by rcases hp.rounds with h | h | h <;> omega_arith
    have hsch := ((Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    rw [← hRk] at hsch
    -- The key and the data are in none of the regions written.
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
    have ciph : ∀ m : Mem, Frame K s₀.mem m →
        Spec.Cmac.aesWith R (Spec.Aes.bytesAt m St (16 * (R + 1))) = Spec.Cmac.aes key := fun m hf => by
      rw [bytesAt_frame hf (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega_arith), hsch,
        Spec.Cmac.aes, ← hRk]
    -- The data, wherever it is read.
    have dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem D L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m D hab, bytesAt_frame hf dDat (by omega_arith)]
    have fS' : Frame K s₀.mem (absMem s₀ S) := fS.mono (by simp [K])
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
    have cv10 : Spec.Aes.bytesAt s₁₀.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₈.mem (St + BitVec.ofNat 64 272) 16 :=
      bytesAt_frame fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith))
        (by decide)
    have out6 := h₆.out
    rw [ciph _ F5] at out6
    have out8 := h₈.out
    rw [m₇, ciph _ F6] at out8
    have hk : ∀ i < 272, s₁₀.mem (St + BitVec.ofNat 64 i) = s₀.mem (St + BitVec.ofNat 64 i) :=
      fun i hi => frame_at F10 dK (by omega_arith) hi
    have hdl : (Spec.Aes.bytesAt s₀.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    have hb5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 288) (held msg.length + fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 288) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem D L).take (fOf msg.length L) := by
      have e := bytesAt_writeBytes (absMem s₀ S) (St + BitVec.ofNat 64 288) (held msg.length)
        (Spec.Aes.bytesAt (absMem s₀ S) D (fOf msg.length L)) (by rw [hlf]; omega_arith)
      rw [hlf] at e
      rw [m₅, m4, ← Offset.add_add, e,
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by omega_arith))).sub_right (Offset.sub_base S (by decide)))
          (by omega_arith)]
      refine congrArg (_ ++ ·) ?_
      have := dat _ fS' 0 (fOf msg.length L) (by omega_arith)
      rwa [BitVec.add_zero, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem D L = d at hdl hb5 dat ⊢
    by_cases hx : leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      have hfL' : fOf msg.length L = L := by unfold leftOf at hx; omega_arith
      have hb : b1Of msg.length L = 0 := by simp [b1Of, hx]
      have hn : nbOf msg.length L = 0 := by simp [nbOf, hx]
      have hr0 : restOf msg.length L = 0 := by simp [restOf, hn, hx]
      have m108 : s₁₀.mem = s₈.mem := by
        rw [h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem
          (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L)) 0 = [] from rfl, writeBytes_nil]
      refine Proof.Cmac.Stream.repr_fill hr hk (by rw [hdl]; have := (f_le msg.length L).2; omega_arith) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _
        rw [cv10, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
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
        rw [m108, hdl, bytesAt_frame f8 dj (by omega_arith), bytesAt_frame f6 dj (by omega_arith), hb5']
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
        rw [cv10, out8, out6, hb, blocksAt_one, cv5, Proof.Cmac.chain_append, Proof.Cmac.Stream.blocksAt_eq,
          dat _ F6 _ _ (by omega_arith), hb5', hdl, hf', hn]
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = _
        have e := bytesAt_writeBytes_self s₈.mem (St + BitVec.ofNat 64 288)
          (xs := Spec.Aes.bytesAt s₈.mem (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L))
            (restOf msg.length L)) (by rw [Proof.Cmac.bytesAt_length]; omega_arith)
        rw [Proof.Cmac.bytesAt_length] at e
        have hr' : d.length - (16 - held msg.length) - 16 * Proof.Cmac.Stream.nblocks msg.length d.length =
            restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        rw [hr', h₁₀.mem, m₉, e, dat _ F8 _ _ (by omega_arith),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega_arith),
          List.drop_drop, hdl, ← hn, hf']

end VG.Proof.CmacAes.Stream.PPC64LE
