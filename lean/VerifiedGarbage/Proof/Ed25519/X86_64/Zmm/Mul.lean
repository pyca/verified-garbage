module
public import VerifiedGarbage.Proof.Ed25519.X86_64.CombLoop
public import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Entry
public import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Half
public import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Select
import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Halves
public import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Digits
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Ed25519.BaseTable
public import VerifiedGarbage.Proof.Ed25519.Group.Extended
import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Consts
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Part1
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Impl.Ed25519.X86_64.CombIfma
import VerifiedGarbage.Proof.Ed25519.X86_64.CombSelect
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.Double4

/-! ### `Ed25519.X86_64.Zmm.Loop`, which only this module used -/

section

/-! ### `Ed25519.X86_64.Zmm.Step`, which only this module used -/

section

/-!
# The `zmm` comb: an addition in each half

After the selection, `zentry_ok`: each half's rows are split into the limbs
of `ymm5–ymm9` (`esplit`, translated), the masks of the signs set
(`zsign`), and the entry, negated for a negative digit, added to the half's
point (`vnegBody`, the carry and `vadd`, translated): what `ventryN_wp` says
of each half.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Zmm

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Zmm VG.Proof.Ed25519.X86_64.Ifma
  VG.Proof.Ed25519.X86_64
open VG.Impl.X25519.X86_64.Ifma (KM carry)
open VG.Impl.Ed25519.X86_64.Ifma (esplit vnegBody vadd)
open VG.Proof.X25519.X86_64.Ifma (lanes fe5 fe5_congr mq limbNat envOf Ctx)
open VG.Proof.X25519.X86_64 (off ofs Outside)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw)

/-! ## The entry -/

/-- The words of `selWord`, as a field element: the entry's field. -/
theorem selWord_fe (j m c : Nat) (hm : m ≤ 16) (hc : c < 3) :
    VG.Proof.X25519.toFe ((selWord j m c 0).toNat + 2 ^ 64 * (selWord j m c 1).toNat +
      2 ^ 128 * (selWord j m c 2).toNat + 2 ^ 192 * (selWord j m c 3).toNat) = combField j m c := by
  by_cases h1 : 1 ≤ m
  · simp only [selWord, h1, ite_true]
    exact val4_feWord _
  · obtain rfl : m = 0 := by omega_using [h1]
    rcases (by omega_using [hc] : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> rfl

/-- The limbs of rows `0–3` of the entry, as field elements. -/
theorem entry_fe {w : Nat → Nat → Nat} (hw : ∀ l k, w l k < 2 ^ 64) (l : Nat) :
    fe5 (limbNat (w l) (2 ^ 51 - 1)) =
      VG.Proof.X25519.toFe (w l 0 + 2 ^ 64 * w l 1 + 2 ^ 128 * w l 2 + 2 ^ 192 * w l 3) := by
  show VG.Proof.X25519.toFe _ = _
  rw [VG.Proof.X25519.X86_64.Ifma.limbNat_lv _ (fun k _ => hw l k)]

/-- The cached entry the selection leaves for the magnitude `m` of table `j`. -/
def selEntry (j m : Nat) : Spec.Ed25519.Point := ⟨combField j m 0, combField j m 1, combField j m 2, 2⟩


/-! ## The blocks -/

theorem half_scratch {z : State} {b : Addr} (hs : Scratch z b) (h : Nat) : Scratch (Zmm.half b h z) b :=
  ⟨hs.rdi, hs.wr, hs.nowrap⟩

/-- `esplit` on both halves: each half's rows split into the limbs of `ymm5–ymm9`. -/
theorem zsplit_ok {z : State} {b : Addr} (hs : Scratch z b) (hz : ZOK b z)
    (hk : ∀ h < 2, EConsts (Zmm.half b h z).mem b) :
    WP isa (.block (tzs 15 esplit)) z fun t => ZOK b t ∧ ZKeep b z t ∧
      (∀ h < 2, ∀ l < 4, ∀ i < 5, lanes (Zmm.half b h t) 5 l i =
          limbNat (srow (envOf (Zmm.half b h z)) l) (2 ^ 51 - 1) i ∧ lanes (Zmm.half b h t) 5 l i < 2 ^ 52) ∧
      (∀ h < 2, ∀ r < 5, ∀ l < 4, qw (Zmm.half b h t) (xr r) l = qw (Zmm.half b h z) (xr r) l) ∧
      (∀ h < 2, EConsts (Zmm.half b h t).mem b) := by
  refine WP.mono (sim_wp (t := 15) (J' := []) (by decide +kernel) hz fun h hh =>
    esplit_wp (half_scratch hs h).rdi (ctx_of (half_scratch hs h)) (hk h hh).toCConsts)
    fun t ⟨o, k, r⟩ => ⟨o, k, fun h hh l hl i hi => ?_, fun h hh q hq l hl => ?_, fun h hh => ?_⟩
  · obtain ⟨y, hr, _, _, u, _⟩ := r h hh
    rw [← hr.lanes_eq (r := 5) (by decide) (fun _ _ _ => List.not_mem_nil) l hl i hi]
    exact u l hl i hi
  · obtain ⟨y, hr, _, _, _, kk⟩ := r h hh
    rw [← hr.qw_eq List.not_mem_nil hl]
    exact kk q hq l hl
  · obtain ⟨y, hr, _, m, _, _⟩ := r h hh
    exact hr.econsts (by rw [m]; exact hk h hh)

/-- The negation, the carry and the addition on both halves. -/
theorem zadd_ok {z : State} {b : Addr} (hs : Scratch z b) (hz : ZOK b z)
    (hk : ∀ h < 2, EConsts (Zmm.half b h z).mem b) (hsm : ∀ h < 2, Small (Zmm.half b h z))
    {bs : Nat → Bool} (hm : ∀ h < 2, ∀ k < 4, qw (Zmm.half b h z) (xr 15) k = VG.Proof.X25519.X86_64.mask (bs h))
    (hy : ∀ h < 2, ∀ l < 4, ∀ i < 5, lanes (Zmm.half b h z) 5 l i < 2 ^ 52) :
    WP isa (.block (tzs 12 vnegBody ++ tzs 15 (carry (5 + ·) ++ vadd))) z fun t => ZOK b t ∧ ZKeep b z t ∧
      (∀ h < 2, lanePt (Zmm.half b h t) =
        vAddPt (lanePt (Zmm.half b h z)) (negIf (bs h) (lanePt5 (Zmm.half b h z)))) ∧
      (∀ h < 2, Small (Zmm.half b h t)) ∧ (∀ h < 2, EConsts (Zmm.half b h t).mem b) := by
  obtain hj : ∀ q < 5, q ∉ [15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15] := by decide
  refine WP.mono (sim_wp2 (t₁ := 12) (t₂ := 15) (J₁ := [12, 12, 12, 12, 12])
    (J₂ := [15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15]) (by decide +kernel) (by decide +kernel) hz
    (Q := fun h s' => s'.gpr = (Zmm.half b h z).gpr ∧ s'.rd = (Zmm.half b h z).rd ∧
      s'.wr = (Zmm.half b h z).wr ∧ Outside b 1024 320 (Zmm.half b h z).mem s'.mem ∧ Small s' ∧
      lanePt s' = vAddPt (lanePt (Zmm.half b h z)) (negIf (bs h) (lanePt5 (Zmm.half b h z))))
    fun h hh => by
      rw [← List.append_assoc]
      exact ventryN_wp (half_scratch hs h).rdi (ctx_of (half_scratch hs h)) (hk h hh) (hsm h hh) (hm h hh)
        (hy h hh)) fun t ⟨o, k, r⟩ => ⟨o, k, fun h hh => ?_, fun h hh => ?_, fun h hh => ?_⟩
  · obtain ⟨y, hr, _, _, _, _, _, p⟩ := r h hh
    rw [← hr.lanePt_eq hj, p]
  · obtain ⟨y, hr, _, _, _, _, sm, _⟩ := r h hh
    exact hr.small hj sm
  · obtain ⟨y, hr, _, _, _, ho, _, _⟩ := r h hh
    exact half_econsts hr (hk h hh) ho

/-- A quadword below the rows of the window, kept by what keeps the memory but those rows. -/
theorem readW_keep {m m' : Mem} {b : Addr} (k : ∀ a, ¬ InZ (a - b).toNat → m' a = m a) {d : Nat}
    (hd : d + 8 ≤ ZB ∨ (ZMASK ≤ d ∧ d + 8 ≤ 8192)) : m'.readW (off b d) 64 = m.readW (off b d) 64 :=
  Mem.readW_congr fun i hi => k _ (by
    simp only [off, Offset.add_ofNat_add_ofNat]
    rw [off_ofNat _ (by unfold ZB ZMASK at hd; omega_using [hd, hi])]; unfold InZ; omega_using [hd, hi])

theorem zq_lanes {z t : State} (k : ∀ r, r ≠ xr 14 → r ≠ xr 15 → ∀ i < 4, t.zlane r i = z.zlane r i)
    (b : Addr) {h : Nat} (hh : h < 2) {r : Nat} (hr : r + 5 ≤ 14) :
    ∀ l < 4, ∀ i < 5, lanes (Zmm.half b h t) r l i = lanes (Zmm.half b h z) r l i := fun l hl i hi => by
  simp only [lanes]
  rw [qw_half b t _ hl, qw_half b z _ hl]
  simp only [zq]
  obtain hne : ∀ q < 14, xr q ≠ xr 14 ∧ xr q ≠ xr 15 := by decide
  rw [k _ (hne (r + i) (by omega_using [hr, hi])).1 (hne (r + i) (by omega_using [hr, hi])).2 _ (by omega_using [hh, hl])]

/-- After the selection: each half's entry, negated for a negative digit, added to its point. -/
theorem zentry_ok {z : State} {b : Addr} (hs : Scratch z b) (hz : ZOK b z)
    (hk : ∀ h < 2, EConsts (Zmm.half b h z).mem b) (hsm : ∀ h < 2, Small (Zmm.half b h z)) {j : Nat}
    {m n : Nat → Nat} (hm : ∀ h < 2, m h ≤ 16)
    (hsel : ∀ h < 2, ∀ c < 3, ∀ k < 4, zq z (xr (11 + c)) h k = selWord j (m h) c k)
    (h14 : ∀ h < 2, VG.Proof.X25519.toFe ((zq z (xr 14) h 0).toNat + 2 ^ 64 * (zq z (xr 14) h 1).toNat +
      2 ^ 128 * (zq z (xr 14) h 2).toNat + 2 ^ 192 * (zq z (xr 14) h 3).toNat) = 2)
    (hSA : z.mem.readW (off b SGA) 64 = signMask (n 0)) (hSB : z.mem.readW (off b SGB) 64 = signMask (n 1)) :
    WP isa (.block (tzs 15 esplit ++ zsign ++ (tzs 12 vnegBody ++ tzs 15 (carry (5 + ·) ++ vadd)))) z fun t =>
      ZOK b t ∧ (∀ r, r ≠ .rcx → t.gpr r = z.gpr r) ∧ t.rd = z.rd ∧ t.wr = z.wr ∧
      (∀ a, ¬ InZ (a - b).toNat → t.mem a = z.mem a) ∧
      (∀ h < 2, lanePt (Zmm.half b h t) =
        vAddPt (lanePt (Zmm.half b h z)) (negIf (decide (n h < 16)) (selEntry j (m h)))) ∧
      (∀ h < 2, Small (Zmm.half b h t)) ∧ (∀ h < 2, EConsts (Zmm.half b h t).mem b) := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zsplit_ok hs hz hk) fun z₁ ⟨o₁, k₁, u₁, q₁, e₁⟩ => ?_
  obtain hs₁ : Scratch z₁ b := ⟨by rw [vm_gpr' k₁.vm]; exact hs.rdi, by rw [vm_wr' k₁.vm]; exact hs.wr, hs.nowrap⟩
  refine WP.mono (zsign_ok hs₁ (mA := signMask (n 0)) (mB := signMask (n 1)) (by rw [readW_keep k₁.mem (Or.inr (by unfold SGA ZMASK; omega_using []))]; exact hSA)
    (by rw [readW_keep k₁.mem (Or.inr (by unfold SGB ZMASK; omega_using []))]; exact hSB)) fun z₂ ⟨q₂, k₂⟩ => ?_
  obtain hs₂ : Scratch z₂ b := ⟨by rw [k₂.gpr _ (by decide)]; exact hs₁.rdi, by rw [k₂.wr]; exact hs₁.wr, hs.nowrap⟩
  obtain zl₂ : ∀ r, r ≠ xr 14 → r ≠ xr 15 → ∀ i < 4, z₂.zlane r i = z₁.zlane r i :=
    fun r h1 h2 => k₂.zl r (fun h => h.elim h1 h2)
  obtain m₂ : ∀ h, (Zmm.half b h z₂).mem = (Zmm.half b h z₁).mem := fun h => by
    show hmem b h z₂.mem = hmem b h z₁.mem; rw [k₂.mem]
  obtain l0 : ∀ h < 2, ∀ l < 4, ∀ i < 5, lanes (Zmm.half b h z₂) 0 l i = lanes (Zmm.half b h z) 0 l i :=
    fun h hh l hl i hi => by
      rw [zq_lanes zl₂ b hh (by decide) l hl i hi]
      simp only [lanes, Nat.zero_add]; rw [q₁ h hh i hi l hl]
  obtain l5 : ∀ h < 2, ∀ l < 4, ∀ i < 5, lanes (Zmm.half b h z₂) 5 l i = lanes (Zmm.half b h z₁) 5 l i :=
    fun h hh => zq_lanes zl₂ b hh (by decide)
  obtain o₂ : ZOK b z₂ := ⟨hs₂.rdi, hs₂.wr, hs.nowrap, by rw [k₂.mem]; exact o₁.masks⟩
  refine WP.mono (zadd_ok (bs := fun h => decide (n h < 16)) hs₂ o₂
    (fun h hh => by rw [m₂ h]; exact e₁ h hh)
    (fun h hh l hl i hi => by rw [l0 h hh l hl i hi]; exact hsm h hh l hl i hi)
    (fun h hh k hk => by
      rw [qw_half b z₂ _ hk, q₂ h hh k hk, ← signMask_eq]
      rcases (by omega_using [hh] : h = 0 ∨ h = 1) with rfl | rfl <;> rfl)
    (fun h hh l hl i hi => by rw [l5 h hh l hl i hi]; exact (u₁ h hh l hl i hi).2))
    fun t ⟨o₃, k₃, p₃, sm₃, e₃⟩ => ?_
  obtain row : ∀ h < 2, ∀ l < 4, fe5 (lanes (Zmm.half b h z₂) 5 l) =
      [combField j (m h) 0, combField j (m h) 1, combField j (m h) 2, 2].getD l 0 := fun h hh l hl => by
    rw [fe5_congr fun i hi => (l5 h hh l hl i hi).trans (u₁ h hh l hl i hi).1,
      entry_fe (w := srow (envOf (Zmm.half b h z))) (fun _ _ => BitVec.isLt _) l]
    obtain e : ∀ k < 4, srow (envOf (Zmm.half b h z)) l k = (zq z (xr (11 + l)) h k).toNat := fun k hk => by
      show (qw (Zmm.half b h z) (xr (11 + l)) k).toNat = _
      rw [qw_half b z _ hk]
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
    rcases (by omega_using [hl] : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
    · rw [hsel h hh 0 (by decide) 0 (by decide), hsel h hh 0 (by decide) 1 (by decide),
        hsel h hh 0 (by decide) 2 (by decide), hsel h hh 0 (by decide) 3 (by decide),
        selWord_fe _ _ _ (hm h hh) (by decide)]
      rfl
    · rw [hsel h hh 1 (by decide) 0 (by decide), hsel h hh 1 (by decide) 1 (by decide),
        hsel h hh 1 (by decide) 2 (by decide), hsel h hh 1 (by decide) 3 (by decide),
        selWord_fe _ _ _ (hm h hh) (by decide)]
      rfl
    · rw [hsel h hh 2 (by decide) 0 (by decide), hsel h hh 2 (by decide) 1 (by decide),
        hsel h hh 2 (by decide) 2 (by decide), hsel h hh 2 (by decide) 3 (by decide),
        selWord_fe _ _ _ (hm h hh) (by decide)]
      rfl
    · exact h14 h hh
  obtain p₂ : ∀ h < 2, lanePt (Zmm.half b h z₂) = lanePt (Zmm.half b h z) := fun h hh => by
    simp only [lanePt]
    rw [fe5_congr (l0 h hh 0 (by decide)), fe5_congr (l0 h hh 1 (by decide)), fe5_congr (l0 h hh 2 (by decide)),
      fe5_congr (l0 h hh 3 (by decide))]
  obtain p5 : ∀ h < 2, lanePt5 (Zmm.half b h z₂) = selEntry j (m h) := fun h hh => by
    simp only [lanePt5, selEntry]
    rw [row h hh 0 (by decide), row h hh 1 (by decide), row h hh 2 (by decide), row h hh 3 (by decide)]
    rfl
  refine ⟨o₃, fun r hr => ?_, ?_, ?_, fun a ha => ?_, fun h hh => ?_, sm₃, e₃⟩
  · rw [vm_gpr' k₃.vm, k₂.gpr r (by simp [hr]), vm_gpr' k₁.vm]
  · rw [vm_rd' k₃.vm, k₂.rd, vm_rd' k₁.vm]
  · rw [vm_wr' k₃.vm, k₂.wr, vm_wr' k₁.vm]
  · rw [k₃.mem a ha, k₂.mem, k₁.mem a ha]
  · rw [p₃ h hh, p₂ h hh, p5 h hh]

end VG.Proof.Ed25519.X86_64.Zmm

end

end


/-!
# The `zmm` comb: a step of the loop

Step `j` adds the entry of table `j` for the odd digit `d_{2j+1}` to half 0
(`A`) and for the even digit `d_{2j}` to half 1 (`B`): after the 26 steps,
`A = [G + Σ d_{2j+1} 1024^j]B` and `B = [G + Σ d_{2j} 1024^j]B`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Zmm

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Zmm VG.Proof.Ed25519.X86_64.Ifma
  VG.Proof.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Impl.X25519.X86_64.Ifma (KM carry)
open VG.Impl.Ed25519.X86_64.Ifma (esplit vnegBody vadd)
open VG.Proof.X25519.X86_64.Ifma (lanes fe5 fe5_congr mq)
open VG.Proof.X25519.X86_64 (off ofs Outside Keeps clob)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw)

/-! ## The sum -/

/-- An entry of the selection, negated for a negative digit, added to a point. -/
theorem entry_rep {P : Spec.Ed25519.Point} {v : ℤ} (hP : Rep P (v • baseAff)) (S i : Nat) {j : Nat}
    (hj : j < 26) :
    Rep (vAddPt P (negIf (decide (nib S i < 16)) (selEntry j (mag (nib S i)))))
      ((sdig S i * 1024 ^ j + v) • baseAff) := by
  obtain hmag : mag (nib S i) < 17 := by unfold mag nib; split <;> omega_arith
  obtain ⟨q₀, hq₀, hrq₀⟩ := combCached_ok j (mag (nib S i)) hj hmag
  obtain hcc : selEntry j (mag (nib S i)) = cache q₀ := by
    rw [← hq₀, selEntry, ← combCached_T j (mag (nib S i))]; rfl
  let q := if nib S i < 16 then negPoint q₀ else q₀
  obtain hneg : negIf (decide (nib S i < 16)) (cache q₀) = cache q := by
    by_cases hlt : nib S i < 16
    · simp only [hlt, decide_true, negIf, ↓reduceIte, q]
      exact VG.Proof.Ed25519.X86_64.negCached_cache q₀
    · simp only [hlt, decide_false, negIf, Bool.false_eq_true, ↓reduceIte, q]
  obtain hrq : Rep q ((sdig S i * 1024 ^ j) • baseAff) := by
    by_cases hlt : nib S i < 16
    · simp only [hlt, ↓reduceIte, q]
      obtain e : sdig S i * 1024 ^ j = -(((mag (nib S i) * 1024 ^ j : Nat) : ℤ)) := by
        simp only [sdig, mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega_arith : nib S i ≤ 16)]; ring
      rw [e, neg_smul, natCast_zsmul]
      exact hrq₀.neg
    · simp only [hlt, ↓reduceIte, q]
      obtain e : sdig S i * 1024 ^ j = (((mag (nib S i) * 1024 ^ j : Nat) : ℤ)) := by
        simp only [sdig, mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega_arith : 16 ≤ nib S i)]; ring
      rw [e, natCast_zsmul]
      exact hrq₀
  rw [hcc, hneg, vAddPt_cache, add_smul, add_comm]
  exact pointAdd_rep hP hrq


/-! ## The invariant -/

/-- The offsets the loop writes: the rows of the window, the sign's mask, `SGA` and `SGB`. -/
def ZChg (q : Nat) : Prop := InZ q ∨ DigOff q

/-- What the loop needs of the state `s₀` it starts from. -/
structure ZLoopPre (s₀ : State) (b T : Addr) (S : Nat) : Prop where
  scratch : Scratch s₀ b
  zok : ZOK b s₀
  hconsts : ∀ h < 2, EConsts (Zmm.half b h s₀).mem b
  consts : EConsts s₀.mem b
  k2 : ∀ h < 2, VG.Proof.X25519.X86_64.F s₀.mem b (ZK2 + 32 * h) = 2
  bits : ∀ q < 256, s₀.mem (off b (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)
  tbl : CombTbl s₀ T
  far : TblFar b T

/-- What the loop keeps of `s₀`: the registers but `rbx`, `rsi` and `clob` (`r11` kept), the
regions, the statics, and the memory but at `ZChg`. -/
structure ZFrame (s₀ : State) (b : Addr) (s : State) : Prop where
  gpr : ∀ r, r ≠ .rbx → r ≠ .rsi → r ∉ clob → s.gpr r = s₀.gpr r
  r11 : s.gpr .r11 = s₀.gpr .r11
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : ∀ a, ¬ ZChg (ofs b a) → s.mem a = s₀.mem a
  syms : s.syms = s₀.syms

theorem ZFrame.scratch {s₀ s : State} {b T : Addr} {S : Nat} (hp : ZLoopPre s₀ b T S) (h : ZFrame s₀ b s)
    (hr : s.gpr .rdi = b) : Scratch s b :=
  ⟨hr, by rw [h.wr]; exact hp.scratch.wr, hp.scratch.nowrap⟩

theorem ZFrame.byte {s₀ s : State} {b : Addr} (h : ZFrame s₀ b s) {d : Nat}
    (hd : ¬ ZChg d) (hd' : d < 2 ^ 64) : s.mem (b + BitVec.ofNat 64 d) = s₀.mem (b + BitVec.ofNat 64 d) :=
  h.mem _ (by simp only [ofs]; rw [off_ofNat _ hd']; exact hd)

theorem ZFrame.readW {s₀ s : State} {b : Addr} (h : ZFrame s₀ b s) {d w : Nat}
    (hd : ∀ i < w / 8, ¬ ZChg (d + i)) (hd' : d + w / 8 < 2 ^ 64) :
    s.mem.readW (b + BitVec.ofNat 64 d) w = s₀.mem.readW (b + BitVec.ofNat 64 d) w :=
  Mem.readW_congr fun i hi => by
    rw [Offset.add_ofNat_add_ofNat]; exact h.byte (hd i hi) (by omega_arith)

theorem ZFrame.zok {s₀ s : State} {b T : Addr} {S : Nat} (hp : ZLoopPre s₀ b T S) (h : ZFrame s₀ b s)
    (hr : s.gpr .rdi = b) : ZOK b s :=
  ⟨hr, by rw [h.wr]; exact hp.scratch.wr, hp.scratch.nowrap, fun sel hs i hi => by
    obtain hm : ∀ sel ∈ blendSels, ZMASK ≤ maskRow sel ∧ maskRow sel + 64 ≤ 6016 := by decide
    have := hm sel hs
    rw [h.readW (fun q hq => by unfold ZChg InZ DigOff SGA SGB combSignMask ZMASK at *; omega_arith) (by omega_arith)]
    exact hp.zok.masks sel hs i hi⟩

theorem ZFrame.k2 {s₀ s : State} {b : Addr} (h : ZFrame s₀ b s) :
    ∀ h' < 2, ∀ k < 4, s.mem.readW (b + BitVec.ofNat 64 (ZK2 + 32 * h' + 8 * k)) 64 =
      s₀.mem.readW (b + BitVec.ofNat 64 (ZK2 + 32 * h' + 8 * k)) 64 :=
  fun h' hh k hk => h.readW (fun q hq => by unfold ZChg InZ DigOff SGA SGB combSignMask ZMASK ZK2 ZB at *; omega_arith)
    (by unfold ZK2; omega_arith)

theorem ZFrame.bits {s₀ s : State} {b T : Addr} {S : Nat} (hp : ZLoopPre s₀ b T S) (h : ZFrame s₀ b s) :
    ∀ q < 256, s.mem (off b (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) := fun q hq => by
  rw [h.mem _ (by rw [bits_far hq]; unfold ZChg InZ DigOff SGA SGB combSignMask ZMASK ZB; omega_arith)]
  exact hp.bits q hq

theorem ZFrame.keep {s₀ s : State} {b : Addr} (h : ZFrame s₀ b s) : PowersKeep b 56 7368 s₀ s :=
  ⟨fun r h1 h2 h3 => h.gpr r h1 h2 h3, h.rd, h.wr, fun p _ hp => h.mem p (by
    unfold ZChg InZ DigOff SGA SGB combSignMask ZMASK ZB; omega_arith)⟩

theorem ZFrame.tbl {s₀ s : State} {b T : Addr} {S : Nat} (hp : ZLoopPre s₀ b T S) (h : ZFrame s₀ b s) :
    CombTbl s T :=
  hp.tbl.keep hp.far h.keep h.syms

theorem ZFrame.consts {s₀ s : State} {b T : Addr} {S : Nat} (hp : ZLoopPre s₀ b T S) (h : ZFrame s₀ b s) :
    EConsts s.mem b :=
  hp.consts.of_mq fun d h1 h2 => h.readW (fun q hq => by
    unfold ZChg InZ DigOff SGA SGB combSignMask ZMASK ZB; omega_arith) (by omega_arith)

/-- The loop's invariant after `j` steps, with the points `[vA]B` and `[vB]B` in the halves. -/
structure ZInv (s₀ : State) (b : Addr) (j : Nat) (vA vB : ℤ) (s : State) : Prop where
  bound : j ≤ 26
  rdi : s.gpr .rdi = b
  counter : s.gpr .rbx = BitVec.ofNat 64 j
  frame : ZFrame s₀ b s
  hconsts : ∀ h < 2, EConsts (Zmm.half b h s).mem b
  small : ∀ h < 2, Small (Zmm.half b h s)
  valA : Rep (lanePt (Zmm.half b 0 s)) (vA • baseAff)
  valB : Rep (lanePt (Zmm.half b 1 s)) (vB • baseAff)

/-! ## Small blocks -/

theorem movRdx_ok (s : State) {j : Nat} (h9 : s.gpr .r9 = BitVec.ofNat 64 j) :
    WP isa (.block [.mov .rdx (.reg .r9)]) s fun t => t.gpr .rdx = BitVec.ofNat 64 j ∧ Keeps [.rdx] s t ∧
      (∀ r i, t.zlane r i = s.zlane r i) ∧ t.syms = s.syms := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg, h9, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, fun _ _ => rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem rbxNext26_ok (s : State) (n : Nat) (hn : n < 26) (hc : s.gpr .rbx = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 26)]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (n + 1) ∧ t.zf = some (decide (n + 1 = 26)) ∧ Keeps [.rbx] s t ∧
      (∀ r i, t.zlane r i = s.zlane r i) ∧ t.syms = s.syms := by
  obtain ha : BitVec.ofNat 64 n + (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (n + 1) := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
  obtain hz : (BitVec.ofNat 64 (n + 1) - (26 : BitVec 32).signExtend 64 == 0) = decide (n + 1 = 26) := by
    rw [show (26 : BitVec 32).signExtend 64 = BitVec.ofNat 64 26 from rfl]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hn]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    hc, ha, hz, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, fun _ _ => rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem tzs_append (t : Nat) (a c : List Instr) : tzs t (a ++ c) = tzs t a ++ tzs t c :=
  List.flatMap_append

/-- The window's constants, as half `h` sees them, kept by what writes only at `DigOff`. -/
theorem hconsts_dig {m m' : Mem} {b : Addr} (hk : MemOff b DigOff m m') {h : Nat} (hh : h < 2)
    (hc : EConsts (hmem b h m) b) : EConsts (hmem b h m') b :=
  hc.of_mq fun d h1 h2 => Mem.readW_congr fun i hi => by
    simp only [hmem]
    rw [Offset.add_ofNat_add_ofNat, off_ofNat _ (by omega_arith)]
    split
    · rename_i hw
      unfold InWin at hw
      refine hk _ ?_
      simp only [ofs]
      rw [off_ofNat _ (by unfold zoff ZB; omega_arith)]
      unfold DigOff zoff ZB SGA SGB combSignMask
      omega_arith
    · refine hk _ ?_
      simp only [ofs]
      rw [off_ofNat _ (by omega_arith)]
      unfold DigOff SGA SGB combSignMask
      omega_arith

/-! ## A step -/

theorem combStep_block : ([.mov .rdx (.reg .r9)] : List Instr) ++ zselect ++ tzs 15 esplit ++ zsign ++
    tzs 12 vnegBody ++ tzs 15 (carry (5 + ·)) ++ tzs 15 vadd ++
    ([.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 26)] : List Instr) =
    ([.mov .rdx (.reg .r9)] : List Instr) ++ (zselect ++ ((tzs 15 esplit ++ zsign ++
      (tzs 12 vnegBody ++ tzs 15 (carry (5 + ·) ++ vadd))) ++
      ([.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 26)] : List Instr))) := by
  simp only [tzs_append, List.append_assoc]

/-- A step of the loop: the entries of table `j` for the digits `d_{2j+1}` and `d_{2j}` added
to the halves. -/
theorem zstep_ok {s₀ z : State} {b T : Addr} {S j : Nat} {vA vB : ℤ} (hp : ZLoopPre s₀ b T S)
    (hS : S < 2 ^ 256) (h : ZInv s₀ b j vA vB z) (hj : j < 26) :
    WP isa combStep z fun t => t.zf = some (decide (j + 1 = 26)) ∧
      ZInv s₀ b (j + 1) (sdig S (2 * j + 1) * 1024 ^ j + vA) (sdig S (2 * j) * 1024 ^ j + vB) t := by
  obtain hsz := h.frame.scratch hp h.rdi
  rw [Zmm.combStep]
  refine WP.seq (WP.mono_syms (zscal zdigits_scal (zdigits_ok hsz hj hS h.counter (h.frame.bits hp)))
    fun z₁ ⟨⟨r8₁, r10₁, r9₁, rbx₁, sa₁, sb₁, g₁, rd₁, wr₁, m₁⟩, zl₁⟩ sy₁ => ?_)
  rw [combStep_block, WP.block_append_iff]
  obtain hs₁ : Scratch z₁ b :=
    ⟨by rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hsz.rdi,
      by rw [wr₁]; exact hsz.wr, hsz.nowrap⟩
  refine WP.mono (movRdx_ok z₁ r9₁) fun z₂ ⟨d₂, k₂, zl₂, sy₂⟩ => ?_
  obtain hs₂ : Scratch z₂ b := hs₁.of_keeps k₂ (by decide)
  obtain f₂ : ZFrame s₀ b z₂ := by
    refine ⟨fun r h1 h2 h3 => ?_, ?_, ?_, ?_, fun a ha => ?_, ?_⟩
    · rw [k₂.1 r (by intro e; simp at e; exact h3 (e ▸ by decide)), g₁ r (fun e => h3 (e ▸ by decide))
        (fun e => h3 (e ▸ by decide)) (fun e => h3 (e ▸ by decide)) (fun e => h3 (e ▸ by decide))
        (fun e => h3 (e ▸ by decide)) (fun e => h3 (e ▸ by decide))]
      exact h.frame.gpr r h1 h2 h3
    · rw [k₂.1 _ (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h.frame.r11
    · rw [k₂.2.2.1, rd₁]; exact h.frame.rd
    · rw [k₂.2.2.2, wr₁]; exact h.frame.wr
    · rw [k₂.2.1, m₁ a (fun e => ha (Or.inr e))]; exact h.frame.mem a ha
    · rw [sy₂, sy₁]; exact h.frame.syms
  obtain hmA : mag (nib S (2 * j + 1)) ≤ 16 := by unfold mag nib; split <;> omega_arith
  obtain hmB : mag (nib S (2 * j)) ≤ 16 := by unfold mag nib; split <;> omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (zselect_ok hs₂ (f₂.tbl hp) hj hmA hmB d₂ (by rw [k₂.1 _ (by decide)]; exact r8₁)
    (by rw [k₂.1 _ (by decide)]; exact r10₁)) fun z₃ ⟨sel₃, k14₃, k₃⟩ => ?_
  obtain hs₃ : Scratch z₃ b := ⟨by rw [k₃.gpr _ (by decide)]; exact hs₂.rdi, by rw [k₃.wr]; exact hs₂.wr, hsz.nowrap⟩
  obtain mem₃ : z₃.mem = z₁.mem := by rw [k₃.mem, k₂.2.1]
  -- the halves' points and constants, kept since `z`
  obtain zl : ∀ r, ¬ (zselRegs r ∨ r = xr 9) → ∀ i < 4, z₃.zlane r i = z.zlane r i := fun r hr i hi => by
    rw [k₃.zl r hr i hi, zl₂, zl₁]
  obtain hreg : ∀ q < 9, ¬ (zselRegs (xr q) ∨ xr q = xr 9) := by decide
  obtain l0 : ∀ h' < 2, ∀ l < 4, ∀ i < 5, lanes (Zmm.half b h' z₃) 0 l i = lanes (Zmm.half b h' z) 0 l i :=
    fun h' hh l hl i hi => by
      simp only [lanes, Nat.zero_add]
      rw [qw_half b z₃ _ hl, qw_half b z _ hl]
      simp only [zq]
      rw [zl _ (hreg i (by omega_arith)) _ (by omega_arith)]
  obtain p₃ : ∀ h' < 2, lanePt (Zmm.half b h' z₃) = lanePt (Zmm.half b h' z) := fun h' hh => by
    simp only [lanePt]
    rw [fe5_congr (l0 h' hh 0 (by decide)), fe5_congr (l0 h' hh 1 (by decide)),
      fe5_congr (l0 h' hh 2 (by decide)), fe5_congr (l0 h' hh 3 (by decide))]
  obtain sm₃ : ∀ h' < 2, Small (Zmm.half b h' z₃) := fun h' hh l hl i hi => by
    rw [l0 h' hh l hl i hi]; exact h.small h' hh l hl i hi
  obtain hk₃ : ∀ h' < 2, EConsts (Zmm.half b h' z₃).mem b := fun h' hh => by
    show EConsts (hmem b h' z₃.mem) b
    rw [mem₃]
    exact hconsts_dig m₁ hh (h.hconsts h' hh)
  rw [WP.block_append_iff]
  refine WP.mono_syms (zentry_ok (m := hmag (mag (nib S (2 * j + 1))) (mag (nib S (2 * j))))
    (n := hmag (nib S (2 * j + 1)) (nib S (2 * j))) hs₃
    ⟨hs₃.rdi, hs₃.wr, hsz.nowrap, by rw [k₃.mem]; exact (f₂.zok hp hs₂.rdi).masks⟩
    hk₃ sm₃ (fun h' hh => by simp only [hmag]; split <;> omega_arith) sel₃
    (fun h' hh => by
      rw [k14₃ h' hh 0 (by decide), k14₃ h' hh 1 (by decide), k14₃ h' hh 2 (by decide), k14₃ h' hh 3 (by decide),
        f₂.k2 h' hh 0 (by decide), f₂.k2 h' hh 1 (by decide), f₂.k2 h' hh 2 (by decide),
        f₂.k2 h' hh 3 (by decide), ← hp.k2 h' hh]
      rfl)
    (by rw [mem₃]; exact sa₁) (by rw [mem₃]; exact sb₁)) fun z₄ ⟨o₄, g₄, rd₄, wr₄, m₄, p₄, sm₄, e₄⟩ sy₄ => ?_
  obtain rbx₄ : z₄.gpr .rbx = BitVec.ofNat 64 j := by
    rw [g₄ _ (by decide), k₃.gpr _ (by decide), k₂.1 _ (by decide)]; exact rbx₁
  refine WP.mono (rbxNext26_ok z₄ j hj rbx₄) fun t ⟨rb, zf, kt, zlt, syt⟩ => ⟨zf, ?_⟩
  obtain lt : ∀ h' < 2, ∀ r l i, l < 4 → lanes (Zmm.half b h' t) r l i = lanes (Zmm.half b h' z₄) r l i :=
    fun h' hh r l i hl => by
      simp only [lanes]; rw [qw_half b t _ hl, qw_half b z₄ _ hl]; simp only [zq]; rw [zlt]
  obtain pt : ∀ h' < 2, lanePt (Zmm.half b h' t) = lanePt (Zmm.half b h' z₄) := fun h' hh => by
    simp only [lanePt]
    rw [fe5_congr fun i _ => lt h' hh 0 0 i (by decide), fe5_congr fun i _ => lt h' hh 0 1 i (by decide),
      fe5_congr fun i _ => lt h' hh 0 2 i (by decide), fe5_congr fun i _ => lt h' hh 0 3 i (by decide)]
  obtain gz : ∀ r, r ≠ .rbx → r ≠ .rax → r ≠ .rcx → r ≠ .rdx → t.gpr r = z₂.gpr r := fun r h0 h1 h2 h3 => by
    rw [kt.1 r (by simp [h0]), g₄ r h2, k₃.gpr r (by simp [h1, h2, h3])]
  refine ⟨by omega_arith, by rw [gz _ (by decide) (by decide) (by decide) (by decide)]; exact hs₂.rdi, rb, ?_,
    fun h' hh => ?_, fun h' hh l hl i hi => ?_, ?_, ?_⟩
  · refine ⟨fun r h1 h2 h3 => ?_, ?_, ?_, ?_, fun a ha => ?_, ?_⟩
    · rw [gz r h1 (fun e => h3 (e ▸ by decide)) (fun e => h3 (e ▸ by decide)) (fun e => h3 (e ▸ by decide))]
      exact f₂.gpr r h1 h2 h3
    · rw [gz _ (by decide) (by decide) (by decide) (by decide)]; exact f₂.r11
    · rw [kt.2.2.1, rd₄, k₃.rd]; exact f₂.rd
    · rw [kt.2.2.2, wr₄, k₃.wr]; exact f₂.wr
    · rw [kt.2.1, m₄ a (fun e => ha (Or.inl e)), k₃.mem]; exact f₂.mem a ha
    · rw [syt, sy₄, k₃.syms]; exact f₂.syms
  · show EConsts (hmem b h' t.mem) b
    rw [kt.2.1]; exact e₄ h' hh
  · rw [lt h' hh 0 l i hl]; exact sm₄ h' hh l hl i hi
  · rw [pt 0 (by decide), p₄ 0 (by decide), p₃ 0 (by decide)]
    simp only [hmag, ite_true]
    exact entry_rep h.valA S (2 * j + 1) hj
  · rw [pt 1 (by decide), p₄ 1 (by decide), p₃ 1 (by decide)]
    simp only [hmag, show (1 : Nat) ≠ 0 by decide, ite_false]
    exact entry_rep h.valB S (2 * j) hj

end VG.Proof.Ed25519.X86_64.Zmm

end

end

/-! ### `Ed25519.X86_64.Zmm.Tail`, which only this module used -/

section

/-!
# The `zmm` comb: `32 A + B`

After the steps, `A` is doubled five times as the lanes of `ymm0–ymm4`
(`vdbl5`); `B`'s cached point `(Y - X, Y + X, 2dT, 2Z)` is its
`(Y - X, Y + X, T, Z)` (`vaddA`) times the lanes `(1, 1, 2d, 2)` of slots
12–15 (split as an entry, `esplit`), and is added to `32 A` (`vadd`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Zmm

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Zmm VG.Proof.Ed25519.X86_64.Ifma
  VG.Proof.Ed25519.X86_64 VG.Proof.Ed25519
open VG.Impl.X25519.X86_64 (sc)
open VG.Impl.X25519.X86_64.Ifma (y ld st mov carry mul4 OPL KM)
open VG.Impl.Ed25519.X86_64.Ifma (esplit vadd vaddA vstA vstore vdbl5)
open Edwards
open VG.Proof.X25519.X86_64.Ifma (lanes fe5 fe5_congr fe5_carry fe5_mul mq vm vm_gpr vm_rd vm_wr Ctx carryI_wp
  carryF_wp slotv envOf envOf_v limbNat Sym symOf symOf_eq run_ok CConsts)
open VG.Proof.X25519.X86_64 (off ofs Outside F)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw)

/-- The cached point of `(X, Y, Z, T)`, as `vcache` computes it: `(Y - X, Y + X, T (d + d), Z 2)`. -/
def cacheOf (P : Spec.Ed25519.Point) : Spec.Ed25519.Point :=
  ⟨(P.Y - P.X) * 1, (P.Y + P.X) * 1, P.T * (Spec.Ed25519.d + Spec.Ed25519.d), P.Z * 2⟩

theorem cacheOf_eq (P : Spec.Ed25519.Point) : cacheOf P = cache P := by
  simp only [cacheOf, cache, Spec.Ed25519.Point.mk.injEq]
  refine ⟨mul_one _, mul_one _, by grind, trivial⟩

theorem xr_ne' : ∀ a < 16, ∀ b < 16, a ≠ b → xr a ≠ xr b := by decide

theorem limbNat_congr' {w w' : Nat → Nat} {m : Nat} (h : ∀ k < 4, w k = w' k) (i : Nat) :
    limbNat w m i = limbNat w' m i := by
  rcases i with _ | _ | _ | _ | _ | _ <;>
    simp only [limbNat, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

/-- A field element's four words, split into limbs. -/
theorem fe5_words' (m : Mem) (base : Addr) (d : Nat) :
    fe5 (limbNat (fun k => (mq m base (d + 8 * k)).toNat) (2 ^ 51 - 1)) = F m base d := by
  show VG.Proof.X25519.toFe _ = VG.Proof.X25519.toFe _
  rw [VG.Proof.X25519.X86_64.Ifma.limbNat_lv _ (fun k _ => BitVec.isLt _)]
  rfl

/-- The rows of slots 12–15 into `ymm11–ymm14`. -/
def vrowsK : List Instr := [ld 11 (offset 12), ld 12 (offset 13), ld 13 (offset 14), ld 14 (offset 15)]

def vrowsKS : Sym := symOf vrowsK

theorem vrowsKS_regs : ∀ l < 4, vrowsKS.reg (11 + l) = .ld (64 + 32 * (12 + l)) := by decide +kernel
theorem vrowsKS_st : vrowsKS.st = [] := by decide +kernel

/-- The product's limbs to `ymm5–ymm9`. -/
def vmovs : List Instr := (List.range 5).map fun j => mov (5 + j) j

def vmovsS : Sym := symOf vmovs

theorem vmovsS_regs : ∀ j < 5, vmovsS.reg (5 + j) = .reg j := by decide +kernel
theorem vmovsS_st : vmovsS.st = [] := by decide +kernel

/-- `B`'s cached point from its lanes: `(Y - X, Y + X, T, Z)` (`vaddA`), carried, to `OPL`
(`vstA`), times the factors of slots 12–15 (`vrowsK`, `esplit`, `mul4 OPL`), to `ymm5–ymm9`,
carried. -/
theorem vcache_wp {s : State} {b : Addr} (hs : Scratch s b) (hk : EConsts s.mem b) (hx : Small s)
    (h12 : F s.mem b (offset 12) = 1) (h13 : F s.mem b (offset 13) = 1)
    (h14 : F s.mem b (offset 14) = Spec.Ed25519.d + Spec.Ed25519.d) (h15 : F s.mem b (offset 15) = 2) :
    WP isa (.block (vaddA ++ carry id ++ vstA ++ vrowsK ++ esplit ++ mul4 OPL ++ vmovs ++ carry (5 + ·))) s
      fun t => t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ Outside b 1024 320 s.mem t.mem ∧
        (∀ l < 4, ∀ i < 5, lanes t 5 l i < 2 ^ 52) ∧ lanePt5 t = cache (lanePt s) := by
  have hcc : CConsts s.mem b := hk.toCConsts
  simp only [List.append_assoc]
  -- `(Y - X, Y + X, T, Z)`
  rw [WP.block_append_iff]
  refine WP.mono (vaddA_wp hs.rdi (ctx_of hs) hcc hx) fun s₁ ⟨v₁, m₁, u₁, _⟩ => ?_
  obtain hs₁ : Scratch s₁ b := ⟨by rw [vm_gpr v₁]; exact hs.rdi, by rw [vm_wr v₁]; exact hs.wr, hs.nowrap⟩
  -- carried
  rw [WP.block_append_iff]
  refine WP.mono (carryI_wp hs₁.rdi (ctx_of hs₁) (by rw [m₁]; exact hcc) fun l hl i hi => (u₁ l hl i hi).2)
    fun s₂ ⟨v₂, m₂, u₂, _⟩ => ?_
  obtain hs₂ : Scratch s₂ b := ⟨by rw [vm_gpr v₂]; exact hs₁.rdi, by rw [vm_wr v₂]; exact hs₁.wr, hs.nowrap⟩
  obtain p₂ : ∀ l < 4, fe5 (lanes s₂ 0 l) = fe5 (aOp (lanes s 0) l) := fun l hl => by
    rw [fe5_congr (fun i hi => (u₂ l hl i hi).1),
      fe5_carry _ (by have := (u₁ l hl 4 (by decide)).2; omega_arith),
      fe5_congr (fun i hi => (u₁ l hl i hi).1)]
  -- to `OPL`
  rw [WP.block_append_iff]
  refine WP.mono (vstA_wp hs₂.rdi (ctx_of hs₂)) fun s₃ ⟨v₃, o₃, u₃, _⟩ => ?_
  obtain hs₃ : Scratch s₃ b := ⟨by rw [vm_gpr v₃]; exact hs₂.rdi, by rw [vm_wr v₃]; exact hs₂.wr, hs.nowrap⟩
  obtain mo₃ : Outside b 1024 320 s.mem s₃.mem := by
    rw [m₂, m₁] at o₃; exact o₃.mono (by decide) (by decide)
  obtain hk₃ : EConsts s₃.mem b := hk.outside mo₃
  -- the factors' rows
  rw [WP.block_append_iff]
  obtain e₄ : Sym.init.run vrowsK = some vrowsKS := symOf_eq _ _
  refine WP.mono (run_ok (ctx_of hs₃) e₄) fun s₄ h₄ => ?_
  obtain m₄ : s₄.mem = s₃.mem := by rw [h₄.mem, vrowsKS_st]; rfl
  obtain hs₄ : Scratch s₄ b := ⟨by rw [h₄.gpr]; exact hs₃.rdi, by rw [h₄.wr]; exact hs₃.wr, hs.nowrap⟩
  obtain r₄ : ∀ l < 4, ∀ k < 4, qw s₄ (xr (11 + l)) k = mq s₃.mem b (64 + 32 * (12 + l) + 8 * k) :=
    fun l hl k hk => by
      rw [h₄.reg _ k hk, VG.Proof.X25519.X86_64.Ifma.xi_xr _ (by omega_arith), vrowsKS_regs l hl]
      simp only [VG.Proof.X25519.X86_64.Ifma.T.eval, hs₃.rdi, mq]
  -- split
  rw [WP.block_append_iff]
  refine WP.mono (esplit_wp hs₄.rdi (ctx_of hs₄) (by rw [m₄]; exact hk₃.toCConsts))
    fun s₅ ⟨v₅, m₅, u₅, _⟩ => ?_
  obtain hs₅ : Scratch s₅ b := ⟨by rw [vm_gpr v₅]; exact hs₄.rdi, by rw [vm_wr v₅]; exact hs₄.wr, hs.nowrap⟩
  obtain f₅ : ∀ l < 4, fe5 (lanes s₅ 5 l) = F s.mem b (64 + 32 * (12 + l)) := fun l hl => by
    rw [fe5_congr (fun i hi => (u₅ l hl i hi).1), ← Outside_F mo₃ (by omega_arith) (Or.inl (by omega_arith)),
      ← fe5_words' s₃.mem b (64 + 32 * (12 + l))]
    exact fe5_congr fun i _ => limbNat_congr' (fun k hk => by
      simp only [srow, envOf_v]; rw [r₄ l hl k hk]) i
  -- the product
  rw [WP.block_append_iff]
  obtain sl₅ : ∀ l < 4, ∀ i < 5, slotv s₅.mem b OPL l i = lanes s₂ 0 l i := fun l hl i hi => by
    rw [m₅, m₄]; exact u₃ l hl i hi
  refine WP.mono (mulLB_wp hs₅.rdi (ctx_of hs₅) (fun l hl i hi => by rw [sl₅ l hl i hi]; exact (u₂ l hl i hi).2)
    (fun l hl i hi => (u₅ l hl i hi).2)) fun s₆ ⟨⟨v₆, m₆, u₆, _⟩, b₆⟩ => ?_
  obtain hs₆ : Scratch s₆ b := ⟨by rw [vm_gpr v₆]; exact hs₅.rdi, by rw [vm_wr v₆]; exact hs₅.wr, hs.nowrap⟩
  obtain p₆ : ∀ l < 4, fe5 (lanes s₆ 0 l) = fe5 (aOp (lanes s 0) l) * F s.mem b (64 + 32 * (12 + l)) :=
    fun l hl => by
      rw [fe5_congr (fun i hi => (u₆ l hl i hi).1),
        fe5_mul (fun i hi => by rw [sl₅ l hl i hi]; exact (u₂ l hl i hi).2) (fun i hi => (u₅ l hl i hi).2),
        fe5_congr (fun i hi => sl₅ l hl i hi), p₂ l hl, f₅ l hl]
  -- to `ymm5–ymm9`
  rw [WP.block_append_iff]
  obtain e₇ : Sym.init.run vmovs = some vmovsS := symOf_eq _ _
  refine WP.mono (run_ok (ctx_of hs₆) e₇) fun s₇ h₇ => ?_
  obtain hs₇ : Scratch s₇ b := ⟨by rw [h₇.gpr]; exact hs₆.rdi, by rw [h₇.wr]; exact hs₆.wr, hs.nowrap⟩
  obtain l₇ : ∀ l < 4, ∀ i < 5, lanes s₇ 5 l i = lanes s₆ 0 l i := fun l hl i hi => by
    simp only [lanes, Nat.zero_add]
    rw [h₇.reg _ l hl, VG.Proof.X25519.X86_64.Ifma.xi_xr _ (by omega_arith), vmovsS_regs i hi]; rfl
  obtain m₇ : s₇.mem = s₆.mem := by rw [h₇.mem, vmovsS_st]; rfl
  -- carried
  refine WP.mono (carryF_wp hs₇.rdi (ctx_of hs₇) (by rw [m₇, m₆, m₅, m₄]; exact hk₃.toCConsts)
    fun l hl i hi => by rw [l₇ l hl i hi]; have := b₆ l hl i hi; have : prodBound < 2 ^ 63 := by decide
                        omega_arith) fun t ⟨v₈, m₈, u₈, _⟩ => ?_
  refine ⟨by rw [vm_gpr v₈, h₇.gpr, vm_gpr v₆, vm_gpr v₅, h₄.gpr, vm_gpr v₃, vm_gpr v₂, vm_gpr v₁],
    by rw [vm_rd v₈, h₇.rd, vm_rd v₆, vm_rd v₅, h₄.rd, vm_rd v₃, vm_rd v₂, vm_rd v₁],
    by rw [vm_wr v₈, h₇.wr, vm_wr v₆, vm_wr v₅, h₄.wr, vm_wr v₃, vm_wr v₂, vm_wr v₁],
    by rw [m₈, m₇, m₆, m₅, m₄]; exact mo₃, fun l hl i hi => (u₈ l hl i hi).2, ?_⟩
  obtain f₈ : ∀ l < 4, fe5 (lanes t 5 l) = fe5 (aOp (lanes s 0) l) * F s.mem b (64 + 32 * (12 + l)) :=
    fun l hl => by
      rw [fe5_congr (fun i hi => (u₈ l hl i hi).1),
        fe5_carry _ (by rw [l₇ l hl 4 (by decide)]; have := b₆ l hl 4 (by decide)
                        have : prodBound < 2 ^ 63 := by decide
                        omega_arith),
        fe5_congr (fun i hi => l₇ l hl i hi), p₆ l hl]
  obtain ⟨a0, a1, a2, a3⟩ := aOp_fe (lanes s 0) hx
  rw [← cacheOf_eq]
  simp only [lanePt5, cacheOf, lanePt]
  rw [f₈ 0 (by decide), f₈ 1 (by decide), f₈ 2 (by decide), f₈ 3 (by decide), a0, a1, a2, a3]
  rw [show F s.mem b 448 = 1 from h12, show F s.mem b 480 = 1 from h13,
    show F s.mem b 512 = _ from h14, show F s.mem b 544 = 2 from h15]

/-! ## The accumulators' rows -/

/-- Quadword `k` of half `h` of a `zmm` register. -/
theorem zmm_qword (s : State) (r : XReg) {h k : Nat} (hh : h < 2) (hk : k < 4) :
    (s.zmm r).extractLsb' (8 * (32 * h + 8 * k)) (8 * 8) = zq s r h k := by
  rw [zq, ← zmm_lane s r (i := 2 * h + k / 2) (by omega_arith), qword, extract_extract _ _ _ _ _ (by omega_arith)]
  congr 1; omega_arith

/-- Quadword `k` of a `ymm` register. -/
theorem ymm_qword (s : State) (r : XReg) {k : Nat} (hk : k < 4) :
    (s.ymm r).extractLsb' (8 * (8 * k)) (8 * 8) = qw s r k := by
  rw [← VG.Proof.Poly1305.X86_64.Avx2.qword256_ymm s r hk, qword256]
  congr 1; omega_arith

theorem readW_zmm (m : Mem) (a : Addr) (s : State) (r : XReg) {h k : Nat} (hh : h < 2) (hk : k < 4) :
    (m.writeW a (s.zmm r)).readW (a + BitVec.ofNat 64 (32 * h + 8 * k)) 64 = zq s r h k := by
  obtain e := readW_writeW_inside m a (s.zmm r) (k := 32 * h + 8 * k) (n := 8) (by omega_arith) (by decide)
  rw [zmm_qword s r hh hk] at e
  exact e

theorem readW_ymm (m : Mem) (a : Addr) (s : State) (r : XReg) {k : Nat} (hk : k < 4) :
    (m.writeW a (s.ymm r)).readW (a + BitVec.ofNat 64 (8 * k)) 64 = qw s r k := by
  obtain e := readW_writeW_inside m a (s.ymm r) (k := 8 * k) (n := 8) (by omega_arith) (by decide)
  rw [ymm_qword s r hk] at e
  exact e

theorem zst_ok {z : State} {b : Addr} (hs : Scratch z b) {d : Nat} (hd : d + 64 ≤ 8192) (r : Nat) :
    WP isa (.block [.vmovdqu32Store (sc d) (y r)]) z fun t =>
      t = z.setMem (z.mem.writeW (b + BitVec.ofNat 64 d) (z.zmm (y r))) := by
  obtain hw : InRegions z.wr (b + BitVec.ofNat 64 d) 64 := ⟨_, hs.wr, Offset.contains_base b hd (by omega_arith)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_sc' hs.rdi, State.store512_eq, hw, ite_true,
    Option.some.injEq, exists_eq_left']

theorem yst_ok {s : State} {b : Addr} (hs : Scratch s b) {d : Nat} (hd : d + 32 ≤ 8192) (r : Nat) :
    WP isa (.block [st d r]) s fun t => t = s.setMem (s.mem.writeW (b + BitVec.ofNat 64 d) (s.ymm (y r))) := by
  obtain hw : InRegions s.wr (b + BitVec.ofNat 64 d) 32 := ⟨_, hs.wr, Offset.contains_base b hd (by omega_arith)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, st, ea_sc' hs.rdi, State.store256_eq, hw,
    ite_true, Option.some.injEq, exists_eq_left']

theorem yld_ok {s : State} {b : Addr} (hs : Scratch s b) {d : Nat} (hd : d + 32 ≤ 8192) {r : Nat} (hr : r < 16) :
    WP isa (.block [ld r d]) s fun t => (∀ k < 4, qw t (xr r) k = mq s.mem b (d + 8 * k)) ∧
      (∀ x, x ≠ xr r → ∀ k < 4, qw t x k = qw s x k) ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.syms = s.syms := by
  obtain hin : InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 d) 32 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base b hd (by omega_arith)⟩
  obtain hy : y r = xr r := y_xr r hr
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ld, ea_sc' hs.rdi, State.load256, hin, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun k hk => ?_, fun x hx k hk => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [VG.Proof.Poly1305.X86_64.Avx2.qw_load _ _ _ _ hk, hy, ite_eq_left_iff.mpr (fun h => absurd rfl h), mq,
      Offset.add_ofNat_add_ofNat]
  · rw [VG.Proof.Poly1305.X86_64.Avx2.qw_load _ _ _ _ hk, hy]; exact ite_eq_right_iff.mpr fun h => absurd h hx

/-- The halves of `zmm0–zmm4` to the rows at `ZACC`. -/
theorem zstores_ok {b : Addr} : ∀ n ≤ 5, ∀ z : State, Scratch z b →
    WP isa (.block ((List.range n).map fun j => .vmovdqu32Store (sc (ZACC + 64 * j)) (y j))) z fun t =>
      (∀ j < n, ∀ h < 2, ∀ k < 4, mq t.mem b (ZACC + 64 * j + (32 * h + 8 * k)) = zq z (y j) h k) ∧
      Outside b ZACC (64 * n) z.mem t.mem ∧ t = z.setMem t.mem
  | 0, _, z, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, by cases z; rfl⟩
  | n + 1, hn, z, hs => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zstores_ok n (by omega_arith) z hs) fun t₁ ⟨c₁, o₁, e₁⟩ => ?_
    obtain hs₁ : Scratch t₁ b := ⟨by rw [e₁]; exact hs.rdi, by rw [e₁]; exact hs.wr, hs.nowrap⟩
    refine WP.mono (zst_ok hs₁ (d := ZACC + 64 * n) (by unfold ZACC; omega_arith) n) fun t et => ?_
    obtain ez : t₁.zmm (y n) = z.zmm (y n) := by rw [e₁]; rfl
    refine ⟨fun j hj h hh k hk => ?_, fun a ha => ?_, ?_⟩
    · rw [et]
      by_cases hjn : j = n
      · subst hjn
        rw [State.setMem_mem, mq, ez, ← Offset.add_ofNat_add_ofNat b (ZACC + 64 * j) (32 * h + 8 * k)]
        exact readW_zmm _ _ z _ hh hk
      · rw [State.setMem_mem, mq, readW_writeW_off _ _ _ (d := ZACC + 64 * j + (32 * h + 8 * k)) (n := 8)
          (by unfold ZACC; omega_arith) (by unfold ZACC; omega_arith) (Or.inl (by unfold ZACC; omega_arith))]
        exact c₁ j (by omega_arith) h hh k hk
    · rw [et, State.setMem_mem, writeW_byte_off _ _ _ _ ?_, o₁ a (by omega_arith)]
      simp only [ofs] at ha
      rw [sub_off]; have := (a - b).isLt; unfold ZACC at *; omega_arith
    · rw [et, e₁]; rfl

/-- `ymm0–ymm4` to the low halves of the rows at `ZACC`. -/
theorem ystores_ok {b : Addr} : ∀ n ≤ 5, ∀ s : State, Scratch s b →
    WP isa (.block ((List.range n).map fun j => st (ZACC + 64 * j) j)) s fun t =>
      (∀ j < n, ∀ k < 4, mq t.mem b (ZACC + 64 * j + 8 * k) = qw s (xr j) k) ∧
      (∀ j < 5, ∀ k < 4, mq t.mem b (ZACC + 64 * j + 32 + 8 * k) = mq s.mem b (ZACC + 64 * j + 32 + 8 * k)) ∧
      Outside b ZACC 320 s.mem t.mem ∧ t = s.setMem t.mem
  | 0, _, s, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl,
      Outside.refl _ _ _ _, by cases s; rfl⟩
  | n + 1, hn, s, hs => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (ystores_ok n (by omega_arith) s hs) fun t₁ ⟨c₁, u₁, o₁, e₁⟩ => ?_
    obtain hs₁ : Scratch t₁ b := ⟨by rw [e₁]; exact hs.rdi, by rw [e₁]; exact hs.wr, hs.nowrap⟩
    refine WP.mono (yst_ok hs₁ (d := ZACC + 64 * n) (by unfold ZACC; omega_arith) n) fun t et => ?_
    obtain ey : t₁.ymm (y n) = s.ymm (y n) := by rw [e₁]; rfl
    refine ⟨fun j hj k hk => ?_, fun j hj k hk => ?_, fun a ha => ?_, ?_⟩
    · rw [et]
      by_cases hjn : j = n
      · subst hjn
        rw [State.setMem_mem, mq, ey, ← Offset.add_ofNat_add_ofNat b (ZACC + 64 * j) (8 * k),
          readW_ymm _ _ s _ hk, y_xr j (by omega_arith)]
      · rw [State.setMem_mem, mq, readW_writeW_off _ _ _ (d := ZACC + 64 * j + 8 * k) (n := 8)
          (by unfold ZACC; omega_arith) (by unfold ZACC; omega_arith) (by unfold ZACC; omega_arith)]
        exact c₁ j (by omega_arith) k hk
    · rw [et, State.setMem_mem, mq, readW_writeW_off _ _ _ (d := ZACC + 64 * j + 32 + 8 * k) (n := 8)
        (by unfold ZACC; omega_arith) (by unfold ZACC; omega_arith) (by unfold ZACC; omega_arith)]
      exact u₁ j hj k hk
    · rw [et, State.setMem_mem, writeW_byte_off _ _ _ _ ?_, o₁ a ha]
      simp only [ofs] at ha
      rw [sub_off]; have := (a - b).isLt; unfold ZACC at *; omega_arith
    · rw [et, e₁]; rfl

/-- The rows at `f j` into `ymm0–ymm4`. -/
theorem yloads_ok {b : Addr} {f : Nat → Nat} (hf : ∀ j < 5, f j + 32 ≤ 8192) :
    ∀ n ≤ 5, ∀ s : State, Scratch s b →
    WP isa (.block ((List.range n).map fun j => ld j (f j))) s fun t =>
      (∀ j < n, ∀ k < 4, qw t (xr j) k = mq s.mem b (f j + 8 * k)) ∧
      (∀ r < 16, n ≤ r → ∀ k < 4, qw t (xr r) k = qw s (xr r) k) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms
  | 0, _, s, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ _ => rfl, rfl, rfl, rfl,
      rfl, rfl⟩
  | n + 1, hn, s, hs => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (yloads_ok hf n (by omega_arith) s hs) fun t₁ ⟨c₁, k₁, g₁, m₁, rd₁, wr₁, sy₁⟩ => ?_
    obtain hs₁ : Scratch t₁ b := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
    refine WP.mono (yld_ok hs₁ (hf n (by omega_arith)) (r := n) (by omega_arith))
      fun t ⟨c, k, g, m, rd, wr, sy⟩ => ⟨fun j hj q hq => ?_, fun r hr hnr q hq => ?_, g.trans g₁, m.trans m₁,
        rd.trans rd₁, wr.trans wr₁, sy.trans sy₁⟩
    · by_cases hjn : j = n
      · subst hjn; rw [c q hq, m₁]
      · rw [k _ (xr_ne' j (by omega_arith) n (by omega_arith) hjn) q hq, c₁ j (by omega_arith) q hq]
    · rw [k _ (xr_ne' r hr n (by omega_arith) (by omega_arith)) q hq, k₁ r hr (by omega_arith) q hq]

/-! ## `32 A + B` -/

theorem qw_half0 (b : Addr) (w : State) (r : XReg) {k : Nat} (hk : k < 4) : qw (Zmm.half b 0 w) r k = qw w r k := by
  rw [qw_half b w r hk]
  simp only [zq, qw, State.zlane, Nat.mul_zero, Nat.zero_add, show k / 2 < 2 by omega_arith, ite_true]

theorem lanes_eq_of {s t : State} {r : Nat} (h : ∀ i < 5, ∀ l < 4, qw t (xr (r + i)) l = qw s (xr (r + i)) l) :
    ∀ l < 4, ∀ i < 5, lanes t r l i = lanes s r l i := fun l hl i hi => by
  simp only [lanes]; rw [h i hi l hl]

theorem lanePt_eq_of {s t : State} (h : ∀ l < 4, ∀ i < 5, lanes t 0 l i = lanes s 0 l i) : lanePt t = lanePt s := by
  simp only [lanePt]
  rw [fe5_congr (h 0 (by decide)), fe5_congr (h 1 (by decide)), fe5_congr (h 2 (by decide)),
    fe5_congr (h 3 (by decide))]

theorem lanePt5_eq_of {s t : State} (h : ∀ l < 4, ∀ i < 5, lanes t 5 l i = lanes s 5 l i) :
    lanePt5 t = lanePt5 s := by
  simp only [lanePt5]
  rw [fe5_congr (h 0 (by decide)), fe5_congr (h 1 (by decide)), fe5_congr (h 2 (by decide)),
    fe5_congr (h 3 (by decide))]

theorem _root_.VG.Proof.Ed25519.X86_64.Ifma.EConsts.zacc {m m' : Mem} {b : Addr} (hk : EConsts m b) (h : Outside b ZACC 320 m m') : EConsts m' b :=
  hk.of_mq fun d _ h2 => by
    rw [VG.Proof.X25519.X86_64.Ifma.mq_eq_word, VG.Proof.X25519.X86_64.Ifma.mq_eq_word]
    exact h.word (Or.inl (by unfold ZACC; omega_arith)) (by omega_arith)

theorem outside_mq {m m' : Mem} {b : Addr} {o n : Nat} (h : Outside b o n m m') {d : Nat}
    (hd : d + 8 ≤ o ∨ o + n ≤ d) (hd' : d + 8 < 2 ^ 64) : mq m' b d = mq m b d :=
  h.word hd hd'

theorem ztail2_split : ztail2 ++ vstore = (List.range 5).map (fun j => st (ZACC + 64 * j) j) ++
    ((List.range 5).map (fun j => ld j (ZACC + 64 * j + 32)) ++
    ((vaddA ++ carry id ++ vstA ++ vrowsK ++ esplit ++ mul4 OPL ++ vmovs ++ carry (5 + ·)) ++
    ((List.range 5).map (fun j => ld j (ZACC + 64 * j)) ++ (vadd ++ vstore)))) := by
  simp only [ztail2, vrowsK, vmovs, List.append_assoc, List.cons_append, List.nil_append]

/-- After the steps, with `A` in half 0 and `B` in half 1 of the lanes: `32 A + B` in slots 0–3. -/
theorem ztail_ok {w : State} {b : Addr} (hs : Scratch w b) (hk : EConsts w.mem b)
    (hA : Small (Zmm.half b 0 w)) (hB : Small (Zmm.half b 1 w)) {a c : EPoint dZ}
    (ha : Rep (lanePt (Zmm.half b 0 w)) a) (hc : Rep (lanePt (Zmm.half b 1 w)) c)
    (h12 : F w.mem b (offset 12) = 1) (h13 : F w.mem b (offset 13) = 1)
    (h14 : F w.mem b (offset 14) = Spec.Ed25519.d + Spec.Ed25519.d) (h15 : F w.mem b (offset 15) = 2) :
    WP isa (.seq (.block ztail1) (.seq vdbl5 (.block (ztail2 ++ vstore)))) w fun t =>
      (∀ r, r ≠ .rsi → t.gpr r = w.gpr r) ∧ t.rd = w.rd ∧ t.wr = w.wr ∧
      Outside b 64 (ZACC + 320 - 64) w.mem t.mem ∧
      Rep (point (env t.mem b) 0 1 2 3) ((32 : Nat) • a + c) := by
  -- the halves to `ZACC`
  refine WP.seq (WP.mono (zstores_ok 5 (by decide) w hs) fun t₁ ⟨c₁, o₁, e₁⟩ => ?_)
  obtain hs₁ : Scratch t₁ b := ⟨by rw [e₁]; exact hs.rdi, by rw [e₁]; exact hs.wr, hs.nowrap⟩
  obtain q₁ : ∀ r k, k < 4 → qw t₁ r k = qw w r k := fun r k hk => by rw [e₁]; rfl
  obtain hk₁ : EConsts t₁.mem b := hk.zacc o₁
  obtain l₁ : ∀ l < 4, ∀ i < 5, lanes t₁ 0 l i = lanes (Zmm.half b 0 w) 0 l i := fun l hl i hi => by
    simp only [lanes]; rw [q₁ _ _ hl, qw_half0 b w _ hl]
  -- `32 A`
  refine WP.seq (WP.mono (vdbl5_ok hs₁ hk₁ (fun l hl i hi => by rw [l₁ l hl i hi]; exact hA l hl i hi)
    (a := a) (by rw [lanePt_eq_of l₁]; exact ha)) fun t₂ ⟨g₂, rd₂, wr₂, o₂, sm₂, p₂⟩ => ?_)
  obtain hs₂ : Scratch t₂ b := ⟨by rw [g₂ _ (by decide)]; exact hs₁.rdi, by rw [wr₂]; exact hs₁.wr, hs.nowrap⟩
  obtain hk₂ : EConsts t₂.mem b := hk₁.outside o₂
  rw [ztail2_split, WP.block_append_iff]
  -- `32 A` to `ZACC`
  refine WP.mono (ystores_ok 5 (by decide) t₂ hs₂) fun t₃ ⟨c₃, u₃, o₃, e₃⟩ => ?_
  obtain hs₃ : Scratch t₃ b := ⟨by rw [e₃]; exact hs₂.rdi, by rw [e₃]; exact hs₂.wr, hs.nowrap⟩
  obtain hk₃ : EConsts t₃.mem b := hk₂.zacc o₃
  -- `B`
  rw [WP.block_append_iff]
  refine WP.mono (yloads_ok (f := fun j => ZACC + 64 * j + 32) (fun j hj => by unfold ZACC; omega_arith) 5 (by decide)
    t₃ hs₃) fun t₄ ⟨c₄, k₄, g₄, m₄, rd₄, wr₄, _⟩ => ?_
  obtain hs₄ : Scratch t₄ b := ⟨by rw [g₄]; exact hs₃.rdi, by rw [wr₄]; exact hs₃.wr, hs.nowrap⟩
  obtain l₄ : ∀ l < 4, ∀ i < 5, lanes t₄ 0 l i = lanes (Zmm.half b 1 w) 0 l i := fun l hl i hi => by
    simp only [lanes, Nat.zero_add]
    rw [c₄ i hi l hl, u₃ i hi l hl, outside_mq o₂ (Or.inr (by unfold ZACC; omega_arith)) (by unfold ZACC; omega_arith),
      qw_half b w _ hl, ← y_xr i (by omega_arith), ← c₁ i hi 1 (by decide) l hl, Nat.add_assoc]
  obtain F₄ : ∀ d, d + 32 ≤ 1024 → F t₄.mem b d = F w.mem b d := fun d hd => by
    rw [m₄, Outside_F o₃ (by omega_arith) (Or.inl (by unfold ZACC; omega_arith)), Outside_F o₂ (by omega_arith) (Or.inl hd),
      Outside_F o₁ (by omega_arith) (Or.inl (by unfold ZACC; omega_arith))]
  -- `B`'s cached point
  rw [WP.block_append_iff]
  refine WP.mono (vcache_wp hs₄ (by rw [m₄]; exact hk₃)
    (fun l hl i hi => by rw [l₄ l hl i hi]; exact hB l hl i hi)
    (by rw [F₄ _ (by decide)]; exact h12) (by rw [F₄ _ (by decide)]; exact h13)
    (by rw [F₄ _ (by decide)]; exact h14) (by rw [F₄ _ (by decide)]; exact h15))
    fun t₅ ⟨g₅, rd₅, wr₅, o₅, b₅, p₅⟩ => ?_
  obtain hs₅ : Scratch t₅ b := ⟨by rw [g₅]; exact hs₄.rdi, by rw [wr₅]; exact hs₄.wr, hs.nowrap⟩
  -- `32 A` back
  rw [WP.block_append_iff]
  refine WP.mono (yloads_ok (f := fun j => ZACC + 64 * j) (fun j hj => by unfold ZACC; omega_arith) 5 (by decide)
    t₅ hs₅) fun t₆ ⟨c₆, k₆, g₆, m₆, rd₆, wr₆, _⟩ => ?_
  obtain hs₆ : Scratch t₆ b := ⟨by rw [g₆]; exact hs₅.rdi, by rw [wr₆]; exact hs₅.wr, hs.nowrap⟩
  obtain l₆ : ∀ l < 4, ∀ i < 5, lanes t₆ 0 l i = lanes t₂ 0 l i := fun l hl i hi => by
    simp only [lanes, Nat.zero_add]
    rw [c₆ i hi l hl, outside_mq o₅ (Or.inr (by unfold ZACC; omega_arith)) (by unfold ZACC; omega_arith), m₄, c₃ i hi l hl]
  obtain l₆' : ∀ l < 4, ∀ i < 5, lanes t₆ 5 l i = lanes t₅ 5 l i :=
    lanes_eq_of fun i hi l hl => k₆ (5 + i) (by omega_arith) (by omega_arith) l hl
  obtain hk₆ : EConsts t₆.mem b := by rw [m₆]; exact (hk₃.outside (by rw [← m₄]; exact o₅))
  -- the sum
  rw [WP.block_append_iff]
  refine WP.mono (vadd_wp hs₆.rdi (ctx_of hs₆) hk₆ (fun l hl i hi => by rw [l₆ l hl i hi]; exact sm₂ l hl i hi)
    (fun l hl i hi => by rw [l₆' l hl i hi]; exact b₅ l hl i hi)) fun t₇ ⟨g₇, rd₇, wr₇, o₇, sm₇, p₇⟩ => ?_
  obtain hs₇ : Scratch t₇ b := ⟨by rw [g₇]; exact hs₆.rdi, by rw [wr₇]; exact hs₆.wr, hs.nowrap⟩
  obtain pt₇ : Rep (lanePt t₇) ((32 : Nat) • a + c) := by
    rw [p₇, lanePt_eq_of l₆, lanePt5_eq_of l₆', p₅, lanePt_eq_of l₄, vAddPt_cache]
    exact pointAdd_rep p₂ hc
  -- to slots 0–3
  refine WP.mono (vstore_wp hs₇.rdi (ctx_of hs₇) (hk₆.outside o₇) sm₇) fun t ⟨g, rd, wr, o, f⟩ => ?_
  obtain eg₃ : t₃.gpr = t₂.gpr := by rw [e₃]; rfl
  obtain eg₁ : t₁.gpr = w.gpr := by rw [e₁]; rfl
  obtain er₃ : t₃.rd = t₂.rd := by rw [e₃]; rfl
  obtain er₁ : t₁.rd = w.rd := by rw [e₁]; rfl
  obtain ew₃ : t₃.wr = t₂.wr := by rw [e₃]; rfl
  obtain ew₁ : t₁.wr = w.wr := by rw [e₁]; rfl
  refine ⟨fun r hr => by rw [g, g₇, g₆, g₅, g₄, eg₃, g₂ r hr, eg₁],
    by rw [rd, rd₇, rd₆, rd₅, rd₄, er₃, rd₂, er₁], by rw [wr, wr₇, wr₆, wr₅, wr₄, ew₃, wr₂, ew₁], ?_, ?_⟩
  · intro x hx
    obtain hx' : ofs b x < 64 ∨ 6400 ≤ ofs b x := by unfold ZACC at hx; omega_arith
    refine (o x (by omega_using [hx'])).trans ((o₇ x (by omega_using [hx'])).trans ?_)
    rw [m₆]
    refine (o₅ x (show ofs b x < 1024 ∨ 1024 + 320 ≤ ofs b x by omega_using [hx'])).trans ?_
    rw [m₄]
    exact (o₃ x (show ofs b x < 6080 ∨ 6080 + 320 ≤ ofs b x by omega_using [hx'])).trans
      ((o₂ x (by omega_using [hx'])).trans (o₁ x (show ofs b x < 6080 ∨ 6080 + 64 * 5 ≤ ofs b x by omega_using [hx'])))
  · have pt : point (env t.mem b) 0 1 2 3 = lanePt t₇ := by
      simp only [point, lanePt, env, VG.Impl.Ed25519.X86_64.offset]
      rw [← f 0 (by decide), ← f 1 (by decide), ← f 2 (by decide), ← f 3 (by decide)]
      rfl
    rw [pt]; exact pt₇

end VG.Proof.Ed25519.X86_64.Zmm

end

end


/-!
# The `zmm` comb: the multiplication

`Zmm.combMultiply` leaves `[s]B` in slots 0–3, as `combMultiply` does: the
constants (`zConstOps`, `vload`'s, and the rows of the `zmm` code, `zconsts`,
which also puts `[G]B` into both halves of the lanes), the 26 steps
(`zstep_ok`) with MXCSR `0x1FBF`, and `32 A + B` (`ztail_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Zmm

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Zmm VG.Proof.Ed25519.X86_64.Ifma
  VG.Proof.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Impl.Ed25519.X86_64.Ifma (vload)
open VG.Proof.X25519.X86_64.Ifma (lanes fe5 fe5_congr consts_wp cregs mq)
open VG.Proof.X25519.X86_64 (Outside F off ofs clob)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

variable {fld : Arith} [EdArith fld]

/-! ## Frames -/

theorem outside_readW {m m' : Mem} {b : Addr} {o n : Nat} (h : Outside b o n m m') {d w : Nat}
    (hd : d + w / 8 ≤ o ∨ o + n ≤ d) (hd' : d + w / 8 < 2 ^ 64) :
    m'.readW (b + BitVec.ofNat 64 d) w = m.readW (b + BitVec.ofNat 64 d) w :=
  Mem.readW_congr fun i hi => by
    rw [Offset.add_ofNat_add_ofNat]
    exact h _ (by simp only [ofs]; rw [off_ofNat _ (by omega_arith)]; omega_arith)

theorem ZFrame.outside {s₀ s : State} {b : Addr} (h : ZFrame s₀ b s) : Outside b 1152 5424 s₀.mem s.mem :=
  fun a ha => h.mem a (by unfold ZChg InZ DigOff SGA SGB combSignMask ZMASK ZB; omega_arith)

theorem half_lanes {s t : State} (b : Addr) (hz : ∀ r i, i < 4 → t.zlane r i = s.zlane r i) {h : Nat}
    (hh : h < 2) (r l i : Nat) (hl : l < 4) : lanes (Zmm.half b h t) r l i = lanes (Zmm.half b h s) r l i := by
  simp only [lanes]; rw [qw_half b t _ hl, qw_half b s _ hl]; simp only [zq]; rw [hz _ _ (by omega_arith)]

/-! ## Before the loop -/

theorem zConst_env (e : Env) : point (evalOps zConstOps e) 0 1 2 3 = combG ∧
    evalOps zConstOps e 12 = 1 ∧ evalOps zConstOps e 13 = 1 ∧
    evalOps zConstOps e 14 = Spec.Ed25519.d + Spec.Ed25519.d ∧ evalOps zConstOps e 15 = 2 := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  rw [← constPoint_eval combG e]
  rfl

/-- The constants, the rows of the `zmm` code, and `[G]B` in both halves. -/
theorem zprep_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block (fieldCode fld zConstOps ++ VG.Impl.X25519.X86_64.Ifma.consts ++ vload ++ zconsts)) s
      fun t => Scratch t base ∧ (∀ r, r ∉ clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      TableFrame base 56 7368 s.mem t.mem ∧ EConsts t.mem base ∧ ZOK base t ∧
      (∀ h < 2, EConsts (Zmm.half base h t).mem base) ∧ (∀ h < 2, Small (Zmm.half base h t)) ∧
      (∀ h < 2, lanePt (Zmm.half base h t) = combG) ∧ (∀ h < 2, F t.mem base (ZK2 + 32 * h) = 2) ∧
      F t.mem base (offset 12) = 1 ∧ F t.mem base (offset 13) = 1 ∧
      F t.mem base (offset 14) = Spec.Ed25519.d + Spec.Ed25519.d ∧ F t.mem base (offset 15) = 2 ∧
      (∀ q < 256, t.mem (off base (768 + q)) = s.mem (off base (768 + q))) := by
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok (fld := fld) hs zConstOps) fun s₁ ⟨k₁, v₁⟩ => ?_
  obtain hs₁ := hs.of_keep k₁
  rw [WP.block_append_iff]
  refine WP.mono (consts_wp s₁) fun s₂ ⟨ha, hc, hd, hb, h8, h9, h10, _, _, g₂, m₂, rd₂, wr₂, _, _, _⟩ => ?_
  obtain hs₂ : Scratch s₂ base :=
    ⟨by rw [g₂ _ (by decide)]; exact hs₁.rdi, by rw [wr₂]; exact hs₁.wr, hs₁.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (vload_wp hs₂.rdi (ctx_of hs₂) ha hc hd hb h8 h9 h10) fun s₃ ⟨g₃, rd₃, wr₃, o₃, k₃, u₃⟩ => ?_
  obtain hs₃ : Scratch s₃ base := ⟨by rw [g₃]; exact hs₂.rdi, by rw [wr₃]; exact hs₂.wr, hs.nowrap⟩
  refine WP.mono (zconsts_ok hs₃ k₃) fun t ⟨hk, mk, k2, ft, qt, gt, rdt, wrt, _⟩ => ?_
  obtain ot : Outside base ZB 1856 s₃.mem t.mem := fun a ha => ft a (by unfold ZB at *; omega_arith)
  obtain fs₃ : ∀ (i : Slot), i.val < 16 → F s₃.mem base (offset i) = evalOps zConstOps (env s.mem base) i :=
    fun i hi => by
      rw [Outside_F o₃ (by simp only [offset]; omega_arith) (Or.inl (by simp only [offset]; omega_arith)), m₂, ← v₁]
      rfl
  obtain fs : ∀ (i : Slot), i.val < 16 → F t.mem base (offset i) = evalOps zConstOps (env s.mem base) i :=
    fun i hi => by
      rw [Outside_F ot (by simp only [offset]; omega_arith) (Or.inl (by simp only [offset, ZB]; omega_arith)), fs₃ i hi]
  obtain lt : ∀ h < 2, ∀ l < 4, ∀ i < 5, lanes (Zmm.half base h t) 0 l i = lanes s₃ 0 l i :=
    fun h hh l hl i hi => by simp only [lanes, Nat.zero_add]; rw [qt h hh i hi l hl]
  obtain pt : lanePt s₃ = combG := by
    obtain e : ∀ l (hl : l < 4), fe5 (lanes s₃ 0 l) = env s₁.mem base ⟨l, by omega_arith⟩ := fun l hl => by
      rw [fe5_congr (fun i hi => (u₃ l hl i hi).1), fe5_load, m₂]; rfl
    simp only [lanePt]
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide),
      ← (zConst_env (env s.mem base)).1, ← v₁]
    rfl
  obtain cz := zConst_env (env s.mem base)
  refine ⟨⟨by rw [gt]; exact hs₃.rdi, by rw [wrt]; exact hs₃.wr, hs.nowrap⟩, fun r hr => ?_,
    by rw [rdt, rd₃, rd₂, k₁.rd], by rw [wrt, wr₃, wr₂, k₁.wr], ?_,
    k₃.of_mq fun d _ h2 => outside_mq ot (Or.inl (by unfold ZB; omega_arith)) (by omega_arith),
    ⟨by rw [gt]; exact hs₃.rdi, by rw [wrt]; exact hs₃.wr, hs.nowrap, mk⟩, hk,
    fun h hh l hl i hi => by rw [lt h hh l hl i hi]; have := (u₃ l hl i hi).2; omega_arith,
    fun h hh => by rw [lanePt_eq_of (lt h hh)]; exact pt,
    fun h hh => by rw [k2 h hh, fs₃ 15 (by decide)]; exact cz.2.2.2.2,
    by rw [fs 12 (by decide)]; exact cz.2.1, by rw [fs 13 (by decide)]; exact cz.2.2.1,
    by rw [fs 14 (by decide)]; exact cz.2.2.2.1, by rw [fs 15 (by decide)]; exact cz.2.2.2.2, fun q hq => ?_⟩
  · rw [gt, g₃, g₂ r (fun h => hr (VG.Proof.Ed25519.X86_64.Ifma.cregs_clob r h)), k₁.gpr r hr]
  · rw [m₂] at o₃
    exact (TableFrame.workspace k₁.mem).trans (((TableFrame.table o₃).mono (by decide) (by decide)).trans
      ((TableFrame.table ot).mono (by decide) (by decide)))
  · rw [ot _ (Or.inl (by rw [bits_far hq]; unfold ZB; omega_arith)), o₃ _ (Or.inl (by rw [bits_far hq]; omega_arith)), m₂,
      k₁.mem _ (Or.inr (by rw [bits_far hq]; omega_arith))]

/-! ## The multiplication -/

/-- `A`'s value after `c` steps: `[G]B` plus the odd digits'. -/
def zvA (S c : Nat) : ℤ := (VG.Proof.Ed25519.X86_64.combGVal : ℤ) + VG.Proof.Ed25519.X86_64.oddSumZ S c

/-- `B`'s value after `c` steps: `[G]B` plus the even digits'. -/
def zvB (S c : Nat) : ℤ := (VG.Proof.Ed25519.X86_64.combGVal : ℤ) + VG.Proof.Ed25519.X86_64.evenSumZ S c

theorem zvA_succ (S j : Nat) :
    zvA S (j + 1) = VG.Proof.Ed25519.X86_64.sdig S (2 * j + 1) * 1024 ^ j + zvA S j := by
  simp only [zvA, VG.Proof.Ed25519.X86_64.oddSumZ]
  rw [Int.add_comm _ ((VG.Proof.Ed25519.X86_64.combGVal : ℤ) + _), Int.add_assoc]

theorem zvB_succ (S j : Nat) :
    zvB S (j + 1) = VG.Proof.Ed25519.X86_64.sdig S (2 * j) * 1024 ^ j + zvB S j := by
  simp only [zvB, VG.Proof.Ed25519.X86_64.evenSumZ]
  rw [Int.add_comm _ ((VG.Proof.Ed25519.X86_64.combGVal : ℤ) + _), Int.add_assoc]

theorem zv_sum {S : Nat} (hS : S < 2 ^ 256) : ((32 : Nat) : ℤ) * zvA S 26 + zvB S 26 = S := by
  rw [← VG.Proof.Ed25519.X86_64.comb_sum hS]
  simp only [zvA, zvB, VG.Proof.Ed25519.X86_64.combVal, show ¬ 52 ≤ 26 by decide, ↓reduceIte,
    show 52 - 26 = 26 from rfl, Nat.cast_ofNat]
  rw [Int.add_assoc]

/-- `Zmm.combMultiply`: `[s]B` into slots 0–3, for the scalar bits expanded into bytes 768
onward. -/
theorem zcomb_ok {s : State} {base T : Addr} (hs : Scratch s base) {S : Nat}
    (hS : S < 2 ^ (16 * 16)) (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (ht : CombTbl s T) (hfar : TblFar base T) :
    WP isa (Zmm.combMultiply fld) s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ PowersKeep base 56 7368 s t := by
  rw [Zmm.combMultiply]
  refine WP.seq (WP.mono_syms (zprep_ok (fld := fld) hs)
    fun s₃ ⟨hs₃, g₁, rd₁, wr₁, m₁, k₁, z₁, hk₁, sm₁, p₁, k2₁, f12, f13, f14, f15, b₁⟩ sy₁ => ?_)
  obtain keep₃ : PowersKeep base 56 7368 s s₃ := ⟨fun r _ _ hr => g₁ r hr, rd₁, wr₁, m₁⟩
  obtain hp : ZLoopPre s₃ base T S :=
    { scratch := hs₃
      zok := z₁
      hconsts := hk₁
      consts := k₁
      k2 := k2₁
      bits := fun q hq => by rw [b₁ q hq]; exact hb q hq
      tbl := ht.keep hfar keep₃ (by rw [sy₁])
      far := hfar }
  refine WP.seq (WP.mono_syms (zscal rfl (mov32_wp s₃ .rbx 0))
    fun s₄ ⟨⟨r₄, g₄, m₄, rd₄, wr₄, _⟩, zl₄⟩ sy₄ => ?_)
  obtain zl : ∀ r i, i < 4 → s₄.zlane r i = s₃.zlane r i := fun r i _ => by rw [zl₄]
  obtain i₄ : ZInv s₃ base 0 (zvA S 0) (zvB S 0) s₄ := by
    obtain g0 : Rep combG ((zvA S 0) • baseAff) := by
      rw [show zvA S 0 = (VG.Proof.Ed25519.X86_64.combGVal : ℤ) by simp [zvA, VG.Proof.Ed25519.X86_64.oddSumZ],
        natCast_zsmul]
      exact VG.Proof.Ed25519.X86_64.combG_ok
    refine ⟨by decide, by rw [g₄ _ (by decide)]; exact hs₃.rdi, by rw [r₄]; rfl,
      ⟨fun r h1 _ _ => g₄ r h1, g₄ _ (by decide), rd₄, wr₄, fun a _ => by rw [m₄], sy₄⟩,
      fun h hh => by show EConsts (hmem base h s₄.mem) base; rw [m₄]; exact hp.hconsts h hh,
      fun h hh l hl i hi => by rw [half_lanes base zl hh 0 l i hl]; exact sm₁ h hh l hl i hi, ?_, ?_⟩
    · rw [lanePt_eq_of (fun l hl i hi => half_lanes base zl (by decide) 0 l i hl), p₁ 0 (by decide)]
      exact g0
    · rw [lanePt_eq_of (fun l hl i hi => half_lanes base zl (by decide) 0 l i hl), p₁ 1 (by decide),
        show zvB S 0 = zvA S 0 by simp [zvA, zvB, VG.Proof.Ed25519.X86_64.oddSumZ,
          VG.Proof.Ed25519.X86_64.evenSumZ]]
      exact g0
  obtain fin : ∀ w, ZInv s₃ base 26 (zvA S 26) (zvB S 26) w →
      WP isa (.seq (.block ztail1) (.seq Impl.Ed25519.X86_64.Ifma.vdbl5
        (.block (ztail2 ++ Impl.Ed25519.X86_64.Ifma.vstore)))) w fun t =>
          Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ PowersKeep base 56 7368 s t := by
    intro w hw
    obtain hsw : Scratch w base := hw.frame.scratch hp hw.rdi
    have ow := hw.frame.outside
    obtain fw : ∀ (i : Slot), 12 ≤ i.val → i.val < 16 → F w.mem base (offset i) = F s₃.mem base (offset i) :=
      fun i h1 h2 => by
        rw [Outside_F ow (by simp only [offset]; omega_arith) (Or.inl (by simp only [offset]; omega_arith))]
    refine WP.mono (ztail_ok hsw (hw.frame.consts hp) (hw.small 0 (by decide)) (hw.small 1 (by decide))
      hw.valA hw.valB (by rw [fw 12 (by decide) (by decide)]; exact f12)
      (by rw [fw 13 (by decide) (by decide)]; exact f13) (by rw [fw 14 (by decide) (by decide)]; exact f14)
      (by rw [fw 15 (by decide) (by decide)]; exact f15)) fun y ⟨yg, yrd, ywr, yo, yp⟩ => ?_
    refine ⟨?_, keep₃.trans (hw.frame.keep.trans ⟨fun r _ h2 _ => by rw [yg r h2], by rw [yrd],
      by rw [ywr], (TableFrame.table yo).mono (by decide) (by decide)⟩)⟩
    rw [← natCast_zsmul, smul_smul, ← add_smul, zv_sum hS, natCast_zsmul] at yp
    exact yp
  refine WP.seq ?_
  apply WP.loop (fun n t => ZInv s₃ base (26 - n) (zvA S (26 - n)) (zvB S (26 - n)) t ∧ 0 < n ∧ n ≤ 26) (n := 26)
  · intro n t ⟨ht', hn0, hn⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega_arith⟩
    refine WP.mono (zstep_ok hp hS ht' (by omega_arith)) fun u ⟨uz, hu⟩ => ?_
    rw [← zvA_succ, ← zvB_succ] at hu
    by_cases hk : k = 0
    · subst hk
      exact Or.inl ⟨by simp only [eval, uz, show 26 - (0 + 1) + 1 = 26 from rfl, decide_true,
        Option.map_some, Bool.not_true], fin u hu⟩
    · refine Or.inr ⟨by simp only [eval, uz, show ¬ (26 - (k + 1) + 1 = 26) by omega_arith, decide_false,
        Option.map_some, Bool.not_false], k, by omega_arith, ?_, by omega_arith, by omega_arith⟩
      rw [show 26 - k = 26 - (k + 1) + 1 by omega_arith]; exact hu
  · exact ⟨i₄, by decide, by decide⟩

end VG.Proof.Ed25519.X86_64.Zmm
