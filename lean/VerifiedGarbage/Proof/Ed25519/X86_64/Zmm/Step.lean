import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Halves
import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Digits
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLoop

/-!
# The `zmm` comb: an addition in each half

After the selection, `zentry_ok`: each half's rows are split into the limbs
of `ymm5–ymm9` (`esplit`, translated), the masks of the signs set
(`zsign`), and the entry, negated for a negative digit, added to the half's
point (`vnegBody`, the carry and `vadd`, translated): what `ventryN_wp` says
of each half.
-/

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
  · obtain rfl : m = 0 := by omega
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> rfl

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
  have hj : ∀ q < 5, q ∉ [15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15] := by decide
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
    rw [off_ofNat _ (by unfold ZB ZMASK at hd; omega)]; unfold InZ; omega)

theorem zq_lanes {z t : State} (k : ∀ r, r ≠ xr 14 → r ≠ xr 15 → ∀ i < 4, t.zlane r i = z.zlane r i)
    (b : Addr) {h : Nat} (hh : h < 2) {r : Nat} (hr : r + 5 ≤ 14) :
    ∀ l < 4, ∀ i < 5, lanes (Zmm.half b h t) r l i = lanes (Zmm.half b h z) r l i := fun l hl i hi => by
  simp only [lanes]
  rw [qw_half b t _ hl, qw_half b z _ hl]
  simp only [zq]
  have hne : ∀ q < 14, xr q ≠ xr 14 ∧ xr q ≠ xr 15 := by decide
  rw [k _ (hne (r + i) (by omega)).1 (hne (r + i) (by omega)).2 _ (by omega)]

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
  have hs₁ : Scratch z₁ b := ⟨by rw [vm_gpr' k₁.vm]; exact hs.rdi, by rw [vm_wr' k₁.vm]; exact hs.wr, hs.nowrap⟩
  refine WP.mono (zsign_ok hs₁ (mA := signMask (n 0)) (mB := signMask (n 1)) (by rw [readW_keep k₁.mem (Or.inr (by unfold SGA ZMASK; omega))]; exact hSA)
    (by rw [readW_keep k₁.mem (Or.inr (by unfold SGB ZMASK; omega))]; exact hSB)) fun z₂ ⟨q₂, k₂⟩ => ?_
  have hs₂ : Scratch z₂ b := ⟨by rw [k₂.gpr _ (by decide)]; exact hs₁.rdi, by rw [k₂.wr]; exact hs₁.wr, hs.nowrap⟩
  have zl₂ : ∀ r, r ≠ xr 14 → r ≠ xr 15 → ∀ i < 4, z₂.zlane r i = z₁.zlane r i :=
    fun r h1 h2 => k₂.zl r (fun h => h.elim h1 h2)
  have m₂ : ∀ h, (Zmm.half b h z₂).mem = (Zmm.half b h z₁).mem := fun h => by
    show hmem b h z₂.mem = hmem b h z₁.mem; rw [k₂.mem]
  have l0 : ∀ h < 2, ∀ l < 4, ∀ i < 5, lanes (Zmm.half b h z₂) 0 l i = lanes (Zmm.half b h z) 0 l i :=
    fun h hh l hl i hi => by
      rw [zq_lanes zl₂ b hh (by decide) l hl i hi]
      simp only [lanes, Nat.zero_add]; rw [q₁ h hh i hi l hl]
  have l5 : ∀ h < 2, ∀ l < 4, ∀ i < 5, lanes (Zmm.half b h z₂) 5 l i = lanes (Zmm.half b h z₁) 5 l i :=
    fun h hh => zq_lanes zl₂ b hh (by decide)
  have o₂ : ZOK b z₂ := ⟨hs₂.rdi, hs₂.wr, hs.nowrap, by rw [k₂.mem]; exact o₁.masks⟩
  refine WP.mono (zadd_ok (bs := fun h => decide (n h < 16)) hs₂ o₂
    (fun h hh => by rw [m₂ h]; exact e₁ h hh)
    (fun h hh l hl i hi => by rw [l0 h hh l hl i hi]; exact hsm h hh l hl i hi)
    (fun h hh k hk => by
      rw [qw_half b z₂ _ hk, q₂ h hh k hk, ← signMask_eq]
      rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> rfl)
    (fun h hh l hl i hi => by rw [l5 h hh l hl i hi]; exact (u₁ h hh l hl i hi).2))
    fun t ⟨o₃, k₃, p₃, sm₃, e₃⟩ => ?_
  have row : ∀ h < 2, ∀ l < 4, fe5 (lanes (Zmm.half b h z₂) 5 l) =
      [combField j (m h) 0, combField j (m h) 1, combField j (m h) 2, 2].getD l 0 := fun h hh l hl => by
    rw [fe5_congr fun i hi => (l5 h hh l hl i hi).trans (u₁ h hh l hl i hi).1,
      entry_fe (w := srow (envOf (Zmm.half b h z))) (fun _ _ => BitVec.isLt _) l]
    have e : ∀ k < 4, srow (envOf (Zmm.half b h z)) l k = (zq z (xr (11 + l)) h k).toNat := fun k hk => by
      show (qw (Zmm.half b h z) (xr (11 + l)) k).toNat = _
      rw [qw_half b z _ hk]
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
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
  have p₂ : ∀ h < 2, lanePt (Zmm.half b h z₂) = lanePt (Zmm.half b h z) := fun h hh => by
    simp only [lanePt]
    rw [fe5_congr (l0 h hh 0 (by decide)), fe5_congr (l0 h hh 1 (by decide)), fe5_congr (l0 h hh 2 (by decide)),
      fe5_congr (l0 h hh 3 (by decide))]
  have p5 : ∀ h < 2, lanePt5 (Zmm.half b h z₂) = selEntry j (m h) := fun h hh => by
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
