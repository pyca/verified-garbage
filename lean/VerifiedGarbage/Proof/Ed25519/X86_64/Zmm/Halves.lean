import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Entry
import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Select

/-!
# The `zmm` comb: what the `ymm` lemmas say of the halves

A `ymm` state related to half `h` of a `zmm` state (`Rel`) agrees with the
half itself on the registers outside the junk and on the memory below the
rows of the window: its lanes, its point (`lanePt`), the bounds of its limbs
(`Small`) and its constants (`EConsts`) are the half's. `sim_wp2` runs two
translated blocks, the second from the junk of the first.
-/

namespace VG.Proof.Ed25519.X86_64.Zmm

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Zmm VG.Proof.Ed25519.X86_64.Ifma
open VG.Impl.X25519.X86_64.Ifma (KM K19 KB0 KB1)
open VG.Impl.Ed25519.X86_64.Ifma (EK13 EK26 EK39)
open VG.Proof.X25519.X86_64.Ifma (lanes fe5 fe5_congr mq)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw)

theorem _root_.VG.Proof.Ed25519.X86_64.Ifma.EConsts.of_mq {m m' : Mem} {base : Addr} (hk : EConsts m base)
    (w : ∀ d, 1344 ≤ d → d + 8 ≤ 4096 → mq m' base d = mq m base d) : EConsts m' base := by
  refine ⟨⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩, fun l hl => ?_,
    fun l hl => ?_, fun l hl => ?_⟩
  · rw [w _ (by simp only [KM]; omega) (by simp only [KM]; omega)]; exact hk.km l hl
  · rw [w _ (by simp only [K19]; omega) (by simp only [K19]; omega)]; exact hk.k19 l hl
  · rw [w _ (by simp only [KB0]; omega) (by simp only [KB0]; omega)]; exact hk.kb0 l hl
  · rw [w _ (by simp only [KB1]; omega) (by simp only [KB1]; omega)]; exact hk.kb1 l hl
  · rw [w _ (by simp only [EK13]; omega) (by simp only [EK13]; omega)]; exact hk.k13 l hl
  · rw [w _ (by simp only [EK26]; omega) (by simp only [EK26]; omega)]; exact hk.k26 l hl
  · rw [w _ (by simp only [EK39]; omega) (by simp only [EK39]; omega)]; exact hk.k39 l hl

/-! ## Registers -/

theorem qw_half (b : Addr) {h : Nat} (z : State) (r : XReg) {k : Nat} (hk : k < 4) :
    qw (Zmm.half b h z) r k = zq z r h k := by
  simp only [qw, zq, half, State.lane]
  rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;> rfl

theorem Rel.qw_eq {b : Addr} {h : Nat} {J : List Nat} {z y : State} (hr : Rel b h J z y) {r : XReg}
    (hj : xi r ∉ J) {k : Nat} (hk : k < 4) : qw y r k = qw (Zmm.half b h z) r k := by
  rw [qw_half b z r hk]
  simp only [qw, zq]
  rw [hr.lane hj (show k / 2 < 2 by omega)]

theorem Rel.lanes_eq {b : Addr} {h : Nat} {J : List Nat} {z y : State} (hr : Rel b h J z y) {r : Nat}
    (hr16 : r + 5 ≤ 16) (hj : ∀ q, r ≤ q → q < r + 5 → q ∉ J) :
    ∀ l < 4, ∀ i < 5, lanes y r l i = lanes (Zmm.half b h z) r l i := fun l hl i hi => by
  simp only [lanes]
  rw [hr.qw_eq (by rw [VG.Proof.X25519.X86_64.Ifma.xi_xr _ (by omega)]; exact hj _ (by omega) (by omega)) hl]

theorem Rel.lanePt_eq {b : Addr} {h : Nat} {J : List Nat} {z y : State} (hr : Rel b h J z y)
    (hj : ∀ q < 5, q ∉ J) : lanePt y = lanePt (Zmm.half b h z) := by
  have e := hr.lanes_eq (r := 0) (by decide) fun q _ hq => hj q hq
  simp only [lanePt]
  rw [fe5_congr (e 0 (by decide)), fe5_congr (e 1 (by decide)), fe5_congr (e 2 (by decide)),
    fe5_congr (e 3 (by decide))]

theorem Rel.small {b : Addr} {h : Nat} {J : List Nat} {z y : State} (hr : Rel b h J z y)
    (hj : ∀ q < 5, q ∉ J) (hs : Small y) : Small (Zmm.half b h z) := fun l hl i hi => by
  rw [← hr.lanes_eq (r := 0) (by decide) (fun q _ hq => hj q hq) l hl i hi]; exact hs l hl i hi

/-! ## Memory -/

theorem Rel.mq_eq {b : Addr} {h : Nat} {J : List Nat} {z y : State} (hr : Rel b h J z y) {d : Nat}
    (hd : d + 8 ≤ 4096) : mq y.mem b d = mq (Zmm.half b h z).mem b d := by
  simp only [mq]
  refine Mem.readW_congr fun i hi => ?_
  rw [Offset.add_ofNat_add_ofNat]
  exact hr.mem _ (by rw [off_ofNat _ (by omega)]; unfold InZ ZB; omega)

theorem Rel.econsts {b : Addr} {h : Nat} {J : List Nat} {z y : State} (hr : Rel b h J z y)
    (hk : EConsts y.mem b) : EConsts (Zmm.half b h z).mem b :=
  hk.of_mq fun _ _ hd => (hr.mq_eq hd).symm

theorem half_econsts {b : Addr} {h : Nat} {J : List Nat} {z y : State} (hr : Rel b h J z y)
    {s : State} (hk : EConsts s.mem b) (ho : VG.Proof.X25519.X86_64.Outside b 1024 320 s.mem y.mem) :
    EConsts (Zmm.half b h z).mem b :=
  hr.econsts (hk.outside ho)

/-! ## Two blocks -/

/-- Two translated blocks, the second from the junk the first leaves. -/
theorem sim_wp2 {b : Addr} {t₁ t₂ : Nat} {is₁ is₂ : List Instr} {J₁ J₂ : List Nat}
    (hj₁ : junk t₁ [] is₁ = some J₁) (hj₂ : junk t₂ J₁ is₂ = some J₂) {z : State} (hz : ZOK b z)
    {Q : Nat → State → Prop} (hy : ∀ h < 2, WP isa (.block (is₁ ++ is₂)) (Zmm.half b h z) (Q h)) :
    WP isa (.block (tzs t₁ is₁ ++ tzs t₂ is₂)) z fun z' => ZOK b z' ∧ ZKeep b z z' ∧
      ∀ h < 2, ∃ y, Rel b h J₂ z' y ∧ Q h y := by
  rw [WP.block_append_iff]
  refine WP.mono (sim_wp (Q := fun h y => WP isa (.block is₂) y (Q h)) hj₁ hz
    fun h hh => WP.block_append_iff.1 (hy h hh)) fun z₁ ⟨o₁, k₁, r₁⟩ => ?_
  exact WP.mono (sim_run is₂ hj₂ o₁ r₁) fun z' ⟨o, k, r⟩ => ⟨o, k₁.trans k, r⟩

end VG.Proof.Ed25519.X86_64.Zmm
