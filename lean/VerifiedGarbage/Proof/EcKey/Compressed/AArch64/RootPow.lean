module

public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Chain
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps

/-! # Root exponentiation reuses the existing field multiplication backend -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Ecdsa.AArch64
open VG.Impl.EcKey.Compressed.AArch64
open VG.Impl.Ecdh.AArch64 (W2)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

 def rootSlots : List Nat := [ACC, TMP, RX, RY, RZ, DX, DY, DZ, TX, TY, TZ]
 def rootWrites (c : Cfg) : List (Nat × Nat) :=
  [(c.sl ACC, 8 * c.n), (c.sl RX, 9 * (8 * c.n)), (c.sl TMP, 8 * c.n)]

 theorem rootTable_end (c : Cfg) : c.sl RX + 9 * (8 * c.n) = c.sl T0 := by
  rw [sl_eq c RX (by decide), sl_eq c T0 (by decide)]
  simp only [RX, T0]
  omega

 theorem fixedOk_rootWrites {c : Cfg} (_hc : BaseCfgOk c) : FixedOk c (rootWrites c) := by
  intro w hw
  simp only [rootWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (by decide : 12 < ACC)))
  · exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (by decide : 12 < RX)))
  · exact (fixedOk_slW (c := c) (l := [TMP]) (by decide)) _ (by simp [slW])

 theorem apart_rootWrites {c : Cfg} (_hc : BaseCfgOk c) {i : Nat} (_hi : i < 45)
    (hw : i ∉ rootSlots) :
    ∀ w ∈ rootWrites c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  have ha : i ≠ ACC := fun h => hw (h ▸ (by simp [rootSlots]))
  have ht : i ≠ TMP := fun h => hw (h ▸ (by simp [rootSlots]))
  have htable : i < RX ∨ T0 ≤ i := by
    simp only [rootSlots, ACC, TMP, RX, RY, RZ, DX, DY, DZ, TX, TY, TZ,
      List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
    change i < 14 ∨ 23 ≤ i
    omega
  intro w h
  simp only [rootWrites, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact sl_apart c ha
  · rw [rootTable_end]
    rcases htable with h | h
    · exact .inl (sl_lt c h ht (by decide))
    · exact .inr (by
        rw [sl_eq c T0 (by decide), sl_eq c i ht]
        have := Nat.mul_le_mul_left (8 * c.n) h
        omega)
  · exact sl_apart c ht (.inl ht) (.inr (by omega))

 theorem rootChain_lay {c : Cfg} (hc : BaseCfgOk c) (e : Nat) :
    ChainLay (rootChain c e) size := by
  change ChainLay (ChainCfg.ofExp c.MP' (c.sl ACC) (c.sl W2) (c.sl RX) e) size
  dsimp only [ChainCfg.ofExp]
  refine ⟨hc.n0, sl_le c hc.n10 (i := ACC) (by decide), sl_le c hc.n10 (i := W2) (by decide), ?_,
    sl_mod8 c ACC, sl_mod8 c W2, sl_mod8 c RX, MP'_A c, sl_apart c (i := ACC) (j := W2) (by decide),
    ?_, ?_, sl_apart c (i := ACC) (j := TMP) (by decide), sl_apart c (i := W2) (j := TMP) (by decide),
    ?_, ?_, sl_apart c (i := W2) (j := MP) (by decide)⟩
  · change c.sl RX + 9 * (8 * c.n) ≤ size
    rw [rootTable_end]; have := sl_le c hc.n10 (i := T0) (by decide); omega
  · exact .inr (by change c.sl RX + 9 * (8 * c.n) ≤ c.sl ACC; rw [rootTable_end]; exact Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (by decide : T0 < ACC)))
  · exact .inr (by change c.sl RX + 9 * (8 * c.n) ≤ c.sl W2; rw [rootTable_end]; exact Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (by decide : T0 < W2)))
  · change c.sl RX + 9 * (8 * c.n) ≤ c.sl TMP ∨ c.sl TMP + 8 * c.n ≤ c.sl RX
    rw [rootTable_end]
    by_cases hh : c.n = 6 ∨ c.n = 8 ∨ c.n = 9
    · rw [sl_tmp c hh]
      left
      rw [sl_eq c T0 (by decide)]
      simp only [T0, VG.Impl.Weierstrass.AArch64.Mont.moAt]
      have := hc.n10; omega
    · have ht : c.sl TMP = 64 + 8 * c.n * TMP := by
        unfold Cfg.sl
        rw [ite_eq_right (fun h => hh h.2)]
        rfl
      rw [ht]
      right
      rw [sl_eq c RX (by decide)]
      simp only [TMP, RX]; omega
  · intro w hw
    change w ∈ [(c.sl ACC, 8 * c.n), (c.sl RX, 9 * (8 * c.n)), (c.sl TMP, 8 * c.n)] at hw
    exact apart_rootWrites hc (i := MP) (by decide) (by decide) w hw

 theorem rootChain_backend {c : Cfg} (hc : BaseCfgOk c) (e : Nat) : Chain.Backend (rootChain c e) := by
  refine ⟨fun f m h => (hc.call_p f m h).2, .inr ⟨?_, ?_, ?_⟩⟩
  · exact sl_own_fn c hc.n10 (i := ACC) (by decide) (by decide)
  · exact sl_own_fn c hc.n10 (i := W2) (by decide) (by decide)
  · change c.sl RX + 9 * (8 * c.n) ≤ VG.Proof.Weierstrass.AArch64.Mont.own c.n
    rw [rootTable_end]
    exact Nat.le_trans (Nat.le_add_right _ _) (sl_own_fn c hc.n10 (i := T0) (by decide) (by decide))

 theorem rootPower_ok {c : Cfg} (hc : BaseCfgOk c) {e : Nat}
    (hchain : ChainOk (rootChain c e) e) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hB : sv c base s W2 < c.C.p) :
    WP isa (rootPower c e) s fun t => KeepRegs (powClob c.n) s t ∧
      Unch base (rootWrites c) s.mem t.mem ∧ sv c base t ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ e :=
  Chain.chainPow_ok (rootChain_lay hc e) (rootChain_backend hc e)
    (unitMod_pow_two hc.p_odd _) hs hM hB hchain

end VG.Proof.EcKey.Compressed.AArch64
