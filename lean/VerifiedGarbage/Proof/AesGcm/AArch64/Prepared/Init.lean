module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Prepared.Powers
public import VerifiedGarbage.Proof.AesGcm.AArch64.Init
public import VerifiedGarbage.Spec.Gcm.Prepared
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM on AArch64: `vg_aes_gcm_init_prepared`

Untrusted: everything here is checked by Lean. The key context of
`vg_aes_gcm_init` (`initWith_wp`, with a context of 1024 bytes), then the
48 prepared powers (`powers_ok`), which write only bytes 256 to 1023 of it
(`initPrepared_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull (PrepPow pp)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt KeyRepr ctxH PreparedPowersRepr)

/-- `vg_aes_gcm_init_prepared(key = x0, key_len = x1, ctx = x2, scratch = x3)`. -/
def initPreparedAArch64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let ctx : Region := ⟨s.gpr .x2, 1024⟩
    let scr : Region := ⟨s.gpr .x3, 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (s.gpr .x2).toNat + 1024 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + 2560 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 16 ∨ (s.gpr .x1).toNat = 24 ∨ (s.gpr .x1).toNat = 32)
  post s s' := KeyRepr s'.mem (s.gpr .x2) (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) ∧
    PreparedPowersRepr s'.mem (s.gpr .x2)
  pub := initAArch64.pub

namespace Prepared

open VG.Proof.AesGcm.AArch64.Prepared (Slots Inv slot slotPow ifp ifn)

/-- The slots, as `Spec.Gcm.PreparedPowersRepr` reads them. -/
theorem repr_of_slots {H : Block} {Ctx : Addr} {m : Mem} (hs : Slots H Ctx m 48) (hH : ctxH m Ctx = H) :
    PreparedPowersRepr m Ctx := by
  intro k hk
  have e : ∀ j < 48, m.readW (slot Ctx j) 128 = pp H (slotPow j) := fun j hj => by
    rw [Mem.readW, show 128 / 8 = 16 from rfl, hs j hj (.inl hj)]; rfl
  rw [hH]
  refine ⟨?_, ?_⟩
  · have := e (2 * k) (by omega)
    rw [slot, show 256 + 16 * (2 * k) = 256 + 32 * k by omega, slotPow, ifp (by omega)] at this
    exact this
  · have := e (2 * k + 1) (by omega)
    rw [slot, show 256 + 16 * (2 * k + 1) = 272 + 32 * k by omega, slotPow, ifn (by omega)] at this
    exact this

/-- `KeyRepr` reads only the first 256 bytes of the context. -/
theorem keyRepr_frame {Ctx : Addr} {m m' : Mem} {key : List Byte}
    (hk : KeyRepr m Ctx key) (hf : Frame [⟨Ctx + BitVec.ofNat 64 256, 768⟩] m m')
    (hL : key.length = 16 ∨ key.length = 24 ∨ key.length = 32) : KeyRepr m' Ctx key := by
  have hR : 16 * (Spec.Aes.rounds (key.length / 4) + 1) ≤ 240 := by
    rcases hL with h | h | h <;> rw [h] <;> decide
  refine ⟨?_, ?_⟩
  · rw [bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base Ctx (by omega) (by decide)).symm) (by omega)]
    exact hk.1
  · show blockAt m' (Ctx + BitVec.ofNat 64 240) = _
    rw [blockAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint Ctx (.inl (by decide)) (by decide) (by decide))]
    exact hk.2

end Prepared

/-- `vg_aes_gcm_init_prepared`. -/
theorem initPrepared_wp (v : GcmImpl) (hP : PrepPow) {s : State} (hp : initPreparedAArch64.pre s) :
    WP isa (Impl.AesGcm.AArch64.Prepared.init v.callees) s fun s' =>
      GprAbi s s' ∧ initPreparedAArch64.post s s' := by
  simp only [initPreparedAArch64] at hp ⊢
  obtain ⟨hrd, hwr, d_kc, d_ks, d_cs, wc, ws, hL⟩ := hp
  refine initWith_wp v _ (by decide) rfl rfl rfl rfl hrd hwr d_kc d_ks d_cs (by omega) hL
    fun s₅ c19 c21 csp crd cwr hsv hk => ?_
  have pW : Covers [⟨s.gpr .x3, 2560⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have pC : Covers [⟨s.gpr .x2, 1024⟩] s₅.wr := by rw [cwr, hwr]; exact covers_of_mem (by simp)
  refine WP.seq (WP.mono (Prepared.powers_ok hP c21 rfl pC) fun s₆ hI => ?_)
  have hf : Frame [⟨s.gpr .x2 + BitVec.ofNat 64 256, 768⟩] s₅.mem s₆.mem := hI.frame
  have hsv₆ : SavedAt s₆.mem (s.gpr .x3) s := hsv.frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((d_cs.sub_left (Offset.sub_base _ (by decide))).sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (exit_ok (by rw [hI.gpr .x19 (by decide), c19]) (by rw [hI.sp, csp])
    (by rw [hI.rd, hI.wr, crd, cwr]; exact covers_left pW) hsv₆) fun s' ⟨hg, hm, _⟩ => ⟨hg, ?_, ?_⟩
  · rw [hm]
    exact Prepared.keyRepr_frame hk hf (by rw [length_bytesAt]; exact hL)
  · rw [hm]
    refine Prepared.repr_of_slots hI.slots ?_
    show blockAt s₆.mem (s.gpr .x2 + BitVec.ofNat 64 240) = blockAt s₅.mem (s.gpr .x2 + BitVec.ofNat 64 240)
    exact blockAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))

end VG.Proof.AesGcm.AArch64
