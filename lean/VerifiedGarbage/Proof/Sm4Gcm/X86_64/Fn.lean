module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Tag

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# SM4-GCM on x86-64: what every function does

Untrusted: everything here is checked by Lean. Each function saves and
restores our caller's registers as AES-GCM's do (`Proof/AesGcm/X86_64/Fn.lean`,
`save_ok`, `restore_ok`, `exit_ok`); the pieces of SM4-GCM's own never write
the slots they are saved in (`saved_tagFrame`, `saved_crFrame`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64
open VG.Proof.AesGcm.X86_64 (Lay savedR)

section
variable {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP)
include L

theorem saved_tagFrame {o : Nat} (ho : o = 0 ∨ o = 112) : ∀ r ∈ tagFrame St W SP o, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using (L.lay.st_w (a := 0) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.lay.w_w (.inr (by omega)) (by decide) (by omega)
  · exact L.lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.kw.sub_right (Lay.wSub (by decide))).symm

theorem saved_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW4 Ctx St W SP s D n) :
    ∀ r ∈ crFrame St SP D n, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.dw.ok.w.sub_right (Lay.wSub (by decide))).symm
  · exact (L.lay.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.kw.sub_right (Lay.wSub (by decide))).symm

end

/-- The stack `stkN` bytes below `SP` contains the 8 bytes below it. -/
theorem below8_stk (SP : Addr) : Region.Sub (below SP 8) (below SP stkN) := below_stk SP (d := 0) (by decide)

/-- The return address is above the stack the calls use. -/
theorem ret_stk (SP : Addr) : (⟨SP, 8⟩ : Region).Disjoint (below SP stkN) :=
  Offset.base_disjoint_below SP (n := stkN) (k := 8) (by decide)

/-- The layout, from disjointness of the context, the state, `W` and the
stack the calls use. -/
theorem Lay4.of {Ctx St W SP : Addr} (cw : Ctx.toNat + 256 ≤ 2 ^ 64) (sw : St.toNat + 80 ≤ 2 ^ 64)
    (ww : W.toNat + 2560 ≤ 2 ^ 64) (cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨St, 80⟩)
    (cW : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩) (sW : (⟨St, 80⟩ : Region).Disjoint ⟨W, 2560⟩)
    (sp : stkN ≤ SP.toNat) (kc : (below SP stkN).Disjoint ⟨Ctx, 256⟩) (ks : (below SP stkN).Disjoint ⟨St, 80⟩)
    (kw : (below SP stkN).Disjoint ⟨W, 2560⟩) : Lay4 Ctx St W SP :=
  ⟨VG.Proof.AesGcm.X86_64.Lay.of cw sw ww cs cW sW (kc.sub_left (below8_stk SP)) (ks.sub_left (below8_stk SP))
    (kw.sub_left (below8_stk SP)), sp, kc, ks, kw⟩

end VG.Proof.Sm4Gcm.X86_64
