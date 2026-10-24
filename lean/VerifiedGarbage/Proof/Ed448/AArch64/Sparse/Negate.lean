module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.SubAlias
import VerifiedGarbage.Proof.Framework.Block

/-! Negation of a selected public entry, using the proven in-place difference. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Impl.Ed448.AArch64.Sparse
open VG.Proof.X448.AArch64 (Scr)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same)
open VG.Proof.Curve448.AArch64.Fast (Mb)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem negateSelected_ok {s:State} {base:Addr} (hs:Scr s base) (hb:BEnv s.mem base)
    (hz:Bnd Mb s.mem base (slot 19)) (hx:Bnd Mb s.mem base (slot 6)) :
    WP isa negateSelected s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [6] s.mem t.mem ∧
      EV t.mem base=Function.update (EV s.mem base) 6 (EV s.mem base 19-EV s.mem base 6) := by
  unfold negateSelected VG.Impl.X448.AArch64.Fast.opsK VG.Impl.X448.AArch64.Fast.Op.progK
  refine WP.seq (WP.mono (subAliasE hs hb 6 19 6 hz hx)
    fun t ⟨tk,tb,ts,te⟩ => WP.block_nil ⟨tk,tb,ts,te⟩)

end VG.Proof.Ed448.AArch64.Sparse
