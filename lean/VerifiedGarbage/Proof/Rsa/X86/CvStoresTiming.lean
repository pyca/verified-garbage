module

public import VerifiedGarbage.Proof.Rsa.X86.CvStoreTiming

/-! # All three masked CRT exports share a value-independent trace -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Rsa.X86.CrtValues
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Proof.Rsa.X86.Keys

def Ready (g : CallGeometry) (s : State) : Prop :=
  num s.mem g.base (2 * g.n) aZero = 0 ∧ ∃ accept : Bool, slot s.mem g.base sMask = if accept then 1 else 0

def ExportPair (g : CallGeometry) (s t : State) : Prop := Pair g s t ∧ Ready g s ∧ Ready g t

theorem store_relCT (g : CallGeometry) (i : Fin 3) (j : Nat) (hj : j < nArr) (nz : aZero ≠ j) :
    RelCT isa (ExportPair g) (store g.n (2 * i.val) j) (ExportPair g) := by
  intro s t tr ur sf tf ⟨h, ⟨zs, cs, ms⟩, ⟨zt, ct, mt⟩⟩ es et
  have eq := (store_trace g i j hj _ _ _ _ _ _
    ⟨h, by rw [ms]; cases cs <;> decide, by rw [mt]; cases ct <;> decide⟩ es et).1
  obtain ⟨hs, _, _, headers, others, ks⟩ := wp_result (store_ok h.left i hj zs cs ms) es
  obtain ⟨ht, _, _, headert, othert, kt⟩ := wp_result (store_ok h.right i hj zt ct mt) et
  refine ⟨eq, h.after hs ht ks kt (by decide), ?_, ?_⟩
  · exact ⟨(others _ (by decide) nz).trans zs, cs, (headers _ (by decide)).trans ms⟩
  · exact ⟨(othert _ (by decide) nz).trans zt, ct, (headert _ (by decide)).trans mt⟩

theorem status_relCT (g : CallGeometry) :
    RelCT isa (ExportPair g) (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sMask))])
      (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (workspaceTaint false) (fun _ _ h => h.1.workspace) (hc := .block [])
  rfl

theorem stores_relCT (g : CallGeometry) : RelCT isa (ExportPair g) (stores g.n) (fun _ _ => True) :=
  VG.RelCT.seq (store_relCT g 0 aDR2 (by decide) (by decide))
    (VG.RelCT.seq (store_relCT g 1 aDR3 (by decide) (by decide))
      (VG.RelCT.seq (store_relCT g 2 3 (by decide) (by decide)) (status_relCT g)))

end VG.Proof.Rsa.X86.CrtValues
