module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Base
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Framework.Mem

/-! # One operation of the batched inverse, in both runs

`relOp`: an operation that the analysis checks from `τS` and that writes only some ranges of the
working space, none of them the batch count, keeps both runs in `Both`: the context, the call's
public data, a fact `C` about the batch count, and facts about the registers that the operation keeps (`Stable`). It
may need some more (`H`, such as a mask in `ecx`) and give others (`X`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.Time

open VG VG.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.InvBatchRt
open VG.Proof.Weierstrass (Unch)

/-- Both runs from `Pre`, with `C` of the batch count and the register facts `G`. -/
def Both (L : Lay) (B : Addr) (Z len N : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (C : Nat → Prop)
    (G : (Reg → BitVec 32) → Prop) (s t : State) : Prop :=
  Pre L B Z len N args sp (fun g m => C (w32 m B 100) ∧ G g) s ∧
    Pre L B Z len N args sp (fun g m => C (w32 m B 100) ∧ G g) t

/-- Register facts that code writing at most `rs` keeps. -/
def Stable (rs : List Reg) (G : (Reg → BitVec 32) → Prop) : Prop :=
  ∀ g g' : Reg → BitVec 32, (∀ r, r ∉ rs → g' r = g r) → G g → G g'

theorem stable_true (rs : List Reg) : Stable rs fun _ => True := fun _ _ _ h => h

theorem unch_w32 {B : Addr} {ws : List (Nat × Nat)} {m m' : Mem} (h : Unch B ws m m') {d : Nat}
    (hd : ∀ w ∈ ws, d + 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) (hd' : d + 4 ≤ 2 ^ 64) : w32 m' B d = w32 m B d :=
  congrArg BitVec.toNat (Mem.readW_congr fun i hi => h _ fun w hw => by
    rw [ofs_off B (by omega)]; have := hd w hw; omega)

variable {L : Lay} {B : Addr} {Z len N : Nat} {args : Nat → BitVec 32} {sp : BitVec 32}

theorem relOp {c : Prog isa} {rs : List Reg} {ws : List (Nat × Nat)} {C : Nat → Prop}
    {G H X : (Reg → BitVec 32) → Prop} (hL : L.ws = 14) (hesp : Reg.esp ∉ rs) (hG : Stable rs G)
    (hws : ∀ w ∈ ws, (104 ≤ w.1 ∨ w.1 + w.2 ≤ 100) ∧ w.1 + w.2 ≤ Z)
    (hf : ∀ s, Bx L s B Z len N → H s.gpr → WP isa c s fun t =>
      Bx L t B Z len N ∧ Keeps rs s t ∧ Unch B ws s.mem t.mem ∧ X t.gpr)
    {hc : VG.Taint.Hint VG.X86.Taint.T} (h : (VG.Taint.check sseTaint τS c hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ H g) c (Both L B Z len N args sp C fun g => G g ∧ X g) :=
  leafU hL (fun s ps => WP.mono (hf s ps.1 ps.2.2.2.2) fun t ⟨hb, K, U, hx⟩ =>
    ⟨hb, ps.2.1.keep K hesp (U.outside fun w hw => ⟨Nat.zero_le _, by rw [Nat.zero_add]; exact (hws w hw).2⟩),
      by rw [unch_w32 U (fun w hw => (hws w hw).1) (by decide)]; exact ps.2.2.1, hG _ _ K.1 ps.2.2.2.1, hx⟩) h

end VG.Proof.Rsa.X86.InvBatchRt.Time
