module

public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Weierstrass.X86.Pow
public import VerifiedGarbage.Proof.Weierstrass.X86.MontCall
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Framework.X86.CallBody
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps

/-!
# ECDSA on x86 (32-bit): calls of internal functions on the working space

The fixed-base comb (`vg_<curve>_comb`, `Cfg.gMul`) and the windows
(`vg_<curve>_window`, `Cfg.ecdhMul`) are internal functions that take no
argument: their callers' working space stays in `edi`. A call of one runs
its body from the state the call instruction leaves (`State.callEntry`):
`esp` 4 bytes lower and the return address below the caller's `esp`, which
is apart from the working space when the 24 bytes of stack below `esp` are
apart from the writable regions (`callEntry_ws`). The body's own calls use
20 bytes of stack below that, which leave the return address where it was,
and its registers as its proof says (`WP.callWs`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

/-- `SpOk` with more stack. -/
theorem _root_.VG.Proof.Weierstrass.X86.SpOk.le {p : Prog isa} {n m : Nat} (h : SpOk p n) (hm : n ≤ m) :
    SpOk p m :=
  ⟨h.1, Nat.le_trans h.2 hm⟩

/-- The return address a call stores, apart from the stack its callee's
calls use. -/
theorem ret_below_disjoint {sp : BitVec 32} (h : 24 ≤ sp.toNat) :
    Region.Disjoint (below sp 4) (below (sp - BitVec.ofNat 32 4) 20) := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have hb := sp.isLt
  have e₁ : ((sp - BitVec.ofNat 32 4).setWidth 64).toNat = sp.toNat - 4 := by
    rw [BitVec.toNat_setWidth, X86.sub_toNat (by omega_using [h])]
    exact Nat.mod_eq_of_lt (by omega_using [hb])
  have e₂ : ((sp - BitVec.ofNat 32 4 - BitVec.ofNat 32 20).setWidth 64).toNat = sp.toNat - 24 := by
    have e : (sp - BitVec.ofNat 32 4).toNat = sp.toNat - 4 := X86.sub_toNat (by omega_using [h])
    rw [BitVec.toNat_setWidth, X86.sub_toNat (by omega_using [h, e]), e]
    exact Nat.mod_eq_of_lt (by omega_using [hb])
  rw [BitVec.toNat_sub, e₁] at h₁
  rw [BitVec.toNat_sub, e₂] at h₂
  have ha := a.isLt
  omega_using [h₁, h₂, h, hb, ha]

/-- The state a call leaves: the working space as its callee's code needs
it, with 20 bytes of stack below `esp`; memory changed only below the
caller's `esp`, so the working space and all below its byte 8192 as they
were. -/
theorem callEntry_ws {s : State} {base : Addr} (hs : Scr s base size)
    (hst : ∀ r ∈ s.wr, Region.Disjoint (below (s.gpr .esp) 24) r)
    (hsp24 : 24 ≤ (s.gpr .esp).toNat) :
    Scr s.callEntry base size ∧ 20 ≤ (s.callEntry.gpr .esp).toNat ∧
      Frame [below (s.gpr .esp) 4] s.mem s.callEntry.mem ∧
      Unch base [Mont.outW] s.mem s.callEntry.mem ∧
      Region.Sub (below (s.callEntry.gpr .esp) 20) (below (s.gpr .esp) 24) ∧
      Region.Sub (below (s.gpr .esp) 4) (below (s.gpr .esp) 24) := by
  have hn := hs.nowrap
  obtain e4 : (s.gpr .esp - 4 : BitVec 32) = s.gpr .esp - BitVec.ofNat 32 4 := rfl
  obtain hesp : (s.callEntry.gpr .esp).toNat = (s.gpr .esp).toNat - 4 := by
    rw [State.callEntry_esp, e4, X86.sub_toNat (by omega_using [hsp24])]
  obtain fr : Frame [below (s.gpr .esp) 4] s.mem s.callEntry.mem :=
    Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (by rw [e4]; exact below_top (k := 4) (Nat.le_refl _) (by omega_using [hsp24]) (Nat.le_refl _))
  obtain s4 : Region.Sub (below (s.gpr .esp) 4) (below (s.gpr .esp) 24) :=
    below_le_sub (by decide) hsp24
  obtain s20 : Region.Sub (below (s.callEntry.gpr .esp) 20) (below (s.gpr .esp) 24) := by
    rw [State.callEntry_esp, e4]; exact below_inner (by decide) hsp24
  obtain hws : Region.Disjoint (below (s.gpr .esp) 24) ⟨base, size⟩ := hst _ hs.wr
  obtain U₀ : Unch base [Mont.outW] s.mem s.callEntry.mem := fun x hx => fr x fun r hr hcx => by
    rw [List.mem_singleton.mp hr] at hcx
    have hx' := hx Mont.outW (List.mem_singleton_self _)
    have hlt : ofs base x < size := by
      have := (x - base).isLt
      have e : size = 8192 := rfl
      simp only [ofs] at hx' ⊢; omega_using [hx', this, e]
    exact hws x (s4 x hcx) (by simp only [Region.Contains]; simp only [ofs] at hlt; omega_using [hlt])
  refine ⟨⟨by rw [State.callEntry_gpr _ (by decide)]; exact hs.edi, hs.wr, hn,
      stkOk_of (z := 20) (Nat.le_refl _) (by omega_using [hesp, hsp24]) hn (by decide) (by
        have := hws.sub_left s20
        simp only [below] at this
        rwa [VG.X86.Taint.sub_setWidth (by omega_using [hesp, hsp24])] at this)⟩,
    by omega_using [hesp, hsp24], fr, U₀, s20, s4⟩

/-- A call of code that keeps the registers but `powClob` and uses 20 bytes
of stack: it returns, with `esp` where it was and the other registers as the
code leaves them, in the state `Q` takes. -/
theorem WP.callWs {name : String} {body : Prog isa} {s : State} {base : Addr} (hs : Scr s base size)
    (hst : ∀ r ∈ s.wr, Region.Disjoint (below (s.gpr .esp) 24) r)
    (hsp24 : 24 ≤ (s.gpr .esp).toNat) (hsp : SpOk body 20) {Q : State → Prop}
    (h : WP isa body s.callEntry fun u => Keeps powClob s.callEntry u ∧ Q (u.setReg .esp (s.gpr .esp))) :
    WP isa (.call name body) s fun s' => Keeps powClob s s' ∧ Q s' := by
  obtain ⟨-, h20, -, -, s20, s4⟩ := callEntry_ws hs hst hsp24
  obtain e4 : (s.gpr .esp - 4 : BitVec 32) = s.gpr .esp - BitVec.ofNat 32 4 := rfl
  refine WP.callBody (WP.mono (WP.withFrame hsp.1 hsp.2 h20 h) fun u ⟨⟨K, q⟩, fu⟩ => ?_)
  obtain huesp : u.gpr .esp = s.gpr .esp - 4 := by
    rw [K.1 .esp (by decide), State.callEntry_esp]
  refine ⟨huesp, ?_, ⟨fun r hr => ?_, by rw [RegUpd.rd_setReg, K.2.1]; rfl,
    by rw [RegUpd.wr_setReg, K.2.2]; rfl⟩, q⟩
  · -- The return address is where the call stored it.
    obtain hc4 : (below (s.gpr .esp) 4).Contains ((s.gpr .esp - 4).setWidth 64) (32 / 8) := by
      rw [e4]; exact below_top (k := 4) (Nat.le_refl _) (by omega_using [hsp24]) (by decide)
    obtain hd4 : ∀ r ∈ s.callEntry.wr ++ [below (s.callEntry.gpr .esp) 20],
        (below (s.gpr .esp) 4).Disjoint r := fun r hr => by
      rw [State.callEntry_wr] at hr
      rcases List.mem_append.mp hr with hr | hr
      · exact (hst r hr).sub_left s4
      · rw [List.mem_singleton.mp hr, State.callEntry_esp, e4]; exact ret_below_disjoint hsp24
    rw [fu.readW hc4 hd4 (by decide), State.callEntry_mem, Mem.readW_writeW_self32]
  · by_cases he : r = .esp
    · subst he; exact RegUpd.gpr_setReg_self _ _ _
    · rw [RegUpd.gpr_setReg_of_ne _ _ he, K.1 r hr, State.callEntry_gpr _ he]

end VG.Proof.Ecdsa.X86
