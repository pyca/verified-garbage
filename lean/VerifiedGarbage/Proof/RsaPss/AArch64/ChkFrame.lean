module

public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkPre
public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Proof.RsaPss.AArch64.Basic
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Offset

/-!
# EMSA-PSS's check of an encoding on AArch64: the prologue

`prologue_ok`: the callee-saved registers and the arguments in their slots
of the frame (`FrC`; `any_salt_len`'s 32 bits in `sAny`), `scratch` in
`x20`, `x19` and `x21` set, `emLen` in `x23`, the mask `0xFF >>> z` in `sC`
and `lo = 0` in `sLo` (`AtC`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Chk

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_addImm)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_mov wp_movw)
open VG.Proof.RsaPss.AArch64 (off maskBits_ok)
open VG.Proof.RsaPss.AArch64.Sgn (fb in_frame wr_frame)

/-- The argument registers kept in slots of the frame. -/
def chkSlots : List (Reg × Nat) := [(.x0, sDig), (.x4, sSaltLen), (.x5, sAny)]

theorem fits : Spill.Fits (saved ++ chkSlots) := by decide

/-- `any_salt_len`'s 32 bits. -/
abbrev anyC (s : State) : BitVec 64 := ((s.gpr .x5).setWidth 32).setWidth 64

/-- `z = 8 emLen - emBits`, and the mask of `maskedDB`'s top bits. -/
abbrev zC (s : State) : Nat := 8 * (s.gpr .x2).toNat - (s.gpr .x3).toNat
abbrev cC (s : State) : Byte := (0xFF : Byte) >>> zC s

/-- The frame's slots that the code reads: the saved registers, the
arguments. -/
structure FrC (s : State) (m : Mem) : Prop where
  sv : Spill.Saved (fb s) s.gpr saved m
  dig : m.readW (fb s + BitVec.ofNat 64 sDig) 64 = s.gpr .x0
  sl : m.readW (fb s + BitVec.ofNat 64 sSaltLen) 64 = s.gpr .x4
  any : m.readW (fb s + BitVec.ofNat 64 sAny) 64 = anyC s

/-- The slots of `FrC`: `[96, 248)` and `[264, 272)` of the frame. -/
abbrev frA (s : State) : Region := ⟨fb s + BitVec.ofNat 64 96, 152⟩
abbrev frB (s : State) : Region := ⟨fb s + BitVec.ofNat 64 264, 8⟩

theorem FrC.frame {s : State} {m m' : Mem} (h : FrC s m) {rs : List Region} (hf : Frame rs m m')
    (hA : ∀ r ∈ rs, (frA s).Disjoint r) (hB : ∀ r ∈ rs, (frB s).Disjoint r) : FrC s m' := by
  have hw : ∀ {d : Nat}, (96 ≤ d ∧ d + 8 ≤ 248) → m'.readW (fb s + BitVec.ofNat 64 d) 64 =
      m.readW (fb s + BitVec.ofNat 64 d) 64 := fun hd =>
    hf.readW (r := ⟨fb s + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hA r hr).sub_left (Offset.sub _ hd.1 (by omega))) (by decide)
  refine ⟨h.sv.frame_in (lo := 96) (n := 152) (by decide) hf hA, by rw [hw (by decide)]; exact h.dig,
    by rw [hw (by decide)]; exact h.sl, ?_⟩
  rw [hf.readW (r := ⟨fb s + BitVec.ofNat 64 sAny, 8⟩) (Region.contains_self _ _)
    (fun r hr => (hB r hr).sub_left (Offset.sub _ (by decide) (by decide))) (by decide)]
  exact h.any

/-- After the prologue. -/
structure AtC (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x19 : u.gpr .x19 = off (s.gpr .x6) oSt
  x20 : u.gpr .x20 = s.gpr .x6
  x21 : u.gpr .x21 = off (s.gpr .x6) oDig
  x23 : u.gpr .x23 = s.gpr .x2
  x1 : u.gpr .x1 = s.gpr .x1
  v : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [⟨fb s, frameBytes⟩, ⟨s.gpr .x6, oRsa⟩] s.mem u.mem
  fr : FrC s u.mem
  lo : u.mem.readW (fb s + BitVec.ofNat 64 sLo) 64 = BitVec.ofNat 64 0
  c : u.mem.readW (fb s + BitVec.ofNat 64 sC) 64 = BitVec.setWidth 64 (cC s)

theorem prologue_ok {D : Nat} {s u : State} (hp : PreC D s) (hsp : u.sp = fb s) (hrd : u.rd = s.rd)
    (hwr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hm : u.mem = s.mem) (hg : ∀ r, u.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) :
    WP isa (.block chkPrologue) u (AtC s) := by
  unfold chkPrologue save regsUp
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  refine wp_movw fun u₀ o₀ e₀ => wp_addSp (by decide) fun u₁ o₁ e₁ => ?_
  rw [o₀.sp, hsp, BitVec.add_zero] at e₁
  have hin : ∀ p ∈ saved ++ chkSlots, InRegions u₁.wr (u₁.gpr .x16 + BitVec.ofNat 64 p.2) 8 := fun p hp' => by
    rw [e₁, o₁.wr, o₀.wr]
    exact wr_frame hwr (by revert p; decide)
  refine Spill.save_ok (b := .x16) (l := saved ++ chkSlots) fits.1 hin ?_
  generalize hm₂ : Spill.saveMem u₁.mem (u₁.gpr .x16) u₁.gpr (saved ++ chkSlots) = m₂
  have gs : ∀ r, r ≠ .x16 → r ≠ .x5 → u₁.gpr r = s.gpr r := fun r h h' => by
    rw [o₁.gpr r (by simpa using h), o₀.gpr r (by simpa using h'), hg]
  have g5 : u₁.gpr .x5 = anyC s := by rw [o₁.get .x5, e₀, hg]
  have fr₂ : Frame [⟨fb s, frameBytes⟩] s.mem m₂ := by
    rw [← hm₂, e₁, o₁.mem, o₀.mem, hm]
    exact Spill.saveMem_frame_base (fun p hp' => by revert p; decide) (by decide) _ _ _
  have sv₂ : Spill.Saved (fb s) u₁.gpr (saved ++ chkSlots) m₂ := by
    rw [← hm₂, e₁]; exact Spill.saveMem_saved fits _ _ _
  refine wp_mov fun u₃ o₃ e₃ => wp_mov fun u₄ o₄ e₄ => wp_addImm (by decide) fun u₅ o₅ e₅ =>
    wp_addImm (by decide) fun u₆ o₆ e₆ => ?_
  have O₆ : Only [.x23, .x20, .x19, .x21] { u₁ with mem := m₂ } u₆ := (o₃.trans (o₄.trans (o₅.trans o₆))).mono
  have sp₆ : u₆.sp = fb s := by rw [O₆.sp]; show u₁.sp = _; rw [o₁.sp, o₀.sp, hsp]
  have wr₆ : u₆.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [O₆.wr]; show u₁.wr = _; rw [o₁.wr, o₀.wr, hwr]
  have x20₆ : u₆.gpr .x20 = s.gpr .x6 := by
    rw [o₆.get .x20, o₅.get .x20, e₄, o₃.get .x6]; exact gs .x6 (by decide) (by decide)
  have x23₆ : u₆.gpr .x23 = s.gpr .x2 := by
    rw [o₆.get .x23, o₅.get .x23, o₄.get .x23, e₃]; exact gs .x2 (by decide) (by decide)
  have x3₆ : u₆.gpr .x3 = s.gpr .x3 := by rw [O₆.get .x3]; exact gs .x3 (by decide) (by decide)
  have hk2 := hp.k2
  have hz := hp.z
  refine WP.mono (maskBits_ok (F := fb s) sp₆ (by rw [wr₆]; exact in_frame s _ (by decide))
    (by rw [wr₆]; exact in_frame s _ (by decide)) (r := .x3) (by decide) (k := (s.gpr .x2).toNat)
    (eb := (s.gpr .x3).toNat) (by rw [x23₆, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by rw [x3₆, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hz.1 hz.2 (by omega)) fun u₇ ⟨K, hm₇⟩ => ?_
  have hm₇' : u₇.mem = (m₂.writeW (fb s + BitVec.ofNat 64 sC) (BitVec.setWidth 64 (cC s))).writeW
      (fb s + BitVec.ofNat 64 sLo) (0 : BitVec 64) := by rw [hm₇, O₆.mem]
  have W2 : Frame [⟨fb s + BitVec.ofNat 64 sC, 8⟩, ⟨fb s + BitVec.ofNat 64 sLo, 8⟩] m₂ u₇.mem := by
    rw [hm₇']
    exact ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW (by simp) _
      (Region.contains_self _ _)
  have sv₇ := sv₂.frame W2 fun p hp' r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      exact Offset.disjoint _ (by revert p; decide) (by revert p; decide) (by decide)
  exact {
    sp := K.sp.trans sp₆
    rd := by rw [K.rd, O₆.rd]; show u₁.rd = _; rw [o₁.rd, o₀.rd, hrd]
    wr := K.wr.trans wr₆
    x19 := by rw [K.get .x19, o₆.get .x19, e₅, e₄, o₃.get .x6, gs .x6 (by decide) (by decide)]
    x20 := by rw [K.get .x20, x20₆]
    x21 := by rw [K.get .x21, e₆, o₅.get .x20, e₄, o₃.get .x6, gs .x6 (by decide) (by decide)]
    x23 := by rw [K.get .x23, x23₆]
    x1 := by rw [K.get .x1, O₆.get .x1]; exact gs .x1 (by decide) (by decide)
    v := fun r hr => by
      rw [K.vcs r hr, O₆.vcs r hr]
      show (u₁.v r).extractLsb' 0 64 = _
      rw [o₁.vcs r hr, o₀.vcs r hr, hv r hr]
    mem := by
      rw [hm₇']
      exact ((fr₂.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).mono (by simp)
    fr := {
      sv := fun p hp' => by
        rw [sv₇ p (List.mem_append_left _ hp')]
        exact gs p.1 (by revert p; decide) (by revert p; decide)
      dig := by rw [sv₇ (.x0, sDig) (by simp [chkSlots])]; exact gs .x0 (by decide) (by decide)
      sl := by rw [sv₇ (.x4, sSaltLen) (by simp [chkSlots])]; exact gs .x4 (by decide) (by decide)
      any := by rw [sv₇ (.x5, sAny) (by simp [chkSlots])]; exact g5 }
    lo := by rw [hm₇', Mem.readW_writeW_self64]; rfl
    c := by
      rw [hm₇', Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64] }

end VG.Proof.RsaPss.AArch64.Chk
