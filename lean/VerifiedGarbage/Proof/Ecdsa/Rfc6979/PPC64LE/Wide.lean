module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.BytesLen
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Entry
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Copy

/-!
# Deterministic ECDSA on PPC64LE: scalars longer than the hash

For P-521 (`big`, whose 66-byte scalars are longer than every hash
function's output): the `Q` bytes at an offset in the frame above its
pointers, shifted right in place through the words at `scratch + 2560`
(`conv_ok`, by `loadBytes_ok`, `shrWords_ok` and `storeBytes_ok`, with
`scratch` in `r3`), as `core`'s digest (`prepC`) and the candidate
(`candTop`) need.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont (wordsVal Outside off ofs)
open VG.Proof.Mont.PPC64LE (Kp Ws)
open VG.Proof.Weierstrass.PPC64LE (loadBytes_ok shrWords_ok storeBytes_ok)
open VG.Proof.Hmac.Common (bytesAt_add)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

theorem frame_of_outside {base : Addr} {d n : Nat} {m m' : Mem} (h : Outside base d n m m')
    (hn : d + n ≤ 2 ^ 64) : Frame [⟨base + BitVec.ofNat 64 d, n⟩] m m' := fun x hx => h x (by
  have h₁ := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at h₁
  have h₂ := Offset.lt_iff x base hn
  simp only [ofs]
  omega_arith)

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-- The registers that the code here writes, none of them callee-saved. -/
abbrev wideRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

theorem wideRegs_pres : ∀ r ∈ preserved, r ∉ wideRegs := by decide

/-- `Ctx` through code that writes registers of `wideRegs` and safe regions. -/
theorem Ctx.kf (hL : L.Ok) {t t' : State} (hc : Ctx L g lr m₀ t) (k : Kp wideRegs t t')
    {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r) (hsy : t'.syms = t.syms) :
    Ctx L g lr m₀ t' :=
  hc.keep hL k.rd k.wr k.sp (fun r hr => k.gpr r (wideRegs_pres r hr)) hf hs hsy

/-- Eight zero bytes stored: the first `k` read back as zeros. -/
theorem bytesAt_writeW_zero (m : Mem) (a : Addr) {k : Nat} (hk : k ≤ 8) :
    Spec.Sha256.bytesAt (m.writeW a (0 : BitVec 64)) a k = List.replicate k 0 := by
  simp only [Spec.Sha256.bytesAt]
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.length_map, List.length_range] at h₁
  simp only [List.getElem_map, List.getElem_range, List.getElem_replicate, Mem.writeW, Mem.write,
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : i < 2 ^ 64),
    show 64 / 8 = 8 from rfl, show i < 8 by omega_arith, ite_true]
  simp

/-- `conv o s`: the `Q` bytes at `sp + o`, above the frame's pointers, shifted
right by `s` bits in place, through the words at `scratch + 2560`. -/
theorem conv_ok (hL : L.Ok) {c : Cfg} (hcl : c.len = 66) (hcw : c.w = 9) {t : State}
    (hc : Ctx L g lr m₀ t) {o s : Nat} (ho₁ : 232 ≤ o) (ho₂ : o + 72 ≤ 592) (hs₁ : 1 ≤ s) (hs₂ : s < 64) :
    WP isa (.block (c.conv o s)) t fun t' => Ctx L g lr m₀ t' ∧ Kp wideRegs t t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (96 + o), 66⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (96 + o)) 66 =
        Spec.Weierstrass.toBytes 66
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (96 + o)) 66) >>> s) := by
  have nB := hL.nB
  have nc := hL.nc
  simp only [Cfg.conv, Cfg.convBody, hcl, hcw, sSlot, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.of_syms (stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_)
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepLd (a := L.B + BitVec.ofNat 64 272) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc.inFrK k₁ (by omega_arith) (by omega_arith)) fun t₂ k₂ m₂ v₂ => ?_
  refine stepAddSp (by omega_arith) fun t₃ k₃ m₃ v₃ => ?_
  have h3 : t₃.gpr .r3 = L.scr := by rw [k₃.gpr _ (by decide), v₂, m₁, hc.pScr]
  have h7 : t₃.gpr .r7 = L.B + BitVec.ofNat 64 (96 + o) := by rw [v₃, k₂.sp, k₁.sp, hc.sp, fr_add]
  have hm₃ : t₃.mem = t.mem := by rw [m₃, m₂, m₁]
  have hWs : ∀ {u : State}, u.wr = t.wr → Ws u L.scr 8192 := fun hw =>
    ⟨⟨8192, Nat.le_refl _, by rw [hw, hc.wr]; simp, nc⟩, by decide⟩
  have hk₃ : Kp wideRegs t t₃ := ((k₁.mono).trans (k₂.mono)).trans (k₃.mono)
  -- The bytes, as words at `scratch + 2560`.
  rw [WP.block_append_iff]
  refine WP.mono (loadBytes_ok (hWs hk₃.wr) (show t₃.gpr .r3 = L.scr + BitVec.ofNat 64 0 by rw [h3, add_ofNat_zero]) (len := 66) (n := 9)
    (o := 2560) (src := .r7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (fun d hd => by rw [h7, fr_add, hk₃.rd, hk₃.wr]; exact hc.inFr (by omega_arith) (by omega_arith))
    (by rw [h7]; exact hL.stk_scr (by omega_arith) (by omega_arith))) fun t₄ ⟨hv₄, k₄, O₄⟩ => ?_
  have hk₄ : Kp wideRegs t t₄ := hk₃.trans k₄.mono
  rw [WP.block_append_iff]
  refine WP.mono (shrWords_ok (hWs hk₄.wr)
    (show t₄.gpr .r3 = L.scr + BitVec.ofNat 64 0 by rw [k₄.gpr _ (by decide), h3, add_ofNat_zero])
    (n := 9) (o := 2560) (sh := s) (by decide) (by decide) hs₁ hs₂) fun t₅ ⟨hv₅, k₅, O₅⟩ => ?_
  have hk₅ : Kp wideRegs t t₅ := hk₄.trans k₅.mono
  -- The mask, all ones.
  refine stepLi (by decide) fun t₆ k₆ m₆ v₆ => ?_
  refine stepSubi (by decide) (by decide) fun t₇ k₇ m₇ v₇ => ?_
  have hk₇ : Kp wideRegs t t₇ := (hk₅.trans k₆.mono).trans k₇.mono
  have h7₇ : t₇.gpr .r7 = L.B + BitVec.ofNat 64 (96 + o) := by
    rw [k₇.gpr _ (by decide), k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), h7]
  refine WP.mono (storeBytes_ok (hWs hk₇.wr)
    (show t₇.gpr .r3 = L.scr + BitVec.ofNat 64 0 by
      rw [k₇.gpr _ (by decide), k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), h3,
        add_ofNat_zero])
    (len := 66) (n := 9) (d := 0) (a := 2560) (dst := .r7) (by decide) (by decide) (by decide) (by decide) true
    (by rw [v₇, v₆]; rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [h7₇, add_ofNat_zero, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega_arith : 96 + o < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega_arith)]; omega_arith)
    (fun e m hem => by
      rw [h7₇, add_ofNat_zero, fr_add, hk₇.wr]; exact hc.inFrW (by omega_arith) (by omega_arith))
    (by rw [h7₇, add_ofNat_zero]; exact (hL.stk_scr (by omega_arith) (by omega_arith)).symm)) fun t₈ ⟨hb₈, k₈, O₈⟩ hsy => ?_
  rw [h7₇, add_ofNat_zero] at hb₈ O₈
  have hk₈ : Kp wideRegs t t₈ := hk₇.trans k₈.mono
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (96 + o), 66⟩] t.mem t₈.mem := by
    have f₄ := frame_of_outside (O₄.trans O₅) (by omega_arith)
    have f₈ := frame_of_outside O₈ (by omega_arith)
    rw [add_ofNat_zero, m₇, m₆] at f₈
    rw [hm₃] at f₄
    exact (f₄.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans (f₈.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩)
  refine ⟨hc.kf hL hk₈ hf (fun r hr => ?_) hsy, hk₈, hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact safe_scr L (by omega_arith)
    · exact safe_high L (by omega_arith) (by omega_arith)
  · rw [← Rfc6979.ecdsa_bytesAt, hb₈]
    simp only [ite_true]
    rw [m₇, m₆, hv₅, hv₄, h7, hm₃, Rfc6979.ecdsa_bytesAt]

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
