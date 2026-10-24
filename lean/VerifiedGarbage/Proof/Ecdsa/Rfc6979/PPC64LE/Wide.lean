module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Steps
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Blocks
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.BytesLen
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Deterministic ECDSA on PPC64LE: scalars longer than the hash

As on AArch64 (`Proof/Ecdsa/Rfc6979/AArch64/Wide.lean`), for a curve whose
scalars are longer than the hash function's output (`wide`: P-521's 66
bytes with SHA-512's 64): the `Q` bytes at an offset in the frame's top
bytes, shifted right in place through the words at `scratch + 2560`
(`conv_ok`, by `loadBytes_ok`, `shrWords_ok` and `storeBytes_ok`, with
`scratch` in `r3`); the digest for `core`, the digest then `Q - D` zero
bytes shifted right, which is the digest's number shifted left by `sh` bits
(`coreDigest_ok`); and the candidate, `V` kept in the frame's top bytes and,
after the next `V`, its first word after it, shifted right by `sh` bits
(`candW_ok`).
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
  omega)

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-- The registers that the code here writes, none of them callee-saved. -/
abbrev wideRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

theorem wideRegs_pres : ∀ r ∈ preserved, r ∉ wideRegs := by decide

/-- `Ctx` through code that writes registers of `wideRegs` and safe regions. -/
theorem Ctx.kf (hL : L.Ok) {t t' : State} (hc : Ctx L g lr m₀ t) (k : Kp wideRegs t t')
    {ws : List Region} (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe L r) : Ctx L g lr m₀ t' :=
  hc.keep hL k.rd k.wr k.sp (fun r hr => k.gpr r (wideRegs_pres r hr)) hf hs

/-- Eight zero bytes stored: the first `k` read back as zeros. -/
theorem bytesAt_writeW_zero (m : Mem) (a : Addr) {k : Nat} (hk : k ≤ 8) :
    Spec.Sha256.bytesAt (m.writeW a (0 : BitVec 64)) a k = List.replicate k 0 := by
  simp only [Spec.Sha256.bytesAt]
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.length_map, List.length_range] at h₁
  simp only [List.getElem_map, List.getElem_range, List.getElem_replicate, Mem.writeW, Mem.write,
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
    show 64 / 8 = 8 from rfl, show i < 8 by omega, ite_true]
  simp

/-- `conv o s`: the `Q` bytes at `sp + o`, in the frame's top bytes, shifted
right by `s` bits in place, through the words at `scratch + 2560`. -/
theorem conv_ok (hL : L.Ok) {c : Cfg} (hcl : c.len = 66) (hcw : c.w = 9) (he : L.e = 144) {t : State}
    (hc : Ctx L g lr m₀ t) {o s : Nat} (ho₁ : 256 ≤ o) (ho₂ : o + 72 ≤ 400) (hs₁ : 1 ≤ s) (hs₂ : s < 64) :
    WP isa (c.conv o s) t fun t' => Ctx L g lr m₀ t' ∧ Kp wideRegs t t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (96 + o), 66⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (96 + o)) 66 =
        Spec.Weierstrass.toBytes 66
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (96 + o)) 66) >>> s) := by
  have nB := hL.nB
  have nc := hL.nc
  simp only [Cfg.conv, Cfg.convBody, hcl, hcw, sSlot, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq (stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_)
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  have hc₁ := hc.kp hL k₁ m₁
  refine stepLd (a := L.B + BitVec.ofNat 64 312) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc₁.inFr (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => wp_nil ?_
  have hc₂ := hc₁.kp hL k₂ m₂
  refine stepAddSp (by omega) fun t₃ k₃ m₃ v₃ => ?_
  have hc₃ := hc₂.kp hL k₃ m₃
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
    (fun d hd => by rw [h7, fr_add]; exact hc₃.inFr (by omega) (by omega))
    (by rw [h7]; exact hL.stk_scr (by omega) (by omega))) fun t₄ ⟨hv₄, k₄, O₄⟩ => ?_
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
    (by rw [h7₇, add_ofNat_zero, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega : 96 + o < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega)]; omega)
    (fun e m hem => by
      rw [h7₇, add_ofNat_zero, fr_add, hk₇.wr]; exact hc.inFrW (by omega) (by omega))
    (by rw [h7₇, add_ofNat_zero]; exact (hL.stk_scr (by omega) (by omega)).symm)) fun t₈ ⟨hb₈, k₈, O₈⟩ => ?_
  rw [h7₇, add_ofNat_zero] at hb₈ O₈
  have hk₈ : Kp wideRegs t t₈ := hk₇.trans k₈.mono
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (96 + o), 66⟩] t.mem t₈.mem := by
    have f₄ := frame_of_outside (O₄.trans O₅) (by omega)
    have f₈ := frame_of_outside O₈ (by omega)
    rw [add_ofNat_zero, m₇, m₆] at f₈
    rw [hm₃] at f₄
    exact (f₄.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans (f₈.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩)
  refine ⟨hc.kf hL hk₈ hf fun r hr => ?_, hk₈, hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact safe_scr L (by omega)
    · exact safe_ext L (by omega) (by omega)
  · rw [← Rfc6979.ecdsa_bytesAt, hb₈]
    simp only [ite_true]
    rw [m₇, m₆, hv₅, hv₄, h7, hm₃, Rfc6979.ecdsa_bytesAt]

theorem bytesAt_copied64 (m : Mem) (D S : Addr) :
    Spec.Sha256.bytesAt (m.writeW D (m.readW S 64)) D 8 = Spec.Sha256.bytesAt m S 8 := by
  rw [show (64 : Nat) = 8 * 8 from rfl, Proof.Hmac.Common.writeW_readW]
  have := Proof.Hmac.Common.bytesAt_writeBytes_self m D (Spec.Sha256.bytesAt m S 8) (by simp [Spec.Sha256.bytesAt])
  rwa [Proof.Hmac.Common.bytesAt_length] at this

theorem app_eq {a b c d : List Byte} (h₁ : a = c) (h₂ : b = d) : a ++ b = c ++ d := h₁ ▸ h₂ ▸ rfl

theorem shift_mul (e : Nat) : (e * 2 ^ (8 * 2)) >>> 9 = e * 2 ^ 7 := by
  rw [Nat.shiftRight_eq_div_pow, show e * 2 ^ (8 * 2) = e * 2 ^ 7 * 2 ^ 9 by rw [Nat.mul_assoc, ← Nat.pow_add],
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-! ## The digest for `core` -/

/-- The digest (from `digest`, loaded into `r9`) and a zero word after it, in
the frame's top bytes. -/
theorem dig_ok (hL : L.Ok) {c : Cfg} (hcD : c.H.D = 64) (he : L.e = 144) (hdn : 64 ≤ dn) {t : State}
    (hc : Ctx L g lr m₀ t) :
    WP isa (.block (([.addSp .r11 0, .load .d .r9 .r11 fDigest, .li .r8 0, .store .d .r8 .r11 (fX + c.H.D)] :
      List Instr) ++ Cfg.copyW (c.H.D / 4) .r9 0 .r11 fX)) t fun u => Ctx L g lr m₀ u ∧
      Frame [⟨L.B + BitVec.ofNat 64 352, 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 352) 66 =
        Spec.Sha256.bytesAt t.mem L.dg 64 ++ List.replicate 2 0 := by
  have nB := hL.nB
  have ng := hL.ng
  simp only [hcD, fX, fDigest, Nat.reduceAdd, Nat.reduceDiv]
  rw [List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  have hc₁ := hc.kp hL k₁ m₁
  refine stepLd (a := L.B + BitVec.ofNat 64 320) (by decide) (by decide) (by rw [hb, fr_add])
    (hc₁.inFr (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => ?_
  have hc₂ := hc₁.kp hL k₂ m₂
  refine stepLi (by decide) fun t₃ k₃ m₃ v₃ => ?_
  have hc₃ := hc₂.kp hL k₃ m₃
  refine stepStd (a := L.B + BitVec.ofNat 64 416) (by decide) (by decide)
    (by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), hb, fr_add]) (hc₃.inFrW (by omega) (by omega))
    fun t₄ k₄ g₄ m₄ => ?_
  rw [v₃] at m₄
  have f₄ : Frame [⟨L.B + BitVec.ofNat 64 416, 8⟩] t₃.mem t₄.mem := by
    rw [m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hc₄ := hc₃.keep hL k₄.rd k₄.wr k₄.sp (fun r _ => by rw [g₄]) f₄
    (by simp only [List.mem_singleton]; rintro r rfl; exact safe_ext L (by omega) (by omega))
  have r₄ : ∀ r, r ≠ .r8 → t₄.gpr r = t₂.gpr r := fun r hr => by rw [g₄, k₃.gpr _ (by simp [hr])]
  have hdgSep : Region.Disjoint ⟨L.dg, 64⟩ ⟨L.B + BitVec.ofNat 64 352, 72⟩ :=
    (hL.stk_DG (d := 352) (n := 72) (by omega)).symm.sub_left (Region.sub_prefix hdn)
  -- The digest.
  refine WP.mono (copyW_ok (S := L.dg) (D := L.B + BitVec.ofNat 64 96) (so := 0) (d := 256) (K := 16)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [add_ofNat_zero, fr_add]; exact hdgSep.sub_right (Region.sub_prefix (by omega)))
    (by omega) (by omega) (by omega) 16 (Nat.le_refl _) t₄
    (by rw [r₄ _ (by decide), v₂, m₁, hc.pDg]) (by rw [r₄ _ (by decide), k₂.gpr _ (by decide), hb])
    (fun j hj => hc₄.inDg (o := 0 + 4 * j) (by omega) (by omega))
    (fun j hj => by rw [fr_add]; exact hc₄.inFrW (by omega) (by omega))) fun t₅ ⟨k₅, f₅, v₅⟩ => ?_
  rw [add_ofNat_zero, fr_add] at v₅
  rw [fr_add] at f₅
  have hc₅ := hc₄.keep hL k₅.rd k₅.wr k₅.sp
    (fun r hr => k₅.gpr r (by intro h; simp at h; subst h; simp [preserved] at hr))
    f₅ (by simp only [List.mem_singleton]; rintro r rfl; exact safe_ext L (by omega) (by omega))
  refine ⟨hc₅, ?_, ?_⟩
  · have hm₂ : t₃.mem = t.mem := by rw [m₃, m₂, m₁]
    rw [← hm₂]
    exact (f₄.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩).trans
      (f₅.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩)
  · rw [show (66 : Nat) = 64 + 2 from rfl, bytesAt_add, v₅, Offset.add_add]
    refine app_eq ?_ ?_
    · rw [bytesAt_frame f₄ (p := L.dg) (n := 64) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hdgSep.sub_right (Offset.sub _ (by omega) (by omega))) (by omega), m₃, m₂, m₁]
    · rw [bytesAt_frame f₅ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by omega), m₄]
      exact bytesAt_writeW_zero _ _ (by decide)

/-- The digest for `core`: the digest's number shifted left by `sh` bits, in
`Q` bytes in the frame's top bytes. -/
theorem coreDigest_ok (hL : L.Ok) {c : Cfg} (hcl : c.len = 66) (hcD : c.H.D = 64) (hcw : c.w = 9) (hsh : c.sh = 7)
    (he : L.e = 144) (hdn : 64 ≤ dn) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa c.coreDigest t fun t' => Ctx L g lr m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 352, 72⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 352) 66 =
        Spec.Weierstrass.toBytes 66 (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg 64) * 2 ^ 7) := by
  have nB := hL.nB
  rw [Cfg.coreDigest]
  refine WP.seq (WP.mono (dig_ok hL hcD he hdn hc) fun t₅ ⟨hc₅, f₅, hY⟩ => ?_)
  rw [hcl, hcD, hsh, show 8 * (66 - 64) - 7 = 9 from rfl]
  refine WP.mono (conv_ok hL hcl hcw he hc₅ (o := 256) (s := 9) (by decide) (by decide) (by decide) (by decide))
    fun t₆ ⟨hc₆, _, f₆, v₆⟩ => ⟨hc₆, ?_, ?_⟩
  · refine (f₅.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (f₆.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega)⟩
  · -- The digest then two zero bytes, shifted right by 9 bits.
    simp only [Nat.reduceAdd] at v₆
    rw [v₆, hY, Rfc6979.ofBytes_append_zeros, shift_mul]

/-- `scratch` in `r3`, from the frame, as a conversion begins. -/
theorem ldScr_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block [.addSp .r11 0, .load .d .r3 .r11 fScratch]) t fun u =>
      Ctx L g lr m₀ u ∧ u.gpr .r3 = L.scr := by
  have nB := hL.nB
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  have hc₁ := hc.kp hL k₁ m₁
  refine stepLd (a := L.B + BitVec.ofNat 64 312) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc₁.inFr (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => wp_nil ⟨hc₁.kp hL k₂ m₂, by rw [v₂, m₁, hc.pScr]⟩

/-! ## The candidate -/

/-- `V`'s `D` bytes to the candidate's place. -/
theorem keepV_ok (hL : L.Ok) {c : Cfg} (hcD : c.H.D = 64) (he : L.e = 144) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block c.keepV) t fun u => Ctx L g lr m₀ u ∧ Kp wideRegs t u ∧
      Frame [⟨L.B + BitVec.ofNat 64 424, 64⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 424) 64 =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 192) 64 := by
  have nB := hL.nB
  simp only [Cfg.keepV, hcD, fV, fKb, Nat.reduceDiv]
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  have hc₁ := hc.kp hL k₁ m₁
  refine WP.mono (copyW_ok (S := L.B + BitVec.ofNat 64 96) (D := L.B + BitVec.ofNat 64 96) (so := 96) (d := 328)
    (K := 16) (by decide) (by decide) (by decide) (by decide)
    (by rw [fr_add, fr_add]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
    (by omega) (by omega) (by omega) 16 (Nat.le_refl _) t₁ hb hb
    (fun j hj => by rw [fr_add]; exact hc₁.inFr (by omega) (by omega))
    (fun j hj => by rw [fr_add]; exact hc₁.inFrW (by omega) (by omega))) fun t₂ ⟨k₂, f₂, v₂⟩ => ?_
  rw [fr_add, fr_add, m₁] at v₂
  rw [fr_add, m₁] at f₂
  exact ⟨hc₁.keep hL k₂.rd k₂.wr k₂.sp
    (fun r hr => k₂.gpr r (by intro h; simp at h; subst h; simp [preserved] at hr))
    (m₁ ▸ f₂) (by simp only [List.mem_singleton]; rintro r rfl; exact safe_ext L (by omega) (by omega)),
    (k₁.mono).trans (k₂.mono), f₂, v₂⟩

/-- The candidate's next eight bytes, from `V`. -/
theorem top_ok (hL : L.Ok) {c : Cfg} (hcD : c.H.D = 64) (he : L.e = 144) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block [.addSp .r11 0, .load .d .r8 .r11 fV, .store .d .r8 .r11 (fKb + c.H.D)]) t fun u =>
      Ctx L g lr m₀ u ∧ Kp wideRegs t u ∧ Frame [⟨L.B + BitVec.ofNat 64 488, 8⟩] t.mem u.mem ∧
      u.mem = t.mem.writeW (L.B + BitVec.ofNat 64 488) (t.mem.readW (L.B + BitVec.ofNat 64 192) 64) := by
  have nB := hL.nB
  simp only [hcD, fV, fKb, Nat.reduceAdd]
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  have hc₁ := hc.kp hL k₁ m₁
  refine stepLd (a := L.B + BitVec.ofNat 64 192) (by decide) (by decide) (by rw [hb, fr_add])
    (hc₁.inFr (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => ?_
  have hc₂ := hc₁.kp hL k₂ m₂
  refine stepStd (a := L.B + BitVec.ofNat 64 488) (by decide) (by decide)
    (by rw [k₂.gpr _ (by decide), hb, fr_add]) (hc₂.inFrW (by omega) (by omega)) fun t₃ k₃ g₃ m₃ => wp_nil ?_
  rw [v₂, m₂, m₁] at m₃
  have f₃ : Frame [⟨L.B + BitVec.ofNat 64 488, 8⟩] t.mem t₃.mem := by
    rw [m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc₂.keep hL k₃.rd k₃.wr k₃.sp (fun r _ => by rw [g₃]) (by rw [m₂, m₁]; exact f₃)
    (by simp only [List.mem_singleton]; rintro r rfl; exact safe_ext L (by omega) (by omega)),
    ((k₁.mono).trans (k₂.mono)).trans (k₃.mono), f₃, m₃⟩

/-- What a candidate changes: `scratch`, the stack below the frame, `K` and
`V`, and the candidate in the frame's top bytes. -/
abbrev CWW {dn : Nat} (L : Lay dn) : List Region :=
  [⟨L.scr, 8192⟩, ⟨L.B, 96⟩, ⟨L.B + BitVec.ofNat 64 128, 128⟩, ⟨L.B + BitVec.ofNat 64 424, 72⟩]

theorem kvw_cww : ∀ r ∈ kvW L, ∃ r' ∈ CWW L, Region.Sub r r' := fun r hr => ⟨r, by
  simp only [CWW, kvW, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with h | h | h <;> simp [h], fun _ h => h⟩

/-- Two `V`s to a candidate: `V = HMAC_K(V)`, kept in the frame's top
bytes, then `V = HMAC_K(V)` again, its first word after it, and the
candidate's `Q` bytes shifted right by `sh` bits. -/
theorem candW_ok (P : Kit) {c : Cfg} (hcH : c.H = P.hm) (hW : c.wide = true) (hcl : c.len = 66) (hcD : c.H.D = 64)
    (hcw : c.w = 9) (hsh : c.sh = 7) (he : L.e = 144) (hq : L.HFar) (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa c.cand t fun u => Ctx L g lr m₀ u ∧ Frame (CWW L) t.mem u.mem ∧
      keyOf P L u.mem = keyOf P L t.mem ∧
      vOf P L u.mem = Spec.Hmac.hmac P.hH.SH.H (keyOf P L t.mem)
        (Spec.Hmac.hmac P.hH.SH.H (keyOf P L t.mem) (vOf P L t.mem)) ∧
      (Spec.Hmac.hmac P.hH.SH.H (keyOf P L t.mem) (vOf P L t.mem)).length = 64 ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 424) 66 =
        Spec.Weierstrass.toBytes 66 (Spec.Weierstrass.ofBytes
          ((Spec.Hmac.hmac P.hH.SH.H (keyOf P L t.mem) (vOf P L t.mem) ++
            Spec.Hmac.hmac P.hH.SH.H (keyOf P L t.mem)
              (Spec.Hmac.hmac P.hH.SH.H (keyOf P L t.mem) (vOf P L t.mem))).take 66) >>> 7) := by
  have nB := hL.nB
  have hD64 : P.H.D = 64 := by rw [← hcD, hcH]; rfl
  simp only [Cfg.cand, hW, ite_true, Cfg.candTop, hsh]
  refine WP.seq (WP.mono (hmacV_ok P hcH hL hq hc) fun u₁ ⟨hc₁, hf₁, hk₁, _, hv₁⟩ => ?_)
  -- `V` in the frame's top bytes.
  refine WP.seq (WP.mono (keepV_ok hL hcD he hc₁) fun u₂ ⟨hc₂, _, hf₂, hb₂⟩ => ?_)
  have kv : ∀ {m m' : Mem} {ws : List Region}, Frame ws m m' →
      (∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 128, 128⟩ r) →
      keyOf P L m' = keyOf P L m ∧ vOf P L m' = vOf P L m := fun hf hd =>
    ⟨bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) (by omega),
      bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) (by omega)⟩
  have e₂ := kv hf₂ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega)
  refine WP.seq (WP.mono (hmacV_ok P hcH hL hq hc₂) fun u₃ ⟨hc₃, hf₃, hk₃, _, hv₃⟩ => ?_)
  have hb₃ : Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 424) 64 = vOf P L u₁.mem := by
    rw [bytesAt_frame hf₃ (fun r hr => by
      simp only [kvW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hL.stk_SCR (by omega)
      · exact Offset.disjoint_base _ (by omega) (by omega)
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb₂, vOf, hD64]
  refine WP.seq (WP.mono (top_ok hL hcD he hc₃) fun u₅ ⟨hc₅, _, hf₅, hm₅⟩ => ?_)
  refine WP.mono (conv_ok hL hcl hcw he hc₅ (o := 328) (s := 7) (by decide) (by decide) (by decide) (by decide))
    fun u₆ ⟨hc₆, _, hf₆, hb₆⟩ => ?_
  simp only [Nat.reduceAdd] at hf₆ hb₆
  have e₅ := kv hf₅ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have e₆ := kv hf₆ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.stk_scr (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  refine ⟨hc₆, ?_, ?_, ?_, by rw [← hv₁, Proof.Hmac.Common.bytesAt_length, hD64], ?_⟩
  · have c₃ : (⟨L.B + BitVec.ofNat 64 424, 72⟩ : Region) ∈ CWW L := by simp [CWW]
    have c₁ : (⟨L.scr, 8192⟩ : Region) ∈ CWW L := by simp [CWW]
    refine ((((hf₁.sub kvw_cww).trans (hf₂.sub fun r hr => ⟨_, c₃, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩)).trans
      (hf₃.sub kvw_cww)).trans (hf₅.sub fun r hr => ⟨_, c₃, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩)).trans
      (hf₆.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, c₁, Offset.sub_base _ (by omega)⟩
    · exact ⟨_, c₃, Offset.sub _ (by omega) (by omega)⟩
  · rw [e₆.1, e₅.1, hk₃, e₂.1, hk₁]
  · rw [e₆.2, e₅.2, hv₃, e₂.1, e₂.2, hv₁, hk₁]
  · -- The candidate's bytes: the first `V`, then the next two of the second.
    have hv₃' : Spec.Hmac.hmac P.hH.SH.H (keyOf P L t.mem)
        (Spec.Hmac.hmac P.hH.SH.H (keyOf P L t.mem) (vOf P L t.mem)) = vOf P L u₃.mem := by
      rw [hv₃, e₂.1, e₂.2, hv₁, hk₁]
    have hl₁ : (vOf P L u₁.mem).length = 64 := by rw [Proof.Hmac.Common.bytesAt_length, hD64]
    rw [hb₆, hv₃', ← hv₁, List.take_append, List.take_of_length_le (by omega), hl₁,
      show 66 - 64 = 2 from rfl]
    refine congrArg (fun x => Spec.Weierstrass.toBytes 66 (Spec.Weierstrass.ofBytes x >>> 7)) ?_
    rw [show (66 : Nat) = 64 + 2 from rfl, bytesAt_add, Offset.add_add]
    simp only [Nat.reduceAdd]
    refine app_eq ?_ ?_
    · rw [bytesAt_frame hf₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
          (by omega), hb₃]
    · rw [bytesAt_take _ _ (k := 8) (by omega), hm₅, bytesAt_copied64]
      show _ = (Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 192) P.H.D).take 2
      rw [hD64, ← bytesAt_take _ _ (by omega), ← bytesAt_take _ _ (by omega)]

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
