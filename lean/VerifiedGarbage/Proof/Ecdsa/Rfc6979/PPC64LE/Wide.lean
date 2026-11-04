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
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Entry
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Copy
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

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
  omega_arith)

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
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : i < 2 ^ 64),
    show 64 / 8 = 8 from rfl, show i < 8 by omega_arith, ite_true]
  simp

/-- `conv o s`: the `Q` bytes at `sp + o`, in the frame's top bytes, shifted
right by `s` bits in place, through the words at `scratch + 2560`. -/
theorem conv_ok (hL : L.Ok) {c : Cfg} (hcl : c.len = 66) (hcw : c.w = 9) (he : L.e = 272) {t : State}
    (hc : Ctx L g lr m₀ t) {o s : Nat} (ho₁ : 256 ≤ o) (ho₂ : o + 72 ≤ 528) (hs₁ : 1 ≤ s) (hs₂ : s < 64) :
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
    (hc₁.inFr (by omega_arith) (by omega_arith)) fun t₂ k₂ m₂ v₂ => wp_nil ?_
  have hc₂ := hc₁.kp hL k₂ m₂
  refine stepAddSp (by omega_arith) fun t₃ k₃ m₃ v₃ => ?_
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
    (fun d hd => by rw [h7, fr_add]; exact hc₃.inFr (by omega_arith) (by omega_arith))
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
    (by rw [h7₇, add_ofNat_zero]; exact (hL.stk_scr (by omega_arith) (by omega_arith)).symm)) fun t₈ ⟨hb₈, k₈, O₈⟩ => ?_
  rw [h7₇, add_ofNat_zero] at hb₈ O₈
  have hk₈ : Kp wideRegs t t₈ := hk₇.trans k₈.mono
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (96 + o), 66⟩] t.mem t₈.mem := by
    have f₄ := frame_of_outside (O₄.trans O₅) (by omega_arith)
    have f₈ := frame_of_outside O₈ (by omega_arith)
    rw [add_ofNat_zero, m₇, m₆] at f₈
    rw [hm₃] at f₄
    exact (f₄.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans (f₈.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩)
  refine ⟨hc.kf hL hk₈ hf fun r hr => ?_, hk₈, hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact safe_scr L (by omega_arith)
    · exact safe_ext L (by omega_arith) (by omega_arith)
  · rw [← Rfc6979.ecdsa_bytesAt, hb₈]
    simp only [ite_true]
    rw [m₇, m₆, hv₅, hv₄, h7, hm₃, Rfc6979.ecdsa_bytesAt]

theorem bytesAt_copied64 (m : Mem) (D S : Addr) :
    Spec.Sha256.bytesAt (m.writeW D (m.readW S 64)) D 8 = Spec.Sha256.bytesAt m S 8 := by
  rw [show (64 : Nat) = 8 * 8 from rfl, Proof.Hmac.Common.writeW_readW]
  have := Proof.Hmac.Common.bytesAt_writeBytes_self m D (Spec.Sha256.bytesAt m S 8) (by simp [Spec.Sha256.bytesAt])
  rwa [Proof.Hmac.Common.bytesAt_length] at this

theorem app_eq {a b c d : List Byte} (h₁ : a = c) (h₂ : b = d) : a ++ b = c ++ d := h₁ ▸ h₂ ▸ rfl

/-- `scratch` in `r3`, from the frame, as a conversion begins. -/
theorem ldScr_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block [.addSp .r11 0, .load .d .r3 .r11 fScratch]) t fun u =>
      Ctx L g lr m₀ u ∧ u.gpr .r3 = L.scr := by
  have nB := hL.nB
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  have hc₁ := hc.kp hL k₁ m₁
  refine stepLd (a := L.B + BitVec.ofNat 64 312) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc₁.inFr (by omega_arith) (by omega_arith)) fun t₂ k₂ m₂ v₂ => wp_nil ⟨hc₁.kp hL k₂ m₂, by rw [v₂, m₁, hc.pScr]⟩

/-! ## Zero words, and the digest in the frame's top bytes -/

/-- `k` zero words (from `r8`) at the frame's `o`, in its top bytes. -/
theorem zeros_ok (hL : L.Ok) {o : Nat} (ho₁ : 256 ≤ o) (ho₂ : o + 72 ≤ 256 + L.e) (ho₄ : o % 4 = 0) :
    ∀ k ≤ 9, ∀ {u : State}, Ctx L g lr m₀ u → u.gpr .r11 = L.B + BitVec.ofNat 64 96 → u.gpr .r8 = 0 →
    WP isa (.block ((List.range k).map fun j => .store .d .r8 .r11 (o + 8 * j))) u
      fun u' => Ctx L g lr m₀ u' ∧ Kp [] u u' ∧ Frame [⟨L.B + BitVec.ofNat 64 (96 + o), 72⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (96 + o)) (8 * k) = List.replicate (8 * k) 0
  | 0, _, u, hc, _, _ => wp_nil ⟨hc, Kp.refl _ _, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hc, h11, h8 => by
    have := hL.nB
    have := hc.ne
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeros_ok hL ho₁ ho₂ ho₄ k (by omega) hc h11 h8) fun u₁ ⟨hc₁, k₁, hf₁, hb₁⟩ => ?_
    refine stepStd (a := L.B + BitVec.ofNat 64 (96 + o + 8 * k)) (by decide) ⟨by omega, by omega⟩
      (by rw [k₁.gpr _ (by simp), h11, fr_add, Nat.add_assoc]) (hc₁.inFrW (by omega) (by omega))
      fun u₂ k₂ g₂ m₂ => wp_nil ?_
    rw [k₁.gpr _ (by simp), h8] at m₂
    have hf₂ : Frame [⟨L.B + BitVec.ofNat 64 (96 + o + 8 * k), 8⟩] u₁.mem u₂.mem := by
      rw [m₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine ⟨hc₁.keep hL k₂.rd k₂.wr k₂.sp (fun r _ => by rw [g₂]) hf₂
      (by simp only [List.mem_singleton]; rintro r rfl; exact safe_ext L (by omega) (by omega)),
      k₁.trans k₂, hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩), ?_⟩
    rw [show 8 * (k + 1) = 8 * k + 8 by omega, bytesAt_add, Offset.add_add, ← List.replicate_append_replicate]
    refine app_eq ?_ ?_
    · rw [← hb₁]
      exact bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
    · rw [m₂, show 96 + o + 8 * k = 96 + o + 8 * k from rfl]
      exact bytesAt_writeW_zero _ _ (Nat.le_refl _)

/-- The frame's 72 bytes at `o` (in its top bytes): `off` zero bytes, the
digest's first `D` bytes, then zeros. -/
theorem dig_ok (hL : L.Ok) {D : Nat} (hD4 : D % 4 = 0) (hdn : D ≤ dn) {o off : Nat} (ho₁ : 256 ≤ o)
    (ho₂ : o + 72 ≤ 256 + L.e) (ho₄ : o % 4 = 0) (hoff : off + D ≤ 72) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block (([.addSp .r11 0, .load .d .r9 .r11 fDigest] : List Instr) ++ Cfg.zero9 o ++
      Cfg.copyW (D / 4) .r9 0 .r11 (o + off))) t fun u => Ctx L g lr m₀ u ∧ Kp wideRegs t u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (96 + o), 72⟩] t.mem u.mem ∧
      ∀ z, off + D + z ≤ 72 → Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (96 + o)) (off + D + z) =
        List.replicate off 0 ++ Spec.Sha256.bytesAt t.mem L.dg D ++ List.replicate z 0 := by
  have nB := hL.nB
  have ng := hL.ng
  have hne := hc.ne
  rw [List.append_assoc, WP.block_append_iff]
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  have hc₁ := hc.kp hL k₁ m₁
  refine stepLd (a := L.B + BitVec.ofNat 64 320) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc₁.inFr (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => wp_nil ?_
  have hc₂ := hc₁.kp hL k₂ m₂
  have h9 : t₂.gpr .r9 = L.dg := by rw [v₂, m₁, hc.pDg]
  rw [Cfg.zero9, List.cons_append]
  refine stepLi (by decide) fun t₃ k₃ m₃ v₃ => ?_
  rw [WP.block_append_iff]
  have hc₃ := hc₂.kp hL k₃ m₃
  have hb₃ : t₃.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), hb]
  refine WP.mono (zeros_ok hL ho₁ ho₂ ho₄ 9 (Nat.le_refl _) hc₃ hb₃ (by rw [v₃]; rfl)) fun t₄ ⟨hc₄, k₄, f₄, z₄⟩ => ?_
  have hdgSep : Region.Disjoint ⟨L.dg, D⟩ ⟨L.B + BitVec.ofNat 64 (96 + o), 72⟩ :=
    (hL.stk_DG (d := 96 + o) (n := 72) (by omega)).symm.sub_left (Region.sub_prefix hdn)
  have e4 : 4 * (D / 4) = D := by omega
  refine WP.mono (copyW_ok (S := L.dg) (D := L.B + BitVec.ofNat 64 96) (so := 0) (d := o + off) (K := D / 4)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [add_ofNat_zero, fr_add, e4]; exact hdgSep.sub_right (Offset.sub _ (by omega) (by omega)))
    (by omega) (by omega) (by omega) (D / 4) (Nat.le_refl _) t₄
    (by rw [k₄.gpr _ (by simp), k₃.gpr _ (by decide), h9]) (by rw [k₄.gpr _ (by simp), hb₃])
    (fun j hj => hc₄.inDg (o := 0 + 4 * j) (by omega) (by omega))
    (fun j hj => by rw [fr_add]; exact hc₄.inFrW (by omega) (by omega))) fun t₅ ⟨k₅, f₅, v₅⟩ => ?_
  rw [add_ofNat_zero, fr_add, e4] at v₅
  rw [fr_add, e4] at f₅
  have hc₅ := hc₄.keep hL k₅.rd k₅.wr k₅.sp
    (fun r hr => k₅.gpr r (by intro h; simp at h; subst h; simp [preserved] at hr))
    f₅ (by simp only [List.mem_singleton]; rintro r rfl; exact safe_ext L (by omega) (by omega))
  have hm₃ : t₃.mem = t.mem := by rw [m₃, m₂, m₁]
  refine ⟨hc₅, ((((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans k₅.mono), ?_, fun z hz => ?_⟩
  · rw [← hm₃]
    exact f₄.trans (f₅.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩)
  · have hz₄ : ∀ a n, a + n ≤ 72 → Spec.Sha256.bytesAt t₄.mem (L.B + BitVec.ofNat 64 (96 + o + a)) n =
        List.replicate n 0 := fun a n han => by
      have h1 := bytesAt_take t₄.mem (L.B + BitVec.ofNat 64 (96 + o)) (n := a + n) (k := 8 * 9) (by omega)
      rw [z₄, List.take_replicate, Nat.min_eq_left (by omega), bytesAt_add, Offset.add_add,
        ← List.replicate_append_replicate] at h1
      exact (List.append_inj h1 (by simp [Spec.Sha256.bytesAt])).2
    have dK : ∀ {a n : Nat}, a + n ≤ off ∨ off + D ≤ a → a + n ≤ 72 →
        Spec.Sha256.bytesAt t₅.mem (L.B + BitVec.ofNat 64 (96 + o + a)) n = List.replicate n 0 := fun h h' => by
      rw [bytesAt_frame f₅ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
      exact hz₄ _ _ h'
    have A : Spec.Sha256.bytesAt t₅.mem (L.B + BitVec.ofNat 64 (96 + o)) off = List.replicate off 0 := by
      have := dK (a := 0) (n := off) (.inl (by omega)) (by omega)
      rwa [Nat.add_zero] at this
    have B : Spec.Sha256.bytesAt t₅.mem (L.B + BitVec.ofNat 64 (96 + o + off)) D = Spec.Sha256.bytesAt t.mem L.dg D := by
      rw [show 96 + o + off = 96 + (o + off) by omega, v₅, ← hm₃]
      exact bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hdgSep) (by omega)
    have C : Spec.Sha256.bytesAt t₅.mem (L.B + BitVec.ofNat 64 (96 + o + (off + D))) z = List.replicate z 0 :=
      dK (.inr (by omega)) (by omega)
    rw [bytesAt_add, bytesAt_add, Offset.add_add, Offset.add_add, A, B, C]

theorem shift_back (e sh : Nat) (hs : sh < 8) : (e * 2 ^ 8) >>> (8 - sh) = e * 2 ^ sh := by
  rw [Nat.shiftRight_eq_div_pow, show e * 2 ^ 8 = e * 2 ^ sh * 2 ^ (8 - sh) by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- If `wide`: `h`, `Q - D` zero bytes then the digest, at `fX`. -/
theorem hPrep_ok (hL : L.Ok) {c : Cfg} (hD4 : c.D % 4 = 0) (hdn : c.D ≤ dn) (hQD : c.D < c.len) (hq : c.len ≤ 72)
    (he : L.e = 272) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block c.hPrep) t fun u => Ctx L g lr m₀ u ∧ Kp wideRegs t u ∧
      Frame [⟨L.B + BitVec.ofNat 64 352, 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 352) c.len =
        List.replicate (c.len - c.D) 0 ++ Spec.Sha256.bytesAt t.mem L.dg c.D := by
  rw [Cfg.hPrep, show fX + c.len - c.D = fX + (c.len - c.D) by simp only [fX]; omega]
  refine WP.mono (dig_ok hL (o := fX) (off := c.len - c.D) hD4 hdn (by decide) (by rw [he]; decide) (by decide)
    (by omega) hc)
    fun u ⟨hcu, ku, fu, bu⟩ => ⟨hcu, ku, fu, ?_⟩
  have := bu 0 (by omega)
  rw [show c.len - c.D + c.D + 0 = c.len by omega, List.replicate_zero, List.append_nil] at this
  exact this

/-- If `wide` and `sh ≠ 0` (P-521's): the digest for `core`, the digest's
number shifted left by `sh` bits, in `Q` bytes at `fXc`. -/
theorem xPrep_ok (hL : L.Ok) {c : Cfg} (hD4 : c.D % 4 = 0) (hdn : c.D ≤ dn) (hQD : c.D < c.len) (hcl : c.len = 66)
    (hcw : c.w = 9) (hsh₁ : c.sh ≠ 0) (hsh₂ : c.sh < 8) (he : L.e = 272) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa c.xPrep t fun u => Ctx L g lr m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 424, 72⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 424) 66 =
        Spec.Weierstrass.toBytes 66 (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg c.D) * 2 ^ c.sh) := by
  rw [Cfg.xPrep, ite_eq_right_of_eq_false _ _ (eq_false hsh₁),
    show fXc + c.len - c.D - 1 = fXc + (c.len - c.D - 1) by simp only [fXc]; omega]
  refine WP.seq (WP.mono (dig_ok hL (o := fXc) (off := c.len - c.D - 1) hD4 hdn (by decide) (by rw [he]; decide)
    (by decide) (by omega) hc) fun u ⟨hcu, _, fu, bu⟩ => ?_)
  refine WP.mono (conv_ok hL hcl hcw he hcu (o := fXc) (s := 8 - c.sh) (by decide) (by decide) (by omega) (by omega))
    fun v ⟨hcv, _, fv, bv⟩ => ⟨hcv, ?_, ?_⟩
  · refine (fu.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (fv.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega)⟩
  · have hY := bu 1 (by omega)
    rw [show c.len - c.D - 1 + c.D + 1 = 66 by omega] at hY
    simp only [show 96 + fXc = 424 from rfl] at bv hY
    rw [bv, hY, List.append_assoc, Rfc6979.ofBytes_zeros, Rfc6979.ofBytes_append_zeros, show 8 * 1 = 8 from rfl,
      shift_back _ _ hsh₂]

/-! ## The candidate -/

/-- `genT` with one more `V`: the last after the others. -/
theorem genT_succ (H : Spec.Hmac.HashFunction) (K : List Byte) : ∀ (k : Nat) (V : List Byte),
    Spec.Ecdsa.Rfc6979.genT H K (k + 1) V =
      ((Spec.Ecdsa.Rfc6979.genT H K k V).1 ++ Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k V).2,
        Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k V).2)
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | k + 1, V => by
    show (Spec.Hmac.hmac H K V ++ (Spec.Ecdsa.Rfc6979.genT H K (k + 1) (Spec.Hmac.hmac H K V)).1,
        (Spec.Ecdsa.Rfc6979.genT H K (k + 1) (Spec.Hmac.hmac H K V)).2) =
      ((Spec.Hmac.hmac H K V ++ (Spec.Ecdsa.Rfc6979.genT H K k (Spec.Hmac.hmac H K V)).1) ++
          Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k (Spec.Hmac.hmac H K V)).2,
        Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k (Spec.Hmac.hmac H K V)).2)
    rw [genT_succ H K k (Spec.Hmac.hmac H K V)]
    simp

theorem hmac_length (P : Kit) (K x : List Byte) : (Spec.Hmac.hmac P.hH.SH.H K x).length = P.H.D :=
  P.hH.hashLen _

theorem genT_length (P : Kit) (K : List Byte) : ∀ (k : Nat) (V : List Byte),
    (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H K k V).1.length = k * P.H.D
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | k + 1, V => by
    rw [genT_succ, List.length_append, genT_length P K k V, hmac_length]
    rw [Nat.succ_mul]

/-- `V`'s `D` bytes to `T + j D`. -/
theorem keepV_ok (hL : L.Ok) {c : Cfg} (hD4 : c.D % 4 = 0) {j : Nat} (hj : j * c.D + c.D ≤ 128) (he : L.e = 272)
    {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block (c.keepV j)) t fun u => Ctx L g lr m₀ u ∧ Kp wideRegs t u ∧
      Frame [⟨L.B + BitVec.ofNat 64 (496 + j * c.D), c.D⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (496 + j * c.D)) c.D =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 192) c.D := by
  have nB := hL.nB
  have e4 : 4 * (c.D / 4) = c.D := by omega
  simp only [Cfg.keepV, fV, fT]
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  have hc₁ := hc.kp hL k₁ m₁
  refine WP.mono (copyW_ok (S := L.B + BitVec.ofNat 64 96) (D := L.B + BitVec.ofNat 64 96) (so := 96)
    (d := 400 + j * c.D) (K := c.D / 4) (by decide) (by decide) (by decide) (by decide)
    (by rw [fr_add, fr_add, e4]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
    (by omega) (by omega) (by omega) (c.D / 4) (Nat.le_refl _) t₁ hb hb
    (fun j hj => by rw [fr_add]; exact hc₁.inFr (by omega) (by omega))
    (fun j hj => by rw [fr_add]; exact hc₁.inFrW (by omega) (by omega))) fun t₂ ⟨k₂, f₂, v₂⟩ => ?_
  rw [fr_add, fr_add, m₁, e4, show 96 + (400 + j * c.D) = 496 + j * c.D by omega] at v₂
  rw [fr_add, m₁, e4, show 96 + (400 + j * c.D) = 496 + j * c.D by omega] at f₂
  exact ⟨hc₁.keep hL k₂.rd k₂.wr k₂.sp
    (fun r hr => k₂.gpr r (by intro h; simp at h; subst h; simp [preserved] at hr))
    (m₁ ▸ f₂) (by simp only [List.mem_singleton]; rintro r rfl; exact safe_ext L (by omega) (by omega)),
    (k₁.mono).trans (k₂.mono), f₂, v₂⟩

/-- What a candidate changes: `scratch`, the stack below the frame, `K` and
`V`, and `T` in the frame's top bytes. -/
abbrev CWW {dn : Nat} (L : Lay dn) : List Region :=
  [⟨L.scr, 8192⟩, ⟨L.B, 96⟩, ⟨L.B + BitVec.ofNat 64 128, 128⟩, ⟨L.B + BitVec.ofNat 64 496, 128⟩]

theorem kvw_cww : ∀ r ∈ kvW L, ∃ r' ∈ CWW L, Region.Sub r r' := fun r hr => ⟨r, by
  simp only [CWW, kvW, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with h | h | h <;> simp [h], fun _ h => h⟩

/-- The first `k` `V`s of the candidate: each `V = HMAC_K(V)`, copied to `T`
after the ones before. -/
theorem candW_ok (P : Kit) {c : Cfg} (hK : KOk P c L) (hL : L.Ok) (hq : L.HFar) (he : L.e = 272) :
    ∀ k, k * P.H.D ≤ 128 → ∀ {t : State}, Ctx L g lr m₀ t → SyOk L m₀ t →
    WP isa (c.candW k) t fun u => Ctx L g lr m₀ u ∧ Frame (CWW L) t.mem u.mem ∧
      keyOf P L u.mem = keyOf P L t.mem ∧
      vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H (keyOf P L t.mem) k (vOf P L t.mem)).2 ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 496) (k * P.H.D) =
        (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H (keyOf P L t.mem) k (vOf P L t.mem)).1 ∧ u.syms = t.syms
  | 0, _, t, hc, _ => wp_nil ⟨hc, Frame.refl _ _, rfl, rfl, by simp [Spec.Ecdsa.Rfc6979.genT, Spec.Sha256.bytesAt],
      rfl⟩
  | k + 1, hk, t, hc, hy => by
    have nB := hL.nB
    have hD := P.hH.hD64
    have hD4 := P.hH.hD4
    have hk' : k * P.H.D + P.H.D ≤ 128 := by rw [Nat.succ_mul] at hk; exact hk
    rw [Cfg.candW]
    refine WP.seq (WP.mono (candW_ok P hK hL hq he k (by omega) hc hy) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁, hb₁, hs₁⟩ => ?_)
    refine WP.seq (WP.mono (hmacV_ok P hK hL hq hc₁ (hy.of_syms hs₁)) fun u₂ ⟨hc₂, hf₂, hk₂, _, hv₂, hs₂⟩ => ?_)
    refine WP.mono_syms (keepV_ok hL (c := c) (j := k) (by rw [hK.D]; exact hD4) (by rw [hK.D]; exact hk') he hc₂)
      fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ hs₃ => ?_
    rw [hK.D] at hf₃ hb₃
    -- What the copy keeps: `K`, `V` and the earlier part of `T`.
    have dKV : ∀ {o : Nat}, 128 ≤ o → o + P.H.D ≤ 256 →
        Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 o) P.H.D = Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 o) P.H.D :=
      fun h₁ h₂ => bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
    have hk₃ : keyOf P L u₃.mem = keyOf P L u₂.mem := dKV (by decide) (by omega)
    have hv₃ : vOf P L u₃.mem = vOf P L u₂.mem := dKV (by decide) (by omega)
    refine ⟨hc₃, ?_, ?_, ?_, ?_, by rw [hs₃, hs₂, hs₁]⟩
    · refine ((hf₁.trans (hf₂.sub kvw_cww)).trans (hf₃.sub fun r hr => ?_))
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B + BitVec.ofNat 64 496, 128⟩, by simp [CWW], Offset.sub _ (by omega) (by omega)⟩
    · rw [hk₃, hk₂, hk₁]
    · rw [hv₃, hv₂, genT_succ, hk₁, hv₁]
    · rw [genT_succ, Nat.succ_mul, bytesAt_add, Offset.add_add, hb₃, ← hb₁,
        show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 192) P.H.D = vOf P L u₂.mem from rfl, hv₂, hk₁, hv₁]
      refine app_eq ?_ rfl
      -- `T`'s first `k` `V`s, kept by the HMAC and the copy.
      rw [bytesAt_frame hf₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
      exact bytesAt_frame hf₂ (fun r hr => by
        simp only [kvW, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hL.stk_SCR (by omega)
        · exact Offset.disjoint_base _ (by omega) (by omega)
        · exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)

/-- If `sh ≠ 0`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
theorem candTop_ok (hL : L.Ok) {c : Cfg} (hcl : c.len = 66) (hcw : c.w = 9) (hsh₁ : c.sh ≠ 0) (hsh₂ : c.sh < 8)
    (he : L.e = 272) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa c.candTop t fun u => Ctx L g lr m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 496, 66⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 496) 66 =
        Spec.Weierstrass.toBytes 66
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 496) 66) >>> c.sh) := by
  rw [Cfg.candTop, ite_eq_right_of_eq_false _ _ (eq_false hsh₁)]
  refine WP.mono (conv_ok hL hcl hcw he hc (o := fT) (s := c.sh) (by decide) (by decide) (by omega) (by omega))
    fun u ⟨hcu, _, hf, hb⟩ => ⟨hcu, hf, hb⟩

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
