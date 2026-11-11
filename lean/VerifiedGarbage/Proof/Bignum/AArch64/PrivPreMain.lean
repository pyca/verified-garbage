module
-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.AArch64.PrivPreR2
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFront
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtUnit
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.PrimeR2
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `vg_rsa_private_precompute` on AArch64: the values

Each prime's `phase` (`phase_ok`) writes `R_X² mod X`, masked, to `pre` at
the cursor and advances it.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.PrivPre

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.PrivPre
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- What a phase may change: the prime's workspace, `n`'s cursor `sD`, and
the `8 l` bytes of `pre` at `op + c`. -/
def PFrm (B : Addr) (rs : List (Nat × Nat)) (op : Addr) (c l : Nat) (m m' : Mem) : Prop :=
  ∀ x, (∀ r ∈ rs, ofs B x < r.1 ∨ r.1 + r.2 ≤ ofs B x) → (ofs op x < c ∨ c + 8 * l ≤ ofs op x) → m' x = m x

/-- A change to `pre` outside the working space keeps the working space. -/
theorem word_of_pre {m m' : Mem} {B op : Addr} {Z cur l d : Nat} (ho : Outside op cur l m m')
    (hsep : ∀ x, ofs B x < Z → ofs op x < cur ∨ cur + l ≤ ofs op x) (hd : d + 8 ≤ Z)
    (hB : B.toNat + Z ≤ 2 ^ 64) : word m' B d = word m B d :=
  Mem.readW_congr fun b hb => (ho _ (hsep _ (by rw [ofs_off B (d := d) (i := b) (by omega_arith)]; omega_arith)))

theorem wv_of_pre {m m' : Mem} {B op : Addr} {Z cur l d k : Nat} (ho : Outside op cur l m m')
    (hsep : ∀ x, ofs B x < Z → ofs op x < cur ∨ cur + l ≤ ofs op x) (hd : d + 8 * k ≤ Z)
    (hB : B.toNat + Z ≤ 2 ^ 64) : wv m' B d k = wv m B d k :=
  wv_congr fun i hi => word_of_pre ho hsep (by omega_arith) hB

theorem pfrm_word {m m' : Mem} {B op : Addr} {rs : List (Nat × Nat)} {Z c l d : Nat} (hf : PFrm B rs op c l m m')
    (hd : ∀ r ∈ rs, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hdZ : d + 8 ≤ Z) (hB : B.toNat + Z ≤ 2 ^ 64)
    (hsep : ∀ x, ofs B x < Z → ofs op x < c ∨ c + 8 * l ≤ ofs op x) : word m' B d = word m B d :=
  Mem.readW_congr fun b hb => by
    have ho : ofs B (off B d + BitVec.ofNat 64 b) = d + b := ofs_off B (by omega_arith)
    exact hf _ (fun r hr => by have := hd r hr; rw [ho]; omega) (hsep _ (by rw [ho]; omega))

theorem pfrm_wv {m m' : Mem} {B op : Addr} {rs : List (Nat × Nat)} {Z c l d k : Nat} (hf : PFrm B rs op c l m m')
    (hd : ∀ r ∈ rs, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) (hdZ : d + 8 * k ≤ Z) (hB : B.toNat + Z ≤ 2 ^ 64)
    (hsep : ∀ x, ofs B x < Z → ofs op x < c ∨ c + 8 * l ≤ ofs op x) : wv m' B d k = wv m B d k :=
  wv_congr fun i hi => pfrm_word hf (fun r hr => by have := hd r hr; omega) (by omega) hB hsep

/-- `pre`'s words outside the part a phase writes are kept. -/
theorem pfrm_pre {m m' : Mem} {B op : Addr} {rs : List (Nat × Nat)} {Z c l e k L : Nat}
    (hf : PFrm B rs op c l m m') (hrZ : ∀ r ∈ rs, r.1 + r.2 ≤ Z) (he : e + 8 * k ≤ c ∨ c + 8 * l ≤ e)
    (hek : e + 8 * k ≤ L) (hL : L ≤ 2 ^ 64) (hsep : ∀ x, ofs B x < Z → L ≤ ofs op x) :
    wv m' op e k = wv m op e k :=
  wv_congr fun i hi => Mem.readW_congr fun b hb => by
    have ho : ofs op (off op (e + 8 * i) + BitVec.ofNat 64 b) = e + 8 * i + b := ofs_off op (by omega_arith)
    refine hf _ (fun r hr => Or.inr ?_) (by rw [ho]; omega)
    have := hrZ r hr
    by_contra hc
    have := hsep (off op (e + 8 * i) + BitVec.ofNat 64 b) (by omega)
    rw [ho] at this
    omega

/-- A prime's `phase`. -/
theorem phase_ok (MM : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {X o wx sl : Nat} {M : Bool}
    {op : Addr} {cur : Nat}
    (hg : Good s B Z w minv) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + wsTab wx ≤ Z)
    (hwx2 : 2 ≤ wx) (hwx : wx < 2 ^ 24) (hwxw : wx ≤ w) (hw24 : w < 2 ^ 24) (hsl : sl < 32)
    (hslv : word s.mem B (8 * sl) = off B o)
    (hP : M = true → X % 2 = 1 ∧ wv s.mem B (slot w Public.aR2) w % X = 2 ^ (128 * w) % X)
    (hws : WsAt s.mem B o wx mx) (hX : XVals s B o wx mx X) (hX1 : 1 < X)
    (hmk : word s.mem B (8 * Public.sMask) = mask M) (hcur : word s.mem B (8 * Crt.sD) = off op cur)
    (hcb : cur + 8 * wx ≤ 2 ^ 64) (hwr : ∀ i < wx, InRegions s.wr (off op (cur + 8 * i)) 8)
    (hsep : ∀ x, ofs B x < Z → ofs op x < cur ∨ cur + 8 * wx ≤ ofs op x) :
    WP isa (seqs (phase MM.mm sl)) s fun t => Good t B Z w minv ∧ WsAt t.mem B o wx mx ∧ XVals t B o wx mx X ∧
      wv t.mem op cur wx = (if M then 2 ^ (128 * wx) % X else 0) ∧
      word t.mem B (8 * Crt.sD) = off op (cur + 8 * wx) ∧
      PFrm B [xRange o wx, (8 * Crt.sD, 8)] op cur wx s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  have ho64 : o < 2 ^ 64 := by omega_arith
  have hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega_arith
  unfold phase
  simp only [List.append_assoc]
  -- Into the prime's workspace.
  refine wp_seqs_append (by simp) (by simp [r2X, Impl.Rsa.AArch64.Crt.redc]) ?_
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = off B o ∧ t.mem = s.mem)
    (by brun [hg.x0, hdr_enc hsl, hs.ld (d := 8 * sl) (by omega_arith), hslv])
    rfl rfl rfl) fun s₁ ⟨⟨h0₁, hm₁⟩, k₁⟩ => ?_
  have hc₁ : SubCtx s₁ B Z o w wx mx :=
    SubCtx.mk' (hs.congr k₁.wr) (by rw [hm₁]; exact hg.hdr) (by rw [hm₁]; exact hws) h0₁ hlo
      (by have := tabBytes_le_wsTab wx; omega_arith)
  have hX₁ : XVals s₁ B o wx mx X := ⟨by rw [hm₁]; exact hX.n, by rw [hm₁]; exact hX.inv, by rw [hm₁]; exact hX.one⟩
  -- `R_X² mod X`.
  refine wp_seqs_append (by simp [r2X, Impl.Rsa.AArch64.Crt.redc]) (by simp) ?_
  refine WP.mono (r2X_ok MM hc₁ hX₁ hwx2 hwxw (by omega) hX1 (P := M = true) (fun hm => by
      rw [hm₁]; exact hP hm)) fun s₂ ⟨hc₂, hX₂, hy₂, f₂, k₂⟩ => ?_
  have hrr := r2Ranges_ok wx
  have fx₂ : Frm B [xRange o wx] s₁.mem s₂.mem := f₂.to_x hrr hoL (List.mem_singleton_self _)
  have hmk₂ : word s₂.mem B (8 * Public.sMask) = mask M := by
    rw [fx₂.x_below (by have := hdr_lt_slot w 8 (show Public.sMask < 32 by decide); omega_arith) ho64, hm₁]
    exact hmk
  have hcur₂ : word s₂.mem B (8 * Crt.sD) = off op cur := by
    rw [fx₂.x_below (by have := hdr_lt_slot w 8 (show Crt.sD < 32 by decide); omega_arith) ho64, hm₁]
    exact hcur
  simp only [seqs]
  -- The cursor, the mask, `w_X` and `Y`'s base.
  refine WP.seq (WP.mono (WP.keep [.x5, .x12, .x15, .x16, .x17] (Q := fun t => t.gpr .x5 = B ∧
      t.gpr .x17 = off op cur ∧ t.gpr .x15 = mask M ∧ t.gpr .x12 = BitVec.ofNat 64 wx ∧
      t.gpr .x16 = off B (o + slot wx Public.aY) ∧ t.mem = s₂.mem)
    (by brun [Impl.Rsa.AArch64.Crt.ldw, hc₂.x0, hdr_enc (show sLink < 32 by decide), hdr_enc (show Public.sMask < 32 by decide),
      hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt (show Public.aY < 8 by decide)),
      hdr_enc (show Crt.sD < 32 by decide),
      hc₂.ld' (show sLink < 32 by decide), hc₂.ldn (show Public.sMask < 32 by decide), hc₂.ld' (show sW < 32 by decide),
      hc₂.ld' (sArr_lt (show Public.aY < 8 by decide)), hc₂.ldn (show Crt.sD < 32 by decide), hc₂.link', hc₂.hw',
      hc₂.harr' (show Public.aY < 8 by decide), hcur₂, hmk₂])
    (by decide) (by decide) (by decide +kernel)) fun s₃ ⟨⟨h5₃, h17₃, h15₃, h12₃, h16₃, hm₃⟩, k₃⟩ => ?_)
  have k03 := (k₁.trans k₂).trans k₃
  have hs₃ : Scr s₃ B Z := hs.congr k03.wr
  have hYs := slot_le (w := wx) (show Public.aY < 8 by decide)
  have hYb : o + slot wx Public.aY + 8 * wx ≤ Z := by omega_arith
  -- The masked copy.
  have hsepC : ∀ j < wx, ∀ b < 8, ofs op (off B (o + slot wx Public.aY + 8 * j) + BitVec.ofNat 64 b) < cur ∨
      cur + 8 * wx ≤ ofs op (off B (o + slot wx Public.aY + 8 * j) + BitVec.ofNat 64 b) := fun j hj b hb =>
    hsep _ (by rw [ofs_off B (d := o + slot wx Public.aY + 8 * j) (i := b) (by omega_arith)]; omega_arith)
  have hmc := maskCopy_ok (S := B) (D := op) (eS := o + slot wx Public.aY) (eD := cur) (w := wx)
    h16₃ h17₃ h12₃ (by omega) (by omega_arith) hcb (fun j hj => hs₃.ld (by omega_arith))
    (fun i hi => by rw [k03.wr]; exact hwr i hi) hsepC
  refine WP.seq (WP.mono hmc fun s₄ ⟨hv₄, ho₄, _, h17₄, k₄⟩ => ?_)
  have hB : B.toNat + Z ≤ 2 ^ 64 := hn
  have hw₄ : ∀ d, d + 8 ≤ Z → word s₄.mem B d = word s₃.mem B d := fun d hd => word_of_pre ho₄ hsep hd hB
  -- The cursor back, and out of the prime's workspace.
  have hl₄ : word s₄.mem B (o + 8 * sLink) = B := by
    rw [hw₄ _ (by unfold sLink sFn; omega_arith), hm₃]; exact hc₂.link'
  have hl₄' : (s₄.mem.writeW (B + BitVec.ofNat 64 (8 * Crt.sD)) (off op (cur + 8 * wx))).readW
      (off B (o + 8 * sLink)) 64 = B := by
    have := (writeW_outside s₄.mem B (d := 8 * Crt.sD) (off op (cur + 8 * wx)) (by unfold Crt.sD sFn; omega)).word
      (d := o + 8 * sLink) (Or.inr (by have := hdr_lt_slot w 8 (show Crt.sD < 32 by decide); omega_arith))
      (by unfold sLink sFn; omega_arith)
    exact this.trans hl₄
  have h0₄ : s₄.gpr .x0 = off B o := ((k₃.trans k₄).gpr .x0 (by decide)).trans hc₂.x0
  refine WP.mono (WP.keep [.x0, .x5] (Q := fun t => t.gpr .x0 = B ∧
      t.mem = s₄.mem.writeW (off B (8 * Crt.sD)) (off op (cur + 8 * wx)))
    (by brun [Impl.Rsa.AArch64.Crt.stw, leave, h0₄, hdr_enc (show sLink < 32 by decide),
      hdr_enc (show Crt.sD < 32 by decide),
      (hs.congr (k03.trans k₄).wr).ld (d := o + 8 * sLink) (by unfold sLink sFn; omega_arith),
      (hs.congr (k03.trans k₄).wr).st (d := 8 * Crt.sD) (by
        have := hdr_lt_slot w 8 (show Crt.sD < 32 by decide); omega_arith), hl₄, hl₄', h17₄, off_off])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h0, hm⟩, k'⟩ => ?_
  have kall := ((k03.trans k₄).trans k')
  have hsD : 8 * Crt.sD + 8 ≤ slot w 8 := hdr_lt_slot w 8 (show Crt.sD < 32 by decide)
  have oT : Outside B (8 * Crt.sD) 8 s₄.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by unfold Crt.sD sFn; omega)
  -- Words of the working space, but the cursor, as they were before the copy.
  have hwT : ∀ d, d + 8 ≤ Z → (d + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ d) →
      word t.mem B d = word s₂.mem B d := fun d hd hd' => by
    rw [oT.word hd' (by omega_arith), hw₄ d hd, hm₃]
  have hb : ∀ d, d + 8 ≤ 8 * Crt.sD → word t.mem B d = word s.mem B d := fun d hd => by
    rw [hwT d (by omega_arith) (Or.inl hd), fx₂.x_below (by omega_arith) ho64, hm₁]
  have hH : Hdr t.mem B w minv := by
    have hH := hg.hdr
    exact ⟨(hb _ (by unfold sW Crt.sD sFn; omega)).trans hH.hw, (hb _ (by unfold sMinv Crt.sD sFn; omega)).trans hH.hminv,
      fun j hj => (hb _ (by unfold sArr Crt.sD sFn; omega)).trans (hH.harr j hj)⟩
  have hxw : ∀ d, d + 8 ≤ slot wx 8 → word t.mem (off B o) d = word s₂.mem (off B o) d := fun d hd => by
    rw [word_off, word_off, hwT _ (by omega_arith) (Or.inr (by omega_arith))]
  have hxv : ∀ d k, d + 8 * k ≤ slot wx 8 → wv t.mem (off B o) d k = wv s₂.mem (off B o) d k := fun d k hd =>
    wv_congr fun i hi => hxw _ (by omega_arith)
  have hN := slot_le (w := wx) (show Public.aN < 8 by decide)
  have hO := slot_le (w := wx) (show Public.aOne < 8 by decide)
  have hnw : (off B o).toNat + slot wx 8 ≤ 2 ^ 64 := hc₁.good.scr.nowrap
  refine ⟨⟨hs.congr kall.wr, h0, hH⟩, hc₂.ws.of_words fun i hi => hxw _ (by unfold slot hdrBytes; omega), ⟨?_, ?_, ?_⟩,
    ?_, by rw [hm, word_writeW_self], ?_, ?_⟩
  · rw [hxv _ _ (by omega_arith)]; exact hX₂.n
  · rw [hxw _ (by omega_arith)]; exact hX₂.inv
  · rw [hxv _ _ (by omega_arith)]; exact hX₂.one
  · have hpre : ∀ i < wx, word t.mem op (cur + 8 * i) = word s₄.mem op (cur + 8 * i) := fun i hi =>
      Mem.readW_congr fun b hb => by
        rw [hm]
        refine writeW_outside s₄.mem B _ (by unfold Crt.sD sFn; omega) _ (Or.inr ?_)
        by_contra hc
        have := hsep _ (Nat.lt_of_lt_of_le (Nat.lt_of_not_le hc) (by omega_arith))
        rw [ofs_off op (d := cur + 8 * i) (i := b) (by omega_arith)] at this
        omega
    rw [wv_congr hpre, wv_mask (S := B) (eS := o + slot wx Public.aY) (fun i hi => by rw [hv₄ i hi, h15₃]),
      hm₃, ← wv_off]
    cases M
    · rfl
    · exact hy₂ rfl
  · intro x hx hp
    rw [hm, writeW_outside s₄.mem B _ (by unfold Crt.sD sFn; omega) x
      (hx _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))), ho₄ x hp, hm₃,
      fx₂ x (fun r hr => hx r (by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self)), hm₁]
  · refine ⟨fun r hr => ?_, kall.rd, kall.wr, kall.sp, kall.vcs⟩
    by_cases h : r = .x0
    · subst h; rw [h0, hg.x0]
    · exact kall.gpr r (by revert hr h; cases r <;> decide)

/-! ## `n`'s values -/

theorem and_one_mask (c : Bool) : mask c &&& BitVec.setWidth 64 1#16 = BitVec.ofNat 64 c.toNat := by
  cases c <;> decide

/-- `outN`: `n` and `R² mod n`, masked, to `pre`, and the mask's low bit
returned. -/
theorem outN_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat} {M : Bool} {op : Addr}
    (hg : Good t B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 28) (hN : NVals t B w minv N)
    (hmk : word t.mem B (8 * Public.sMask) = mask M) (hO : word t.mem B (8 * Public.sOut) = op)
    (hwr : ∀ i < 2 * w, InRegions t.wr (off op (8 * i)) 8)
    (hsep : ∀ x, ofs B x < Z → 16 * w ≤ ofs op x) :
    WP isa (seqs outN) t fun u =>
      wv u.mem op 0 w = (if M then N else 0) ∧
      wv u.mem op (8 * w) w = (if M then 2 ^ (64 * w) * 2 ^ (64 * w) % N else 0) ∧
      u.gpr .x0 = BitVec.ofNat 64 M.toNat ∧ Outside op 0 (16 * w) t.mem u.mem ∧ Keep (.x0 :: mmRegs) t u := by
  have hs := hg.scr
  have hn := hs.nowrap
  have hsN := slot_le (w := w) (show Public.aN < 8 by decide)
  have hsR := slot_le (w := w) (show Public.aR2 < 8 by decide)
  have hsepC : ∀ (e j : Nat), e + 8 * j + 8 ≤ Z → ∀ b < 8, ∀ c l, c + l ≤ 16 * w →
      ofs op (off B (e + 8 * j) + BitVec.ofNat 64 b) < c ∨ c + l ≤ ofs op (off B (e + 8 * j) + BitVec.ofNat 64 b) :=
    fun e j hj b hb c l hcl => Or.inr (by
      have := hsep _ (by rw [ofs_off B (d := e + 8 * j) (i := b) (by omega_arith)]; omega_arith); omega_arith)
  simp only [outN, seqs]
  refine WP.seq (WP.mono (WP.keep [.x12, .x15, .x16, .x17] (Q := fun u => u.gpr .x15 = mask M ∧
      u.gpr .x12 = BitVec.ofNat 64 w ∧ u.gpr .x16 = off B (slot w Public.aN) ∧ u.gpr .x17 = op ∧
      u.mem = t.mem)
    (by brun [hg.x0, hdr_enc (show Public.sMask < 32 by decide), hdr_enc (show sW < 32 by decide),
      hdr_enc (sArr_lt (show Public.aN < 8 by decide)), hdr_enc (show Public.sOut < 32 by decide),
      hg.ld hZ (show Public.sMask < 32 by decide), hg.ld hZ (show sW < 32 by decide),
      hg.ld hZ (sArr_lt (show Public.aN < 8 by decide)), hg.ld hZ (show Public.sOut < 32 by decide),
      hmk, hg.hdr.hw, hg.hdr.harr Public.aN (by decide), hO])
    (by decide) (by decide) (by decide +kernel)) fun u₁ ⟨⟨h15₁, h12₁, h16₁, h17₁', hm₁⟩, k₁⟩ => ?_)
  have h17₁ : u₁.gpr .x17 = off op 0 := by rw [h17₁']; simp [off]
  have hs₁ : Scr u₁ B Z := hs.congr k₁.wr
  refine WP.seq (WP.mono (maskCopy_ok (S := B) (D := op) (eS := slot w Public.aN) (eD := 0) (w := w)
    h16₁ h17₁ h12₁ (by omega) (by omega_arith) (by omega_arith) (fun j hj => hs₁.ld (by omega_arith))
    (fun i hi => by rw [k₁.wr, Nat.zero_add]; exact hwr i (by omega))
    (fun j hj b hb => hsepC _ j (by omega_arith) b hb 0 (8 * w) (by omega)))
    fun u₂ ⟨hv₂, ho₂, _, h17₂, k₂⟩ => ?_)
  have hsep₂ : ∀ x, ofs B x < Z → ofs op x < 0 ∨ 0 + 8 * w ≤ ofs op x := fun x hx =>
    Or.inr (by have := hsep x hx; omega)
  have hw₂ : ∀ d, d + 8 ≤ Z → word u₂.mem B d = word t.mem B d := fun d hd => by
    rw [word_of_pre ho₂ hsep₂ hd hn, hm₁]
  have k12 := k₁.trans k₂
  have h0₂ : u₂.gpr .x0 = B := (k12.gpr .x0 (by decide)).trans hg.x0
  refine WP.seq (WP.mono (WP.keep [.x16] (Q := fun u => u.gpr .x16 = off B (slot w Public.aR2) ∧ u.mem = u₂.mem)
    (by brun [h0₂, hdr_enc (sArr_lt (show Public.aR2 < 8 by decide)),
      (hs.congr k12.wr).ld (d := 8 * sArr Public.aR2) (by have := hdr_lt_slot w 8 (sArr_lt (show Public.aR2 < 8 by decide)); omega_arith),
      hw₂ _ (show 8 * sArr Public.aR2 + 8 ≤ Z by
        have := hdr_lt_slot w 8 (sArr_lt (show Public.aR2 < 8 by decide)); omega_arith),
      hg.hdr.harr Public.aR2 (by decide)])
    (by decide) (by decide) (by decide +kernel)) fun u₃ ⟨⟨h16₃, hm₃⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  have hs₃ : Scr u₃ B Z := hs.congr k13.wr
  have h17₃ : u₃.gpr .x17 = off op (8 * w) := by rw [k₃.gpr .x17 (by decide), h17₂, Nat.zero_add]
  have h12₃ : u₃.gpr .x12 = BitVec.ofNat 64 w := by rw [(k₂.trans k₃).gpr .x12 (by decide), h12₁]
  refine WP.seq (WP.mono (maskCopy_ok (S := B) (D := op) (eS := slot w Public.aR2) (eD := 8 * w) (w := w)
    h16₃ h17₃ h12₃ (by omega) (by omega_arith) (by omega_arith) (fun j hj => hs₃.ld (by omega_arith))
    (fun i hi => by rw [k13.wr, show 8 * w + 8 * i = 8 * (w + i) by omega]; exact hwr _ (by omega))
    (fun j hj b hb => hsepC _ j (by omega_arith) b hb (8 * w) (8 * w) (by omega)))
    fun u₄ ⟨hv₄, ho₄, _, _, k₄⟩ => ?_)
  have hsep₄ : ∀ x, ofs B x < Z → ofs op x < 8 * w ∨ 8 * w + 8 * w ≤ ofs op x := fun x hx =>
    Or.inr (by have := hsep x hx; omega)
  have k14 := k13.trans k₄
  have h0₄ : u₄.gpr .x0 = B := (k14.gpr .x0 (by decide)).trans hg.x0
  have hmk₄ : word u₄.mem B (8 * Public.sMask) = mask M := by
    rw [word_of_pre ho₄ hsep₄ (show 8 * Public.sMask + 8 ≤ Z by
      have := hdr_lt_slot w 8 (show Public.sMask < 32 by decide); omega_arith) hn, hm₃,
      hw₂ _ (show 8 * Public.sMask + 8 ≤ Z by have := hdr_lt_slot w 8 (show Public.sMask < 32 by decide); omega_arith)]
    exact hmk
  refine WP.mono (WP.keep [.x0, .x3] (Q := fun u => u.gpr .x0 = BitVec.ofNat 64 M.toNat ∧ u.mem = u₄.mem)
    (by brun [h0₄, hdr_enc (show Public.sMask < 32 by decide),
      (hs.congr k14.wr).ld (d := 8 * Public.sMask) (by have := hdr_lt_slot w 8 (show Public.sMask < 32 by decide); omega_arith),
      hmk₄, and_one_mask])
    (by decide) (by decide) (by decide +kernel)) fun u ⟨⟨h0, hm⟩, k'⟩ => ?_
  have hR2 : wv u₃.mem B (slot w Public.aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [hm₃, wv_of_pre ho₂ hsep₂ (by omega_arith) hn, hm₁, ← hN.r2, Nat.mod_eq_of_lt hN.r2lt]
  refine ⟨?_, ?_, h0, ?_, ?_⟩
  · rw [hm, ho₄.wv (Or.inl (by omega)) (by omega_arith), hm₃,
      wv_mask (S := B) (eS := slot w Public.aN) (fun i hi => by rw [hv₂ i hi, h15₁]), hm₁, hN.n]
  · have h15₃ : u₃.gpr .x15 = mask M := by rw [(k₂.trans k₃).gpr .x15 (by decide), h15₁]
    rw [hm, wv_mask (S := B) (eS := slot w Public.aR2) (fun i hi => by rw [hv₄ i hi, h15₃]), hR2]
  · intro x hx
    rw [hm, ho₄ x (by omega), hm₃, ho₂ x (by omega), hm₁]
  · refine ⟨fun r hr => ?_, (k14.trans k').rd, (k14.trans k').wr, (k14.trans k').sp, (k14.trans k').vcs⟩
    exact (k14.trans k').gpr r (by revert hr; cases r <;> decide)

/-! ## After the checks -/

/-- The modulus' values, kept by what keeps the words of its arrays. -/
theorem nvals_of_words {s t : State} {B : Addr} {w : Nat} {minv : BitVec 64} {N : Nat} (h : NVals s B w minv N)
    (hw : ∀ d, d + 8 ≤ slot w 8 → 256 ≤ d → word t.mem B d = word s.mem B d) : NVals t B w minv N := by
  have hv : ∀ j < 8, wv t.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj =>
    wv_congr fun i hi => hw _ (by have := slot_le (w := w) hj; omega) (by unfold slot hdrBytes; omega)
  exact ⟨by rw [hv _ (by decide)]; exact h.n,
    by rw [hw _ (by have := slot_le (w := w) (show Public.aN < 8 by decide); omega)
      (by unfold slot hdrBytes; omega)]; exact h.inv,
    by rw [hv _ (by decide)]; exact h.r2, by rw [hv _ (by decide)]; exact h.r2lt,
    by rw [hv _ (by decide)]; exact h.one⟩

/-- A prime's values, kept by what keeps the words of its arrays. -/
theorem xvals_of_words {s t : State} {B : Addr} {o wx : Nat} {mx : BitVec 64} {X : Nat} (h : XVals s B o wx mx X)
    (hw : ∀ d, d + 8 ≤ slot wx 8 → 256 ≤ d → word t.mem B (o + d) = word s.mem B (o + d)) :
    XVals t B o wx mx X := by
  have hv : ∀ j < 8, wv t.mem (off B o) (slot wx j) wx = wv s.mem (off B o) (slot wx j) wx := fun j hj => by
    rw [wv_off, wv_off]
    exact wv_congr fun i hi => by
      rw [show o + slot wx j + 8 * i = o + (slot wx j + 8 * i) by omega]
      exact hw _ (by have := slot_le (w := wx) hj; omega) (by unfold slot hdrBytes; omega)
  exact ⟨by rw [hv _ (by decide)]; exact h.n,
    by
      have hi := h.inv
      rw [word_off] at hi ⊢
      rw [hw _ (by have := slot_le (w := wx) (show Public.aN < 8 by decide); omega)
        (by unfold slot hdrBytes; omega)]; exact hi,
    by rw [hv _ (by decide)]; exact h.one⟩

theorem if3_gt {M : Bool} {P : Nat} (h : M = true → 1 < P) : 1 < if M then P else 3 := by
  cases M
  · simp
  · exact h rfl

theorem if3_r2 (M : Bool) (P k : Nat) :
    (if M then k % (if M then P else 3) else 0) = if M then k % P else 0 := by cases M <;> rfl

/-- `primes` and `outN`, from what `Crt.checks` leaves. -/
theorem tail_ok (MM : Mont) {s₀ t : State} {B : Addr} {Z w pl ql : Nat} {minv mp mq : BitVec 64} {N C P Q : Nat} {M : Bool}
    {op : Addr} (h : CrtReady s₀ t B Z w pl ql minv mp mq N C P Q M) (hw8 : 8 ≤ w) (hw24 : w < 2 ^ 24)
    (hz : offQ w pl + slot (wsWords ql) 8 + wsTab (wsWords ql) ≤ Z) (hpw : wsWords pl ≤ w)
    (hqw : wsWords ql ≤ w) (hO : word t.mem B (8 * Public.sOut) = op) (hP1 : M = true → 1 < P)
    (hQ1 : M = true → 1 < Q) (hNo : N % 2 = 1) (hPQ : M = true → P * Q = N)
    (hwr : ∀ i < 2 * w + wsWords pl + wsWords ql, InRegions t.wr (off op (8 * i)) 8)
    (hL : 8 * (2 * w + wsWords pl + wsWords ql) ≤ 2 ^ 64)
    (hsep : ∀ x, ofs B x < Z → 8 * (2 * w + wsWords pl + wsWords ql) ≤ ofs op x) :
    WP isa (seqs (primes MM.mm ++ outN)) t fun u =>
      wv u.mem op 0 w = (if M then N else 0) ∧
      wv u.mem op (8 * w) w = (if M then 2 ^ (64 * w) * 2 ^ (64 * w) % N else 0) ∧
      wv u.mem op (16 * w) (wsWords pl) = (if M then 2 ^ (128 * wsWords pl) % P else 0) ∧
      wv u.mem op (16 * w + 8 * wsWords pl) (wsWords ql) = (if M then 2 ^ (128 * wsWords ql) % Q else 0) ∧
      u.gpr .x0 = BitVec.ofNat 64 M.toNat ∧
      (∀ x, Z ≤ ofs B x → 8 * (2 * w + wsWords pl + wsWords ql) ≤ ofs op x → u.mem x = t.mem x) ∧
      Keep (.x0 :: mmRegs) t u := by
  have hg := h.good
  have hs := hg.scr
  have hn := hs.nowrap
  have hsD : 8 * Crt.sD + 8 ≤ slot w 8 := hdr_lt_slot w 8 (show Crt.sD < 32 by decide)
  have hp2 : 2 ≤ wsWords pl := by unfold wsWords; omega
  have hq2 : 2 ≤ wsWords ql := by unfold wsWords; omega
  have hZ8 : slot w 8 ≤ Z := by unfold offQ at hz; omega
  have hwp24 : wsWords pl < 2 ^ 24 := by omega
  have hwq24 : wsWords ql < 2 ^ 24 := by omega
  have eQ : offQ w pl = offP w + slot (wsWords pl) 8 + wsTab (wsWords pl) := rfl
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega
  have hPZ : offP w + slot (wsWords pl) 8 + wsTab (wsWords pl) + slot (wsWords ql) 8 + wsTab (wsWords ql) ≤ Z := by
    rw [← eQ]; exact hz
  have hoP : offP w = slot w 8 := rfl
  have hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega
  have hZ64 : Z ≤ 2 ^ 64 := by omega
  have hQlo : slot w 8 ≤ offQ w pl := by omega
  simp only [primes, List.append_assoc]
  -- The cursor.
  refine wp_seqs_append (by simp) (by simp [phase]) ?_
  refine WP.mono (WP.keep [.x4, .x17] (Q := fun u =>
      u.mem = t.mem.writeW (off B (8 * Crt.sD)) (off op (16 * w)))
    (by brun [setCursor, hg.x0, hdr_enc (show Public.sOut < 32 by decide), hdr_enc (show sW < 32 by decide),
      hdr_enc (show Crt.sD < 32 by decide), hg.ld hZ8 (show Public.sOut < 32 by decide),
      hg.ld hZ8 (show sW < 32 by decide), hs.st (d := 8 * Crt.sD) (by omega), hO, hg.hdr.hw,
      shl_ofNat (show w * 2 ^ 4 < 2 ^ 64 by omega), show w * 2 ^ 4 = 16 * w by omega, off])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have oT₁ : Outside B (8 * Crt.sD) 8 t.mem t₁.mem := by
    rw [hm₁]; exact writeW_outside _ _ _ (by unfold Crt.sD sFn; omega)
  -- Words of the working space above `n`'s header are kept by the cursor.
  have hw₁ : ∀ d, 8 * Crt.sD + 8 ≤ d → d + 8 ≤ 2 ^ 64 → word t₁.mem B d = word t.mem B d := fun d hd hd' =>
    oT₁.word (Or.inr hd) hd'
  have hg₁ : Good t₁ B Z w minv := ⟨hs.congr k₁.wr, (k₁.gpr .x0 (by decide)).trans hg.x0, by
    rw [hm₁]; exact Hdr.store hg.hdr (by decide) (by decide) _⟩
  have hslP : word t₁.mem B (8 * sWsP) = off B (offP w) := by
    rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact h.wsP
  have hslQ : word t₁.mem B (8 * sWsQ) = off B (offQ w pl) := by
    rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact h.wsQ
  have hwsP : WsAt t₁.mem B (offP w) (wsWords pl) mp := h.pws.of_words fun i hi => by
    rw [word_off, word_off, hw₁ _ (by omega_arith) (by omega_arith)]
  have hwsQ : WsAt t₁.mem B (offQ w pl) (wsWords ql) mq := h.qws.of_words fun i hi => by
    rw [word_off, word_off, hw₁ _ (by omega) (by omega)]
  have hxP : XVals t₁ B (offP w) (wsWords pl) mp (if M then P else 3) := xvals_of_words h.pxv fun d hd hd' =>
    hw₁ _ (by omega_arith) (by omega_arith)
  have hxQ : XVals t₁ B (offQ w pl) (wsWords ql) mq (if M then Q else 3) := xvals_of_words h.qxv fun d hd hd' =>
    hw₁ _ (by omega) (by omega)
  have hmk₁ : word t₁.mem B (8 * Public.sMask) = mask M := by
    rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact h.msk
  have hN₁ : NVals t₁ B w minv N := nvals_of_words h.nv fun d hd hd' =>
    hw₁ _ (by unfold Crt.sD sFn; omega) (by omega)
  -- `p`.
  refine wp_seqs_append (by simp [phase]) (by simp [phase]) ?_
  refine WP.mono (phase_ok MM (sl := sWsP) (op := op) (cur := 16 * w) hg₁ (by unfold offP; omega) (by rw [← eQ]; unfold offQ at hz ⊢; omega) hp2 hwp24
    hpw hw24 (by decide) hslP (fun hm => by
      simp only [hm, ite_true]
      exact ⟨odd_of_dvd hNo ⟨Q, (hPQ hm).symm⟩, r2_of_dvd ⟨Q, (hPQ hm).symm⟩ hN₁.r2⟩) hwsP hxP (if3_gt hP1) hmk₁ (by rw [hm₁, word_writeW_self]) (by omega)
    (fun i hi => by rw [k₁.wr, show 16 * w + 8 * i = 8 * (2 * w + i) by omega]; exact hwr _ (by omega))
    (fun x hx => Or.inr (by have := hsep x hx; omega))) fun t₂ ⟨hg₂, _, _, hvP, hc₂, f₂, k₂⟩ => ?_
  have hsep₂ : ∀ x, ofs B x < Z → ofs op x < 16 * w ∨ 16 * w + 8 * wsWords pl ≤ ofs op x := fun x hx =>
    Or.inr (by have := hsep x hx; omega)
  have hrs₂ : ∀ d, d + 8 ≤ Z → (d + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ d) →
      (d + 8 ≤ offP w + 8 * 17 ∨ offQ w pl ≤ d) → word t₂.mem B d = word t₁.mem B d := fun d hd h1 h2 =>
    pfrm_word f₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [xRange]; rw [eQ] at h2; omega
      · exact h1) hd hn hsep₂
  have hslQ₂ : word t₂.mem B (8 * sWsQ) = off B (offQ w pl) := by
    rw [hrs₂ _ (by unfold sWsQ Crt.sD sFn at *; omega) (Or.inl (by unfold sWsQ Crt.sD sFn; omega))
      (Or.inl (by unfold sWsQ Crt.sD sFn at *; omega))]
    exact hslQ
  have hmk₂ : word t₂.mem B (8 * Public.sMask) = mask M := by
    rw [hrs₂ _ (by unfold Public.sMask Crt.sD sFn at *; omega) (Or.inl (by unfold Public.sMask Crt.sD sFn; omega))
      (Or.inl (by unfold Public.sMask Crt.sD sFn at *; omega))]
    exact hmk₁
  have hwsQ₂ : WsAt t₂.mem B (offQ w pl) (wsWords ql) mq := hwsQ.of_words fun i hi => by
    rw [word_off, word_off, hrs₂ _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))]
  have hxQ₂ : XVals t₂ B (offQ w pl) (wsWords ql) mq (if M then Q else 3) := xvals_of_words hxQ fun d hd hd' =>
    hrs₂ _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
  have hN₂ : NVals t₂ B w minv N := nvals_of_words hN₁ fun d hd hd' =>
    hrs₂ d (by omega) (Or.inr (by unfold Crt.sD sFn; omega)) (Or.inl (by unfold offP; omega))
  have hdQ : M = true → Q ∣ N := fun hm => ⟨P, by rw [Nat.mul_comm]; exact (hPQ hm).symm⟩
  -- `q`.
  refine wp_seqs_append (by simp [phase]) (by simp [outN]) ?_
  refine WP.mono (phase_ok MM (sl := sWsQ) (op := op) (cur := 16 * w + 8 * wsWords pl) hg₂ hQlo hz hq2 hwq24
    hqw hw24 (by decide) hslQ₂ (fun hm => by
      simp only [hm, ite_true]
      exact ⟨odd_of_dvd hNo (hdQ hm), r2_of_dvd (hdQ hm) hN₂.r2⟩) hwsQ₂ hxQ₂ (if3_gt hQ1) hmk₂ hc₂ (by omega)
    (fun i hi => by
      rw [(k₁.trans k₂).wr, show 16 * w + 8 * wsWords pl + 8 * i = 8 * (2 * w + wsWords pl + i) by omega]
      exact hwr _ (by omega))
    (fun x hx => Or.inr (by have := hsep x hx; omega))) fun t₃ ⟨hg₃, _, _, hvQ, _, f₃, k₃⟩ => ?_
  have hsep₃ : ∀ x, ofs B x < Z → ofs op x < 16 * w + 8 * wsWords pl ∨
      16 * w + 8 * wsWords pl + 8 * wsWords ql ≤ ofs op x := fun x hx =>
    Or.inr (by have := hsep x hx; omega)
  -- `n`'s words (below the primes' workspaces, but the cursor) are kept.
  have hn₃ : ∀ d, d + 8 ≤ slot w 8 → (d + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ d) →
      word t₃.mem B d = word t.mem B d := fun d hd h1 => by
    rw [pfrm_word f₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simp only [xRange]; omega
        · exact h1) (by omega) hn hsep₃,
      hrs₂ _ (by omega) h1 (Or.inl (by omega))]
    rcases h1 with h1 | h1
    · rw [hm₁, (writeW_outside t.mem B _ (by unfold Crt.sD sFn; omega)).word (Or.inl h1) (by omega)]
    · exact hw₁ _ h1 (by omega)
  have hN₃ : NVals t₃ B w minv N := nvals_of_words h.nv fun d hd hd' =>
    hn₃ d hd (Or.inr (by unfold Crt.sD sFn; omega))
  have hslot₃ : ∀ i < 31, word t₃.mem B (8 * i) = word t.mem B (8 * i) := fun i hi =>
    hn₃ _ (by have := hdr_lt_slot w 8 (show i < 32 by omega); omega) (Or.inl (by unfold Crt.sD sFn; omega))
  have kall₃ := (k₁.trans k₂).trans k₃
  refine WP.mono (outN_ok (op := op) (M := M) hg₃ hZ8 (by omega) (by omega) hN₃
    ((hslot₃ _ (by decide)).trans h.msk) ((hslot₃ _ (by decide)).trans hO)
    (fun i hi => by rw [kall₃.wr]; exact hwr i (by omega)) (fun x hx => by have := hsep x hx; omega))
    fun u ⟨hvN, hvR, h0, ho, k'⟩ => ?_
  have hrZ : ∀ r ∈ [xRange (offQ w pl) (wsWords ql), (8 * Crt.sD, 8)], r.1 + r.2 ≤ Z := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl)
    · simp only [xRange]; omega
    · simp only; omega
  have hrZ₂ : ∀ r ∈ [xRange (offP w) (wsWords pl), (8 * Crt.sD, 8)], r.1 + r.2 ≤ Z := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl)
    · simp only [xRange]; omega
    · simp only; omega
  refine ⟨hvN, hvR, ?_, ?_, h0, fun x hx hp => ?_, (((k₁.trans k₂).trans k₃).trans k').mono (by decide)⟩
  · rw [ho.wv (Or.inr (by omega)) (by omega),
      pfrm_pre f₃ hrZ (Or.inl (Nat.le_refl _)) (by omega) hL hsep, hvP, if3_r2]
  · rw [ho.wv (Or.inr (by omega)) (by omega), hvQ, if3_r2]
  · rw [ho x (Or.inr (by omega)), f₃ x (fun r hr => Or.inr (by have := hrZ r hr; omega)) (Or.inr (by omega)),
      f₂ x (fun r hr => Or.inr (by have := hrZ₂ r hr; omega)) (Or.inr (by omega)),
      oT₁ x (Or.inr (by omega))]

end VG.Proof.Bignum.AArch64.PrivPre
