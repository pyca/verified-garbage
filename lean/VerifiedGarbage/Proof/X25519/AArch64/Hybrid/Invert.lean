module

public import VerifiedGarbage.Proof.X25519.AArch64.Hybrid.Exec
public import VerifiedGarbage.Impl.X25519.AArch64.Invert
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Pow
public import VerifiedGarbage.Proof.Mont.AArch64.Ops
public import VerifiedGarbage.Proof.X25519.Invert
public import VerifiedGarbage.Proof.X25519.Field
public import VerifiedGarbage.Proof.Ed25519.AArch64.Field
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import VerifiedGarbage.Proof.X25519.AArch64.Hybrid.InvSound
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# X25519 on AArch64: the inversion by divsteps

Untrusted: everything here is checked by Lean. `Invert.invert` leaves
`[slot 15] ≡ [slot 2]^(p - 2)` (`invert_ok`), from the Montgomery products'
(`Mont.AArch64.mul_ok`) and the divsteps' (`invSound`) proofs.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Hybrid

open VG VG.AArch64
open VG.Impl.X25519.AArch64.Invert (TBL BASE ACC R2 ONE SX1 M cfg storeConst pre post)
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- X25519's working space, for the Montgomery arithmetic. -/
theorem mscr {s : State} {base : Addr} (hs : Scratch s base) : VG.Proof.Mont.AArch64.Scr s base 4096 :=
  ⟨hs.x0, hs.wr, hs.nowrap, by decide⟩

theorem M_mo : M.mo = 4032 := rfl
theorem M_tmp : M.tmp = 4000 := rfl
theorem M_n : M.n = 4 := rfl

/-- `[o] = v` (four words). -/
theorem storeConst_ok {s : State} {base : Addr} (hs : VG.Proof.Mont.AArch64.Scr s base 4096) {o : Nat} (v : Nat)
    (ho : o + 32 ≤ 4096) (h8 : o % 8 = 0) (hv : v < 2 ^ 256) :
    WP isa (.block (storeConst o v)) s fun t =>
      VG.Proof.Mont.wordsVal t.mem base o 4 = v ∧ VG.Proof.Mont.Outside base o 32 s.mem t.mem ∧
      VG.Proof.Mont.AArch64.KeepRegs [.x2] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, VG.Proof.Mont.word t.mem base (o + 8 * j) = BitVec.ofNat 64 (v >>> (64 * j))) ∧
    VG.Proof.Mont.Outside base o 32 s.mem t.mem ∧ VG.Proof.Mont.AArch64.KeepRegs [.x2] s t
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) inv (fun n t hn ⟨tw, tO, tk⟩ => ?_) 4 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), VG.Proof.Mont.Outside.refl _ _ _ _,
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩) fun t ⟨tw, tO, tk⟩ => ⟨?_, tO, tk⟩
  · have ts : VG.Proof.Mont.AArch64.Scr t base 4096 :=
      ⟨(tk.gpr _ (by decide)).trans hs.x0, tk.wr ▸ hs.wr, hs.nowrap, hs.enc⟩
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Mont.AArch64.const64_ok t .x2 _) fun a ⟨a2, ka⟩ => ?_
    have as : VG.Proof.Mont.AArch64.Scr a base 4096 := ts.of_keeps ka (by decide)
    refine WP.mono (VG.Proof.Mont.AArch64.st_ok as (d := o + 8 * n) (by omega) (by omega) .x2) fun b hb => ?_
    subst hb
    refine ⟨fun j hj => ?_, ?_, ?_⟩
    · by_cases h : j = n
      · subst h; rw [VG.Proof.Mont.word_writeW_self, a2]
      · rw [(VG.Proof.Mont.writeW_outside a.mem base (a.gpr .x2) (d := o + 8 * n) (by omega)).word (by omega)
          (by omega), ka.mem]
        exact tw j (by omega)
    · exact (tO.trans (by rw [show a.mem = t.mem from ka.mem]; exact VG.Proof.Mont.Outside.refl _ _ _ _)).trans
        ((VG.Proof.Mont.writeW_outside _ base _ (by omega)).mono (by omega) (by omega))
    · exact ⟨fun r hr => (ka.gpr r hr).trans (tk.gpr r hr), ka.rd.trans tk.rd, ka.wr.trans tk.wr,
        ka.sp.trans tk.sp⟩
  · have w0 := tw 0 (by decide); have w1 := tw 1 (by decide)
    have w2 := tw 2 (by decide); have w3 := tw 3 (by decide)
    simp only [VG.Proof.Mont.wordsVal, Nat.mul_zero, Nat.add_zero, Nat.mul_one] at w0 w1 w2 w3 ⊢
    simp only [show o + 8 + 8 = o + 16 by omega, show o + 16 + 8 = o + 24 by omega] at *
    rw [w0, w1, w2, w3]
    simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega

/-- Slot `o`'s four words, as the Montgomery arithmetic reads them. -/
theorem fe_wordsVal (m : Mem) (base : Addr) (o : Nat) :
    VG.Proof.Ed25519.AArch64.fe m base o = VG.Proof.Mont.wordsVal m base o 4 := by
  simp only [VG.Proof.Ed25519.AArch64.fe, VG.Proof.Mont.wordsVal, VG.Proof.Ed25519.AArch64.word,
    VG.Proof.Mont.word, VG.Proof.Ed25519.AArch64.off, VG.Proof.Mont.off, Nat.add_zero, Nat.mul_zero]
  rw [show o + 8 + 8 = o + 16 by omega, show o + 16 + 8 = o + 24 by omega]
  simp only [VG.Proof.Ed25519.Word64.val4]
  omega

/-- The modulus `p` at `M.mo`, as the Montgomery arithmetic needs it. -/
theorem modOk {m : Mem} {base : Addr} (h : VG.Proof.Mont.wordsVal m base M.mo 4 = Spec.X25519.P) :
    VG.Proof.Mont.AArch64.ModOkA M 4096 Spec.X25519.P m base :=
  ⟨by decide, by decide, by decide, by decide, by decide, h, by decide +kernel, by decide +kernel,
    fun f m' hc => by rw [VG.Proof.Weierstrass.AArch64.callOf_small (by decide)] at hc; cases hc⟩

theorem modA : VG.Proof.Mont.AArch64.ModA M := ⟨by decide, by decide⟩

/-- A word away from what a Montgomery operation writes keeps its value. -/
theorem opkeep_word {s t : State} {base : Addr} {o : Nat} (tk : VG.Proof.Mont.AArch64.OpKeep M base o s t)
    {d : Nat} (h1 : d + 8 ≤ o ∨ o + 32 ≤ d) (h2 : d + 8 ≤ 4000 ∨ 4032 ≤ d) (hd : d + 8 ≤ 4096) :
    VG.Proof.Mont.word t.mem base d = VG.Proof.Mont.word s.mem base d :=
  (Mem.readW_congr fun i hi => (tk.mem _ (by rw [VG.Proof.Mont.ofs_off base (by omega)]; simp only [M_n]; omega)
    (by rw [VG.Proof.Mont.ofs_off base (by omega), M_tmp, M_n]; omega)).symm).symm

theorem opkeep_wv {s t : State} {base : Addr} {o : Nat} (tk : VG.Proof.Mont.AArch64.OpKeep M base o s t)
    {d : Nat} (h1 : d + 32 ≤ o ∨ o + 32 ≤ d) (h2 : d + 32 ≤ 4000 ∨ 4032 ≤ d) (hd : d + 32 ≤ 4096) :
    VG.Proof.Mont.wordsVal t.mem base d 4 = VG.Proof.Mont.wordsVal s.mem base d 4 := by
  simp only [VG.Proof.Mont.wordsVal]
  rw [opkeep_word tk (d := d) (by omega) (by omega) (by omega),
    opkeep_word tk (d := d + 8) (by omega) (by omega) (by omega),
    opkeep_word tk (d := d + 8 + 8) (by omega) (by omega) (by omega),
    opkeep_word tk (d := d + 8 + 8 + 8) (by omega) (by omega) (by omega)]

theorem opkeep_outside {s t : State} {base : Addr} {o : Nat} (tk : VG.Proof.Mont.AArch64.OpKeep M base o s t)
    (ho : 2304 ≤ o) (ho' : o + 32 ≤ 4096) : VG.Proof.Mont.Outside base 2304 1792 s.mem t.mem :=
  fun x hx => tk.mem x (by simp only [M_n]; omega) (by simp only [M_tmp, M_n]; omega)

/-- The constants, and `[BASE] = z R mod p`. -/
theorem pre_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block pre) s fun t =>
      VG.Proof.Mont.AArch64.ModOkA M 4096 Spec.X25519.P t.mem base ∧
      VG.Proof.Mont.wordsVal t.mem base ONE 4 = 1 ∧
      VG.Proof.Mont.word t.mem base SX1 = s.gpr .x1 ∧
      VG.Proof.Mont.wordsVal t.mem base BASE 4 < Spec.X25519.P ∧
      VG.Proof.Mont.wordsVal t.mem base BASE 4 * 2 ^ 256 % Spec.X25519.P =
        VG.Proof.Ed25519.AArch64.fe s.mem base 128 * (1444) % Spec.X25519.P ∧
      VG.Proof.Mont.Outside base 2304 1792 s.mem t.mem ∧
      VG.Proof.Mont.AArch64.KeepRegs (VG.Proof.Mont.AArch64.clob 4 ++ [.x2]) s t := by
  have hm := mscr hs
  simp only [pre, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Mont.AArch64.st_ok hm (d := SX1) (by decide) (by decide) .x1) fun a ha => ?_
  subst ha
  have am : VG.Proof.Mont.AArch64.Scr { s with mem := s.mem.writeW (VG.Proof.Mont.off base SX1) (s.gpr .x1) }
      base 4096 := ⟨hm.x0, hm.wr, hm.nowrap, hm.enc⟩
  rw [WP.block_append_iff]
  refine WP.mono (storeConst_ok am Spec.X25519.P (o := M.mo) (by decide) (by decide) (by decide))
    fun b ⟨bv, bO, bk⟩ => ?_
  have bs : VG.Proof.Mont.AArch64.Scr b base 4096 := ⟨(bk.gpr _ (by decide)).trans am.x0, bk.wr ▸ am.wr, hm.nowrap, hm.enc⟩
  rw [WP.block_append_iff]
  refine WP.mono (storeConst_ok bs (1444) (o := R2) (by decide) (by decide) (by decide))
    fun c ⟨cv, cO, ck⟩ => ?_
  have cs : VG.Proof.Mont.AArch64.Scr c base 4096 := ⟨(ck.gpr _ (by decide)).trans bs.x0, ck.wr ▸ bs.wr, hm.nowrap, hm.enc⟩
  rw [WP.block_append_iff]
  refine WP.mono (storeConst_ok cs 1 (o := ONE) (by decide) (by decide) (by decide)) fun d ⟨dv, dO, dk⟩ => ?_
  have ds : VG.Proof.Mont.AArch64.Scr d base 4096 := ⟨(dk.gpr _ (by decide)).trans cs.x0, dk.wr ▸ cs.wr, hm.nowrap, hm.enc⟩
  have dmo : VG.Proof.Mont.wordsVal d.mem base M.mo 4 = Spec.X25519.P := by
    rw [dO.wordsVal (by decide) (by decide), cO.wordsVal (by decide) (by decide), bv]
  have dr2 : VG.Proof.Mont.wordsVal d.mem base R2 4 = 1444 := by
    rw [dO.wordsVal (by decide) (by decide), cv]
  refine WP.mono (VG.Proof.Mont.AArch64.mul_ok ds (modOk dmo) modA (o := BASE) (a := 128) (b := R2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [M_n, dr2]; decide))
    fun t ⟨tk, tv, te⟩ => ?_
  have wA : VG.Proof.Mont.Outside base SX1 8 s.mem (s.mem.writeW (VG.Proof.Mont.off base SX1) (s.gpr .x1)) :=
    VG.Proof.Mont.writeW_outside _ base _ (by decide)
  have d128 : VG.Proof.Mont.wordsVal d.mem base 128 4 = VG.Proof.Mont.wordsVal s.mem base 128 4 := by
    rw [dO.wordsVal (by decide) (by decide), cO.wordsVal (by decide) (by decide),
      bO.wordsVal (by decide) (by decide)]
    exact wA.wordsVal (by decide) (by decide)
  refine ⟨modOk (by rw [opkeep_wv tk (d := M.mo) (by decide) (by decide) (by decide)]; exact dmo),
    by rw [opkeep_wv tk (d := ONE) (by decide) (by decide) (by decide)]; exact dv, ?_, by rw [← M_n]; exact tv,
    ?_, ?_, ⟨fun r hr => ?_, tk.rd.trans (dk.rd.trans (ck.rd.trans bk.rd)),
      tk.wr.trans (dk.wr.trans (ck.wr.trans bk.wr)), tk.sp.trans (dk.sp.trans (ck.sp.trans bk.sp))⟩⟩
  · rw [opkeep_word tk (d := SX1) (by decide) (by decide) (by decide), dO.word (by decide) (by decide),
      cO.word (by decide) (by decide), bO.word (by decide) (by decide)]
    exact VG.Proof.Mont.word_writeW_self _ _ _ _
  · rw [fe_wordsVal, ← d128, ← dr2]
    simpa only [M_n] using te
  · exact ((((wA.mono (by decide) (by decide)).trans (bO.mono (by decide) (by decide))).trans
      (cO.mono (by decide) (by decide))).trans (dO.mono (by decide) (by decide))).trans
      (opkeep_outside tk (by decide) (by decide))
  · simp only [List.mem_append, List.mem_singleton, not_or] at hr
    rw [tk.gpr r (by simpa only [M_n] using hr.1), dk.gpr r (by simpa using hr.2),
      ck.gpr r (by simpa using hr.2), bk.gpr r (by simpa using hr.2)]

open VG.Proof.Weierstrass (toM rinv UnitMod ofNat_mul' ofNat_eq_ofNat ofNat_pow' mul_rinv unitMod_pow_two) in
/-- The arithmetic of `Invert.invert`: `z` in as `z R`, `z^(p - 2) R` out by a product with `1`. -/
theorem invert_arith {Z Bv Acc Res : Nat}
    (hb : Bv * 2 ^ 256 % Spec.X25519.P = Z * 1444 % Spec.X25519.P)
    (hacc : toM Spec.X25519.P (2 ^ 256) Acc = toM Spec.X25519.P (2 ^ 256) Bv ^ (Spec.X25519.P - 2))
    (hres : Res * 2 ^ 256 % Spec.X25519.P = Acc * 1 % Spec.X25519.P) :
    VG.Proof.X25519.toFe Res = VG.Proof.X25519.invert (VG.Proof.X25519.toFe Z) := by
  have hU : UnitMod Spec.X25519.P (2 ^ 256) := unitMod_pow_two (by decide) 256
  have hu := mul_rinv hU
  have e1444 : (Fin.ofNat Spec.X25519.P 1444 : Fin Spec.X25519.P) =
      Fin.ofNat Spec.X25519.P (2 ^ 256) * Fin.ofNat Spec.X25519.P (2 ^ 256) := by
    rw [← ofNat_mul']; exact ofNat_eq_ofNat.mpr (by decide +kernel)
  have hb' : Fin.ofNat Spec.X25519.P Bv * Fin.ofNat Spec.X25519.P (2 ^ 256) =
      Fin.ofNat Spec.X25519.P Z * Fin.ofNat Spec.X25519.P 1444 := by
    rw [← ofNat_mul', ← ofNat_mul']; exact ofNat_eq_ofNat.mpr hb
  have hres' : Fin.ofNat Spec.X25519.P Res * Fin.ofNat Spec.X25519.P (2 ^ 256) =
      Fin.ofNat Spec.X25519.P Acc := by
    rw [← ofNat_mul']; exact ofNat_eq_ofNat.mpr (by rw [hres, Nat.mul_one])
  have hB : toM Spec.X25519.P (2 ^ 256) Bv = Fin.ofNat Spec.X25519.P Z := by
    unfold toM; rw [e1444] at hb'; grind
  have hR : Fin.ofNat Spec.X25519.P Res = toM Spec.X25519.P (2 ^ 256) Acc := by
    unfold toM; grind
  rw [VG.Proof.X25519.invert_eq, VG.Proof.X25519.pow_pw]
  show Fin.ofNat Spec.X25519.P Res = Fin.ofNat Spec.X25519.P ((Fin.ofNat Spec.X25519.P Z).val ^ (Spec.X25519.P - 2))
  rw [hR, hacc, hB, ← ofNat_pow', Fin.val_ofNat]
  exact (ofNat_eq_ofNat (m := Spec.X25519.P)).mpr (Nat.pow_mod Z (Spec.X25519.P - 2) Spec.X25519.P)

/-- What `Invert.invert` changes in X25519's working space: slot 15, and from
the inversion's area on. -/
def IMem (base : Addr) (m m' : Mem) : Prop :=
  ∀ x, (VG.Proof.Mont.ofs base x < 544 ∨ (576 ≤ VG.Proof.Mont.ofs base x ∧ VG.Proof.Mont.ofs base x < 2304) ∨
    4096 ≤ VG.Proof.Mont.ofs base x) → m' x = m x

theorem invLay : VG.Proof.Weierstrass.AArch64.InvLay cfg 4096 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, modA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem invOk : VG.Proof.Weierstrass.AArch64.InvOk cfg Spec.X25519.P :=
  VG.Proof.Weierstrass.AArch64.InvOk.ofMod (by decide +kernel) (by decide)

theorem invW_eq : VG.Proof.Weierstrass.AArch64.invW cfg = [(2624, 32), (2304, 288), (4000, 32)] := rfl

theorem cfg_n : cfg.M.n = 4 := rfl
theorem cfg_acc : cfg.acc = ACC := rfl
theorem cfg_base : cfg.base = BASE := rfl

theorem offset_two : VG.Impl.Ed25519.AArch64.offset 2 = 128 := rfl
theorem offset_fifteen : VG.Impl.Ed25519.AArch64.offset 15 = 544 := rfl

/-- A word away from what the divsteps write keeps its value. -/
theorem unch_word {m m' : Mem} {base : Addr} (hU : VG.Proof.Weierstrass.Unch base (VG.Proof.Weierstrass.AArch64.invW cfg) m m')
    {d : Nat} (h1 : d + 8 ≤ 2304 ∨ 2592 ≤ d) (h2 : d + 8 ≤ 2624 ∨ 2656 ≤ d) (h3 : d + 8 ≤ 4000 ∨ 4032 ≤ d)
    (hd : d + 8 ≤ 4096) : VG.Proof.Mont.word m' base d = VG.Proof.Mont.word m base d := by
  refine (Mem.readW_congr fun i hi => (hU _ ?_).symm).symm
  intro w hw
  rw [invW_eq] at hw
  rw [VG.Proof.Mont.ofs_off base (by omega)]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> omega

theorem unch_wv {m m' : Mem} {base : Addr} (hU : VG.Proof.Weierstrass.Unch base (VG.Proof.Weierstrass.AArch64.invW cfg) m m')
    {d : Nat} (h1 : d + 32 ≤ 2304 ∨ 2592 ≤ d) (h2 : d + 32 ≤ 2624 ∨ 2656 ≤ d) (h3 : d + 32 ≤ 4000 ∨ 4032 ≤ d)
    (hd : d + 32 ≤ 4096) : VG.Proof.Mont.wordsVal m' base d 4 = VG.Proof.Mont.wordsVal m base d 4 := by
  simp only [VG.Proof.Mont.wordsVal]
  rw [unch_word hU (d := d) (by omega) (by omega) (by omega) (by omega),
    unch_word hU (d := d + 8) (by omega) (by omega) (by omega) (by omega),
    unch_word hU (d := d + 8 + 8) (by omega) (by omega) (by omega) (by omega),
    unch_word hU (d := d + 8 + 8 + 8) (by omega) (by omega) (by omega) (by omega)]

/-- `[slot 15] = [slot 2]^(p - 2)`. -/
theorem invert_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa VG.Impl.X25519.AArch64.Invert.invert s fun t =>
      VG.Proof.Ed25519.AArch64.env t.mem base 15 = VG.Proof.X25519.invert (VG.Proof.Ed25519.AArch64.env s.mem base 2) ∧
      VG.Proof.Mont.AArch64.KeepRegs (.x19 :: VG.Proof.Mont.AArch64.clob 4 ++ [.x2]) s t ∧
      t.gpr .x1 = s.gpr .x1 ∧ IMem base s.mem t.mem := by
  have hm := mscr hs
  refine WP.seq (WP.mono (pre_ok hs) fun a ⟨aM, a1, ax, ab, abv, aO, ak⟩ => ?_)
  have as : VG.Proof.Mont.AArch64.Scr a base 4096 := ⟨(ak.gpr _ (by decide)).trans hm.x0, ak.wr ▸ hm.wr, hm.nowrap, hm.enc⟩
  refine WP.seq (WP.mono (invSound invLay (by decide) (VG.Proof.Weierstrass.unitMod_pow_two (by decide) _) as aM ab invOk)
    fun b ⟨bk, bU, bv, be⟩ => ?_)
  have bs : VG.Proof.Mont.AArch64.Scr b base 4096 := ⟨(bk.gpr _ (by decide)).trans as.x0, bk.wr ▸ as.wr, hm.nowrap, hm.enc⟩
  have bmo : VG.Proof.Mont.wordsVal b.mem base M.mo 4 = Spec.X25519.P := by
    rw [unch_wv bU (by decide) (by decide) (by decide) (by decide)]; exact aM.val
  have b1 : VG.Proof.Mont.wordsVal b.mem base ONE 4 = 1 := by
    rw [unch_wv bU (by decide) (by decide) (by decide) (by decide)]; exact a1
  rw [VG.Impl.X25519.AArch64.Invert.post, WP.block_append_iff]
  refine WP.mono (VG.Proof.Mont.AArch64.mul_ok bs (modOk bmo) modA (o := 544) (a := ACC) (b := ONE)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [M_n, b1]; decide))
    fun c ⟨ck, cv, ce⟩ => ?_
  have cs : VG.Proof.Mont.AArch64.Scr c base 4096 := ⟨(ck.gpr _ (by decide)).trans bs.x0, ck.wr ▸ bs.wr, hm.nowrap, hm.enc⟩
  refine WP.mono (VG.Proof.Mont.AArch64.ld_ok cs (d := SX1) (by decide) (by decide) .x1) fun d ⟨d1, dk, _⟩ => ?_
  refine ⟨?_, ⟨fun r hr => ?_, dk.rd.trans (ck.rd.trans (bk.rd.trans ak.rd)), dk.wr.trans (ck.wr.trans (bk.wr.trans ak.wr)),
    dk.sp.trans (ck.sp.trans (bk.sp.trans ak.sp))⟩, ?_, fun x hx => ?_⟩
  · simp only [VG.Proof.Ed25519.AArch64.env, VG.Proof.Ed25519.AArch64.F, offset_two, offset_fifteen]
    rw [dk.mem, fe_wordsVal, fe_wordsVal]
    have be' : VG.Proof.Weierstrass.toM Spec.X25519.P (2 ^ 256) (VG.Proof.Mont.wordsVal b.mem base ACC 4) =
        VG.Proof.Weierstrass.toM Spec.X25519.P (2 ^ 256) (VG.Proof.Mont.wordsVal a.mem base BASE 4) ^
          (Spec.X25519.P - 2) := be
    have ce' : VG.Proof.Mont.wordsVal c.mem base 544 4 * 2 ^ 256 % Spec.X25519.P =
        VG.Proof.Mont.wordsVal b.mem base ACC 4 * VG.Proof.Mont.wordsVal b.mem base ONE 4 % Spec.X25519.P := ce
    rw [b1] at ce'
    rw [fe_wordsVal] at abv
    exact invert_arith (Z := VG.Proof.Mont.wordsVal s.mem base 128 4) (Bv := VG.Proof.Mont.wordsVal a.mem base BASE 4)
      (Acc := VG.Proof.Mont.wordsVal b.mem base ACC 4) (Res := VG.Proof.Mont.wordsVal c.mem base 544 4) abv be' ce'
  · simp only [List.mem_cons, List.mem_append, not_or] at hr
    obtain ⟨⟨h19, hc⟩, h2⟩ := hr
    have h2' : r ≠ .x2 := by simpa using h2
    rw [dk.gpr r (by simp only [List.mem_singleton]; exact fun e => hc (by subst e; decide)),
      ck.gpr r (by simpa only [M_n] using hc),
      bk.gpr r (by simp only [VG.Proof.Weierstrass.AArch64.powClob, List.mem_cons, not_or]; exact ⟨h19, hc⟩),
      ak.gpr r (by simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨hc, h2'⟩)]
  · rw [d1, opkeep_word ck (d := SX1) (by decide) (by decide) (by decide),
      unch_word bU (by decide) (by decide) (by decide) (by decide)]
    exact ax
  · rw [dk.mem]
    have hn := hm.nowrap
    rw [ck.mem x (by simp only [M_n]; omega) (by simp only [M_tmp, M_n]; omega)]
    rw [bU x (by
      intro w hw
      rw [invW_eq] at hw
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> omega)]
    exact aO x (by omega)

end VG.Proof.X25519.AArch64.Hybrid
