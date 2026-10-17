module

public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCall
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
public import VerifiedGarbage.Proof.RsaPss.VerifyAny
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaPss.AArch64.FixedSaltSelect
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyLogic

/-!
# RSASSA-PSS verification on AArch64: after the checks

`main_ok`: from the checks passed (`AtMain`), `DB`'s registers, the call's
arguments and the call, then `EM` checked (`b1_ok`, `b2_ok`): `x0` is 1
exactly when the encoding in RSAVP1's result is valid (`vlogic`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (off off_add Lay Rep mgfWr slotR slot_keep dbRegs_ok b1_ok b2_ok B1 wct mkB nz nz_lt
  resV msgV acc0V acc1V vlogic byte_of_bytesAt)
open VG.Proof.RsaPss.AArch64.Sgn (stk kR fb kb fb_eq frame_sub frame_sub0 below_fb below_sub in_frame zx_eq)

/-- After the checks, with `lo` and the mask `c` in their slots and
`emLen - hLen - 2` in `x9`. -/
structure AtMain (D : Nat) (s : State) (lo : Nat) (c : Byte) (w : State) : Prop where
  sp : w.sp = fb s
  rd : w.rd = s.rd
  wr : w.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x9 : w.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x1).toNat - lo - (D + 2))
  x19 : w.gpr .x19 = off (scr s) oSt
  x20 : w.gpr .x20 = scr s
  x21 : w.gpr .x21 = off (scr s) oDig
  x23 : w.gpr .x23 = s.gpr .x1
  v : ∀ r ∈ preservedV, (w.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [⟨fb s, frameBytes⟩] s.mem w.mem
  fr : Fr s w.mem
  lo : w.mem.readW (fb s + BitVec.ofNat 64 sLo) 64 = BitVec.ofNat 64 lo
  c : w.mem.readW (fb s + BitVec.ofNat 64 sC) 64 = BitVec.setWidth 64 c

/-- In the frame: the slots and the callee-saved registers' values. -/
structure Mid (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  fr : Fr s t.mem

/-- RSAVP1's result, or zeros. -/
abbrev pubX (s : State) : List Byte := (pubOut s).getD (List.replicate (s.gpr .x1).toNat 0)

/-- The salt length `verify` expects. -/
abbrev sLenV (s : State) : Option Nat := if anyV s = 0 then some (stackArg s 1).toNat else none

theorem pubX_length (s : State) : (pubX s).length = (s.gpr .x1).toNat := by
  unfold pubX
  cases h : pubOut s with
  | none => simp
  | some y =>
    rw [Option.getD_some, RsaPss.publicOpChecked_length' h, VG.Proof.RsaPkcs1Sig.bytesAt_length]

theorem pubX_bytes {s : State} {m : Mem} {r : BitVec 32}
    (h : Spec.Rsa.written m (off (scr s) oEm) (s.gpr .x1).toNat r (pubOut s)) :
    Spec.Rsa.bytesAt m (off (scr s) oEm) (s.gpr .x1).toNat = pubX s := by
  unfold pubX
  cases e : pubOut s with
  | none => rw [e] at h; exact h.2
  | some y => rw [e] at h; exact h.2

theorem rsa_lay {D K : Nat} {s : State} (hp : PreV D K s) (hK : 16 ≤ K) {t : State} (hsp : t.sp = fb s)
    (hwr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) (h20 : t.gpr .x20 = scr s) : Lay t (fb s) (scr s) := by
  have hfb := fb_toNat hp
  have hws : (scr s).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64 := hp.ws
  have hhs := hp.hs
  exact {
    sp := hsp
    x20 := h20
    fw := by rw [hwr]; exact List.mem_cons_self
    sw := ⟨sR s, by rw [hwr]; exact List.mem_cons_of_mem _ hp.hws,
      ⟨rfl, show oRsa ≤ (stackArg s 3).toNat * 8 by unfold oRsa; omega⟩⟩
    Fw := by omega
    Sw := by unfold oRsa; omega
    dFS := (hp.ks.sub_left (frame_sub0 K s)).sub_right (rsa_sub hp)
    dB := (hp.ks.sub_left fun a h => below_sub K s a
      (Offset.sub_below (fb s) (a := 16) (b := K) (n := 16) (m := K) hK (by omega) a h)).sub_right (rsa_sub hp) }

theorem mgfWr_sub (s : State) {K : Nat} (hK : 16 ≤ K) :
    ∀ r ∈ mgfWr (fb s) (scr s) ++ [slotR (fb s) sPos], r = ⟨scr s, oRsa⟩ ∨ Region.Sub r (kR K s) := by
  intro r hr
  simp only [mgfWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr fun a h => below_sub K s a
      (Offset.sub_below (fb s) (a := 16) (b := K) (n := 16) (m := K) hK (by omega) a h)
  · exact .inr (frame_sub K s (by decide))
  · exact .inr (frame_sub K s (by decide))
  · exact .inr (frame_sub K s (by decide))

/-- What `EM`'s checks write keeps `Fr`. -/
theorem fr_mgf {D K : Nat} {s : State} (hp : PreV D K s) {m m' : Mem} (h : Fr s m)
    (hf : Frame (mgfWr (fb s) (scr s) ++ [slotR (fb s) sPos]) m m') : Fr s m' := by
  refine h.frame hf (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) <;>
  · simp only [mgfWr, slotR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.ks.sub_left (frame_sub K s (by decide))).sub_right (rsa_sub hp)
    · exact Offset.disjoint_below _ (by omega)
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)

/-- The digest, in memory changed only where the code writes. -/
theorem dig_keep {D K : Nat} {s : State} (hp : PreV D K s) (hK : 16 ≤ K) {m₁ m₂ m₃ : Mem}
    (h₁ : Frame [kR K s, sR s] s.mem m₁) (h₂ : Frame (mgfWr (fb s) (scr s) ++ [slotR (fb s) sPos]) m₁ m₂)
    (h₃ : Frame (mgfWr (fb s) (scr s)) m₂ m₃) :
    Spec.Rsa.bytesAt m₃ (s.gpr .x4) D = Spec.Rsa.bytesAt s.mem (s.gpr .x4) D := by
  have hl : D ≤ 2 ^ 64 := by have := hp.wdg; omega
  have hd : ∀ r ∈ mgfWr (fb s) (scr s) ++ [slotR (fb s) sPos], Region.Disjoint (dgR D s) r := fun r hr => by
    rcases mgfWr_sub s hK r hr with rfl | h
    · exact hp.dgs.sub_right (rsa_sub hp)
    · exact (hp.kdg.sub_left h).symm
  rw [VG.Proof.RsaPss.AArch64.bytes_apartL h₃ (fun r hr => hd r (List.mem_append_left _ hr)) hl,
    VG.Proof.RsaPss.AArch64.bytes_apartL h₂ hd hl,
    VG.Proof.RsaPss.AArch64.bytes_apartL h₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.kdg.symm
      · exact hp.dgs) hl]

/-- The hash functions the arguments name, in a list of them (a tier's). -/
structure Pick (hs : List Hash) (s : State) where
  H : Hash
  G : Hash
  hH : HashOK H
  hG : HashOK G
  Hs : Spec.Mgf1.Hash
  Gs : Spec.Mgf1.Hash
  kH : hs[(stackArg s 6).toNat]? = some H
  kG : hs[(stackArg s 7).toNat]? = some G
  hl : hs.length ≤ 4096
  hHh : ∀ x, Hs.hash x = hH.SH.H.hash x
  hHl : Hs.len = H.D
  hGh : ∀ x, Gs.hash x = hG.SH.H.hash x
  hGl : Gs.len = G.D
  hGv : Proof.Mgf1.Valid Gs
  hHv : Proof.Mgf1.Valid Hs

/-- After the call: `EM` checked, `x0` 1 exactly when the encoding is
valid. -/
theorem check_ok {hs : List Hash} {K : Nat} {s t : State} (P : Pick hs s) (hp : PreV P.H.D K s) (hK : 16 ≤ K)
    {lo : Nat} {cb : Byte} {z : Nat} (ha : AfterCall P.H.D K s lo cb t) (hlo : lo ≤ 1)
    (hfit : P.H.D + 2 ≤ (s.gpr .x1).toNat - lo) (hc : cb = (0xFF : Byte) >>> z)
    (hsl : anyV s = 0 → (stackArg s 1).toNat < (s.gpr .x1).toNat - lo - P.H.D - 1) :
    WP isa (seqs [.block acc0, mgfXorAny hs, .block clearTop, posScan, posCheck,
      onHash sHash hs Impl.RsaPss.AArch64.FixedSalt.select]) t fun u => Mid s u ∧ (Cons s →
      ∀ b : Bool, (b = true ↔ (lo = 1 → (pubX s).getD 0 0 = 0) ∧
        RsaPss.EncOk₂ P.Hs P.Gs (Spec.Rsa.bytesAt s.mem (s.gpr .x4) P.H.D) ((pubX s).drop lo)
          ((s.gpr .x1).toNat - lo) z (sLenV s)) →
        u.gpr .x0 = if b then 1#64 else 0#64) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hhh := hp.hh; have hhg := hp.hg
  have hD : 0 < P.H.D ∧ P.H.D ≤ 64 := ⟨P.hH.sizes.D0, by have := P.hH.sizes.DN; have := P.hH.N_le; omega⟩
  have L := rsa_lay hp hK ha.sp ha.wr ha.x20
  have h25 := ha.x25
  generalize hk : (s.gpr .x1).toNat = k at hfit hsl h25 hk1 hk2 ⊢
  have hkd : lo + (k - lo - P.H.D - 1) + P.H.D + 1 = k := by omega
  have h23 : t.gpr .x23 = BitVec.ofNat 64 k := by rw [ha.x23, ← hk, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hS : t.mem.readW (off (fb s) sSaltLen) 64 = stackArg s 1 := ha.fr.sl
  have hsD : t.mem.readW (off (fb s) sHLen) 64 = BitVec.ofNat 64 P.H.D := by
    rw [ha.fr.rs (.x5, sHLen) (by simp [regSlots]), ← hp.dl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine (b1_ok P.kG P.hl P.hG P.hGh P.hGl P.hGv hD L (V := fun o => t.mem (off (scr s) o)) (fun _ _ => rfl)
    (by rw [ha.fr.mgf, zx_eq (by omega)]) hsD (k := k) (lo := lo)
    (db := k - lo - P.H.D - 1) (c := cb) (any := anyV s) (sv := stackArg s 1) hkd (by omega) (by omega) hlo ha.x19
    ha.x21 h23 ha.x24 h25 ha.lo ha.c ha.fr.any hS
    (rest := onHash sHash hs Impl.RsaPss.AArch64.FixedSalt.select)
    fun u B => ?_ : WP isa (seqs [.block acc0, mgfXorAny hs, .block clearTop, posScan, posCheck,
      onHash sHash hs Impl.RsaPss.AArch64.FixedSalt.select]) t _)
  have gu : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25], u.gpr r = t.gpr r := B.cs
  have hslot : ∀ d, d + 8 ≤ frameBytes →
      (d + 8 ≤ sNb ∨ sNb + 8 ≤ d) → (d + 8 ≤ sDone ∨ sDone + 8 ≤ d) →
      (d + 8 ≤ sPos ∨ sPos + 8 ≤ d) →
      u.mem.readW (off (fb s) d) 64 = t.mem.readW (off (fb s) d) 64 := by
    intro d hd hn hf hpos
    apply slot_keep B.fr
    intro r hr
    rcases List.mem_append.mp hr with h | h
    · exact L.slotW hd hn hf r h
    · rw [List.mem_singleton.mp h]
      exact Offset.disjoint _ hpos (by unfold frameBytes at hd; omega) (by decide)
  have hdg : u.mem.readW (off (fb s) sDig) 64 = s.gpr .x4 := by
    rw [hslot sDig (by decide) (by decide) (by decide) (by decide)]
    exact ha.fr.rs (.x4, sDig) (by simp [regSlots])
  have hrd : ∀ j < P.H.D, InRegions (u.rd ++ u.wr) (s.gpr .x4 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [B.rd, B.wr, ha.rd, ha.wr]
    exact Covers.left (Covers.trans (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; simp) hp.hrd) _ _
      ⟨dgR P.H.D s, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by have := hp.wdg; omega)⟩
  refine WP.mono (VG.Proof.RsaPss.AArch64.FixedSalt.selectAny_ok P.hH P.kH P.hl (L.congr B.sp B.wr (gu .x20 (by decide)))
    (W := wct (fun o => t.mem (off (scr s) o)) (mkB P.Gs P.H.D (fun o => t.mem (off (scr s) o)) (oEm + lo)
      (k - lo - P.H.D - 1)) (oEm + lo) (k - lo - P.H.D - 1) cb) (e := oEm + lo) (db := k - lo - P.H.D - 1)
    B.em (by omega) (by unfold oEm oY; omega)
    (nz_lt (by omega)) (by omega) (by rw [gu .x19 (by decide), ha.x19]) (by rw [gu .x21 (by decide), ha.x21])
    (by rw [gu .x24 (by decide), ha.x24]) (by rw [gu .x25 (by decide), h25]) B.acc B.pos hdg hrd
    (hp.dgs.sub_right (rsa_sub hp))
    (by rw [hslot sAny (by decide) (by decide) (by decide) (by decide)]; exact ha.fr.any)
    (sl := (stackArg s 1).toNat)
    (by rw [hslot sSaltLen (by decide) (by decide) (by decide) (by decide), hS, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    hsl
    (by
      intro hany hacc
      have heq := (VG.Proof.RsaPss.AArch64.acc1V_eq_zero _ _ _ _ _).mp hacc
      exact (VG.Proof.RsaPss.AArch64.eq_ofNat_iff (by omega) _).mp (heq.2.2.2 hany))
    (by
      have hb := VG.Proof.RsaPss.AArch64.acc_lt (fun o => t.mem (off (scr s) o)) k lo cb
        (fun i => wct (fun o => t.mem (off (scr s) o))
          (mkB P.Gs P.H.D (fun o => t.mem (off (scr s) o)) (oEm + lo) (k - lo - P.H.D - 1))
          (oEm + lo) (k - lo - P.H.D - 1) cb (oEm + lo + i))
        (k - lo - P.H.D - 1) (anyV s) (stackArg s 1) (fun _ => 0) 0 (by omega)
        (fun h => by have := hsl h; omega) (fun _ => by decide)
      simpa [VG.Proof.RsaPss.AArch64.orF] using hb)
    (by rw [hslot sHash (by decide) (by decide) (by decide) (by decide), ha.fr.hsh, zx_eq (by omega)]))
    fun u' ⟨sp', rd', wr', cs', v', fr', x0'⟩ => ⟨?_, fun hcons b hb => ?_⟩
  · exact ⟨by rw [sp', B.sp, ha.sp], by rw [rd', B.rd, ha.rd], by rw [wr', B.wr, ha.wr],
      fun r hr => by rw [v' r hr, B.v r hr, ha.v r hr],
      fr_mgf hp (fr_mgf hp ha.fr B.fr) (fr'.mono fun r hr => List.mem_append_left _ hr)⟩
  rw [x0', dig_keep (D := P.H.D) hp hK ha.mem B.fr (Frame.refl _ _), ← funext P.hHh]
  have hx := pubX_bytes (ha.res hcons)
  rw [hk] at hx
  refine vlogic P.hHv P.hGv P.hHl (x := pubX s) (by rw [pubX_length, hk]) (fun i hi => ?_) hkd (by omega) hlo hk2
    (VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _) hc (fun h => hsl h) hb
  show t.mem (off (scr s) (oEm + i)) = _
  rw [← off_add]
  exact byte_of_bytesAt hx hi

/-- `DB`'s registers, before the call. -/
theorem pre_ok {D K : Nat} {s w : State} (hp : PreV D K s) (hK : 16 ≤ K) {lo : Nat} {cb : Byte}
    (hm : AtMain D s lo cb w) (hfit : D + 2 ≤ (s.gpr .x1).toNat - lo) :
    WP isa (.block dbRegs) w (PreCall D s lo cb) := by
  have L := rsa_lay hp hK hm.sp hm.wr hm.x20
  refine WP.mono (dbRegs_ok L hm.x9 hm.lo) fun u₁ ⟨O₁, x25₁, x24₁⟩ => ?_
  rw [show (s.gpr .x1).toNat - lo - (D + 2) + 1 = (s.gpr .x1).toNat - lo - D - 1 by omega] at x25₁
  exact {
    sp := O₁.sp.trans hm.sp
    rd := O₁.rd.trans hm.rd
    wr := O₁.wr.trans hm.wr
    x19 := (O₁.get .x19).trans hm.x19
    x20 := (O₁.get .x20).trans hm.x20
    x21 := (O₁.get .x21).trans hm.x21
    x23 := (O₁.get .x23).trans hm.x23
    x24 := x24₁
    x25 := x25₁
    v := fun r hr => (O₁.vcs r hr).trans (hm.v r hr)
    mem := O₁.mem ▸ hm.mem
    fr := O₁.mem ▸ hm.fr
    lo := O₁.mem ▸ hm.lo
    c := O₁.mem ▸ hm.c }

theorem main_ok {hs : List Hash} (c : PdChecked) {K : Nat} {s w : State} (P : Pick hs s)
    (hp : PreV P.H.D K s) (hK : 16 ≤ K)
    (hcK : c.stack ≤ K) {lo : Nat} {cb : Byte} {z : Nat} (hm : AtMain P.H.D s lo cb w) (hlo : lo ≤ 1)
    (hfit : P.H.D + 2 ≤ (s.gpr .x1).toNat - lo) (hc : cb = (0xFF : Byte) >>> z)
    (hsl : anyV s = 0 → (stackArg s 1).toNat < (s.gpr .x1).toNat - lo - P.H.D - 1) :
    WP isa (verifyMain hs c.name c.code) w fun u => Mid s u ∧ (Cons s →
      ∀ b : Bool, (b = true ↔ (lo = 1 → (pubX s).getD 0 0 = 0) ∧
        RsaPss.EncOk₂ P.Hs P.Gs (Spec.Rsa.bytesAt s.mem (s.gpr .x4) P.H.D) ((pubX s).drop lo)
          ((s.gpr .x1).toNat - lo) z (sLenV s)) →
        u.gpr .x0 = if b then 1#64 else 0#64) := by
  unfold verifyMain seqs seqs seqs
  refine WP.seq (WP.mono (pre_ok hp hK hm hfit) fun u₁ hP => ?_)
  refine WP.seq (WP.mono (pubArgs_ok hP) fun u₂ h₂ => ?_)
  refine WP.seq (WP.mono (call_ok c hp hcK h₂) fun u₃ h₃ => ?_)
  exact check_ok P hp hK h₃ hlo hfit hc hsl

end VG.Proof.RsaPss.AArch64.Vfy
