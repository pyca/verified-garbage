module

public import VerifiedGarbage.Proof.Ffdh.Lead
public import VerifiedGarbage.Proof.Ffdh.AArch64.Ws
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.Lead
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Ws
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# FFDH on AArch64: the scan for the first nonzero octet

`scan sp`, in the outer workspace, over the `p_len` octets `bs` at the
pointer in slot `sp`: `lead bs` iterations, each reading an octet and going
on while it is zero and not the last; the pointer and length of the octets
from `lead bs` into `sEp` and `sEl`, and that octet into `x3`
(`scan_ok`). The octets are public, and so is the number of iterations:
two runs on the same octets agree (`scan_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Crt
open VG.Impl.Ffdh.AArch64.Domain
open VG.Impl.Bignum.Public (sK)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep count_loop eval_nonzero ne_zero_iff)

/-- The loop's body. -/
def scanBody : List Instr :=
  [.ldrb .x4 .x1 0, movi .x7 0, movi .x8 1, .subs .x .x3 .x4 .x8, .csel .x .x5 .x7 .x8,
    movi .x9 2, .subs .x .x3 .x2 .x9, .csel .x .x6 .x8 .x7, .logic .and .x .x5 .x5 .x6, .add .x .x1 .x1 .x5,
    .sub .x .x2 .x2 .x5]

theorem scan_eq (sp : Nat) : seqs (scan sp) =
    .seq (.block [ldh .x1 sp, ldh .x2 sK]) (.seq (.loop (.block scanBody) (.nonzero .x .x5))
      (.block [sth .x1 sEp, sth .x2 sEl, .ldrb .x3 .x1 0])) := rfl

/-- The registers before iteration `j`. -/
def ScanAt (s₀ : State) (p : Addr) (n j : Nat) (t : State) : Prop :=
  t.gpr .x1 = off p j ∧ t.gpr .x2 = BitVec.ofNat 64 (n - j) ∧ t.mem = s₀.mem ∧
    Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9] s₀ t

theorem byte_ofNat (b : Byte) : ((BitVec.ofNat 64 b.toNat) : BitVec 64).toNat = b.toNat := by
  rw [BitVec.toNat_ofNat]; have := b.isLt; omega

theorem scan_flag8 : ∀ (b : Byte) (d : Bool),
    ((if (!decide (BitVec.setWidth 64 (BitVec.setWidth 32 b) = 0)) = true then BitVec.setWidth 64 0#16
        else BitVec.setWidth 64 1#16) &&& if d = true then BitVec.setWidth 64 1#16 else BitVec.setWidth 64 0#16) =
      BitVec.ofNat 64 (decide (b = 0) && d).toNat := by
  decide

theorem scan_flag (b : Byte) {m : Nat} (hm : m < 2 ^ 64) :
    ((if (!decide (BitVec.setWidth 64 (BitVec.setWidth 32 b) = 0)) = true then BitVec.setWidth 64 0#16
        else BitVec.setWidth 64 1#16) &&&
      if decide (2 ≤ (BitVec.ofNat 64 m).toNat) = true then BitVec.setWidth 64 1#16 else BitVec.setWidth 64 0#16) =
      BitVec.ofNat 64 (decide (b = 0 ∧ 2 ≤ m)).toNat := by
  rw [scan_flag8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Bool.decide_and]

theorem subs_c2 (x : BitVec 64) :
    decide (2 ^ 64 ≤ x.toNat + (~~~(BitVec.setWidth 64 (2#16))).toNat + (true).toNat) = decide (2 ≤ x.toNat) := by
  have h1 : (~~~(BitVec.setWidth 64 (2#16))).toNat = 2 ^ 64 - 3 := by decide
  rw [h1, Bool.toNat_true]
  have := x.isLt
  by_cases h : 2 ≤ x.toNat <;> simp [h] <;> omega

/-- One iteration from `j ≤ lead bs`: `x5 := j < lead bs` (as 1 or 0), and the
pointer and the length moved by it. -/
theorem scanStep_ok {s₀ : State} {p : Addr} {bs : List Byte} (hl : bs.length < 2 ^ 32) (hne : bs ≠ [])
    (hrd : ∀ i < bs.length, InRegions (s₀.rd ++ s₀.wr) (p + BitVec.ofNat 64 i) 1)
    (hval : ∀ i (h : i < bs.length), s₀.mem (p + BitVec.ofNat 64 i) = bs[i]) {j : Nat} (hj : j ≤ lead bs)
    {t : State} (ht : ScanAt s₀ p bs.length j t) :
    WP isa (.block scanBody) t fun t' => ScanAt s₀ p bs.length (min (j + 1) (lead bs)) t' ∧
      ((t'.gpr .x5).toNat ≠ 0 ↔ j + 1 ≠ lead bs + 1) := by
  have hL := lead_lt hne
  have hjl : j < bs.length := by omega
  obtain ⟨h1, h2, hm, kt⟩ := ht
  have hld : InRegions (t.rd ++ t.wr) (p + BitVec.ofNat 64 j) 1 := by rw [kt.rd, kt.wr]; exact hrd j hjl
  have hb : t.mem (p + BitVec.ofNat 64 j) = bs[j] := by rw [hm]; exact hval j hjl
  -- Whether the scan goes on.
  have hgo : (bs[j] = 0 ∧ 2 ≤ bs.length - j) ↔ j < lead bs := by
    constructor
    · rintro ⟨hz, h2⟩
      by_contra hc
      have hje : j = lead bs := by omega
      subst hje
      exact lead_nonzero hne (by omega) hz
    · intro hlt
      obtain ⟨_, hz⟩ := lead_zero j hlt
      exact ⟨hz, by omega⟩
  generalize hc : decide (bs[j] = 0 ∧ 2 ≤ bs.length - j) = c
  have hv : (BitVec.ofNat 64 c.toNat).toNat ≠ 0 ↔ j < lead bs := by
    rw [← hgo]
    cases c
    · exact ⟨fun h => absurd (by decide) h, fun h => absurd h (of_decide_eq_false hc)⟩
    · exact ⟨fun _ => of_decide_eq_true hc, fun _ => by decide⟩
  refine WP.mono (WP.keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9] (Q := fun t' =>
      t'.gpr .x5 = BitVec.ofNat 64 c.toNat ∧ t'.gpr .x1 = off p (j + c.toNat) ∧
      t'.gpr .x2 = BitVec.ofNat 64 (bs.length - j) - BitVec.ofNat 64 c.toNat ∧ t'.mem = t.mem)
    (by
      unfold scanBody
      brun [h1, h2, hld, VG.Proof.MlKem.AArch64.read_one, hb, subs_one_c, subs_c2, scan_flag _ (show bs.length - j < 2 ^ 64 by omega), hc]
      done)
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h5, h1', h2', hm'⟩, k⟩ => ?_
  have hc' : c = decide (j < lead bs) := by rw [← hc]; exact decide_eq_decide.mpr hgo
  subst hc'
  refine ⟨⟨?_, ?_, hm'.trans hm, (kt.trans k).mono (by decide)⟩, ?_⟩
  · rw [h1']
    by_cases hlt : j < lead bs
    · rw [decide_eq_true hlt, Nat.min_eq_left (by omega)]; rfl
    · rw [decide_eq_false hlt, Nat.min_eq_right (by omega)]
      simp only [Bool.toNat_false, Nat.add_zero]; congr 1; omega
  · rw [h2']
    by_cases hlt : j < lead bs
    · rw [decide_eq_true hlt, Nat.min_eq_left (by omega), Bool.toNat_true,
        VG.Proof.Bignum.AArch64.ofNat_sub_one' (by omega) (by omega)]
      exact congrArg _ (by omega)
    · rw [decide_eq_false hlt, Nat.min_eq_right (by omega), Bool.toNat_false]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
  · rw [h5, hv]; omega

/-- `scan sp`, in the outer workspace, over the octets `bs` at the pointer in
slot `sp`, `p_len` of them. -/
theorem scan_ok {s : State} {B : Addr} {Z w : Nat} (h : Outer s B Z w) {sp : Nat} (hsp : sp < 32) {p : Addr}
    {bs : List Byte} (hp : word s.mem B (8 * sp) = p) (hk : word s.mem B (8 * sK) = BitVec.ofNat 64 bs.length)
    (hne : bs ≠ []) (hl : bs.length < 2 ^ 32) (hsrc : Src s B Z p bs) :
    WP isa (seqs (scan sp)) s fun t =>
      word t.mem B (8 * sEp) = off p (lead bs) ∧ word t.mem B (8 * sEl) = BitVec.ofNat 64 (bs.length - lead bs) ∧
      t.gpr .x3 = BitVec.ofNat 64 (bs[lead bs]'(lead_lt hne)).toNat ∧
      Frm B [(8 * sEp, 8), (8 * sEl, 8)] s.mem t.mem ∧ Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9] s t := by
  have hn := h.scr.nowrap
  have hL := lead_lt hne
  have hroom := h.room
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  rw [scan_eq]
  refine WP.seq (WP.mono (WP.keep [.x1, .x2] (Q := fun t => t.gpr .x1 = p ∧ t.gpr .x2 = BitVec.ofNat 64 bs.length ∧
      t.mem = s.mem) (by brun [h.x0, hdr_enc hsp, hdr_enc (show sK < 32 by decide), h.ld hsp, h.ld (show sK < 32 by decide),
        hp, hk]) rfl rfl rfl) fun s₁ ⟨⟨h1₁, h2₁, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (count_loop (cr := .x5) (n := lead bs + 1) (by omega)
    (fun k t => ScanAt s₁ p bs.length (min k (lead bs)) t)
    (fun k hk t ht => by
      have e : min k (lead bs) = k := Nat.min_eq_left (by omega)
      rw [e] at ht
      refine WP.mono (scanStep_ok hl hne (fun i hi => by rw [k₁.rd, k₁.wr]; exact hsrc.rd i hi)
        (fun i hi => by rw [hm₁]; exact hsrc.val i hi) (by omega) ht) fun t' ⟨ht', hc⟩ => ⟨ht', ?_⟩
      rw [hc])
    ⟨by rw [h1₁]; simp, by rw [h2₁]; simp, rfl, Keep.refl _ _⟩) fun s₂ h₂ => ?_)
  rw [Nat.min_eq_right (by omega)] at h₂
  obtain ⟨h1₂, h2₂, hm₂, k₂⟩ := h₂
  have h0₂' : s₂.gpr .x0 = B := by rw [k₂.gpr .x0 (by decide), k₁.gpr .x0 (by decide)]; exact h.x0
  have hs₂ : Scr s₂ B Z := h.scr.congr (k₂.wr.trans k₁.wr)
  have hld : InRegions (s₂.rd ++ s₂.wr) (off p (lead bs)) 1 := by
    rw [k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hsrc.rd _ hL
  have eEp : sEp = 23 := rfl
  have eEl : sEl = 24 := rfl
  have hEp := hdr_lt_slot w 8 (show sEp < 32 by decide)
  have hEl := hdr_lt_slot w 8 (show sEl < 32 by decide)
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = (s₂.mem.writeW (off B (8 * sEp)) (off p (lead bs))).writeW
      (off B (8 * sEl)) (BitVec.ofNat 64 (bs.length - lead bs)) ∧
      t.gpr .x3 = BitVec.setWidth 64 (BitVec.setWidth 32 (((s₂.mem.writeW (off B (8 * sEp)) (off p (lead bs))).writeW
      (off B (8 * sEl)) (BitVec.ofNat 64 (bs.length - lead bs))).read (off p (lead bs)) 1)))
    (by brun [h0₂', h1₂, h2₂, hdr_enc (show sEp < 32 by decide), hdr_enc (show sEl < 32 by decide),
      hs₂.st (d := 8 * sEp) (by omega), hs₂.st (d := 8 * sEl) (by omega), hld])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨hm, h3⟩, k⟩ => ?_
  have o₁ := writeW_outside s₂.mem B (d := 8 * sEp) (off p (lead bs)) (by omega)
  have o₂ := writeW_outside (s₂.mem.writeW (off B (8 * sEp)) (off p (lead bs))) B (d := 8 * sEl)
    (BitVec.ofNat 64 (bs.length - lead bs)) (by omega)
  have hout : Z ≤ ofs B (off p (lead bs)) := hsrc.out _ hL
  have hbyte : ((s₂.mem.writeW (off B (8 * sEp)) (off p (lead bs))).writeW (off B (8 * sEl))
      (BitVec.ofNat 64 (bs.length - lead bs))) (off p (lead bs)) = bs[lead bs] := by
    rw [o₂ _ (Or.inr (by omega)), o₁ _ (Or.inr (by omega)), hm₂, hm₁]; exact hsrc.val _ hL
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hm, o₂.word (by omega) (by omega)]; exact word_writeW_self _ _ _ _
  · rw [hm]; exact word_writeW_self _ _ _ _
  · rw [h3, VG.Proof.MlKem.AArch64.read_one, hbyte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := (bs[lead bs]'hL).isLt
    omega
  · intro x hx
    rw [hm, o₂ x (hx (8 * sEl, 8) (by simp)), o₁ x (hx (8 * sEp, 8) (by simp)), hm₂, hm₁]
  · exact ((k₁.trans k₂).trans k).mono (by decide)

/-! ## Constant time -/

/-- The public data of `scan sp`: the workspace, the pointer and the octets. -/
structure ScanPub where
  B : Addr
  Z : Nat
  w : Nat
  p : Addr
  bs : List Byte

/-- `scan_ok`'s hypotheses. -/
def ScanPre (sp : Nat) (a : ScanPub) (s : State) : Prop :=
  Outer s a.B a.Z a.w ∧ word s.mem a.B (8 * sp) = a.p ∧ word s.mem a.B (8 * sK) = BitVec.ofNat 64 a.bs.length ∧
    a.bs ≠ [] ∧ a.bs.length < 2 ^ 32 ∧ Src s a.B a.Z a.p a.bs ∧ sp < 32

/-- Before iteration `j` of the loop. -/
def ScanJ (a : ScanPub) (j : Nat) (t : State) : Prop :=
  t.gpr .x1 = off a.p j ∧ t.gpr .x2 = BitVec.ofNat 64 (a.bs.length - j) ∧ a.bs ≠ [] ∧
    a.bs.length < 2 ^ 32 ∧ Src t a.B a.Z a.p a.bs ∧ t.gpr .x0 = a.B

theorem scanJ_step (a : ScanPub) (j : Nat) (t : State) (hj : j < lead a.bs + 1) (h : ScanJ a j t) :
    WP isa (.block scanBody) t fun t' => isa.eval (.nonzero .x .x5) t' = some (decide (j + 1 < lead a.bs + 1)) ∧
      (j + 1 < lead a.bs + 1 → ScanJ a (j + 1) t') ∧ (j + 1 = lead a.bs + 1 → ScanJ a (lead a.bs) t') := by
  obtain ⟨h1, h2, hne, hl, hsrc, h0⟩ := h
  refine WP.mono (scanStep_ok (s₀ := t) hl hne hsrc.rd hsrc.val (j := j) (by omega)
    ⟨h1, h2, rfl, Keep.refl _ _⟩) fun t' ⟨⟨h1', h2', hm', k'⟩, hc⟩ => ?_
  have hs' : Src t' a.B a.Z a.p a.bs := hsrc.congr (by rw [hm']; exact InScr.refl _ _ _) k'.rd k'.wr
  have h0' : t'.gpr .x0 = a.B := (k'.gpr .x0 (by decide)).trans h0
  refine ⟨?_, fun hlt => ?_, fun he => ?_⟩
  · rw [eval_nonzero, ne_zero_iff]
    exact congrArg some (decide_eq_decide.mpr (by rw [hc]; omega))
  · rw [Nat.min_eq_left (by omega)] at h1' h2'
    exact ⟨h1', h2', hne, hl, hs', h0'⟩
  · rw [Nat.min_eq_right (by omega)] at h1' h2'
    exact ⟨h1', h2', hne, hl, hs', h0'⟩

/-- `scan sp` leaks the same in runs on the same octets. -/
theorem scan_ct {sp : Nat} {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x1 sp, ldh .x2 sK]) hc₁).isSome = true)
    (hT₂ : (taint.check (Taint.ofRegs [.x0, .x1]) (.block [sth .x1 sEp, sth .x2 sEl, .ldrb .x3 .x1 0]) hc₂).isSome =
      true) :
    RelCT isa (Two (ScanPre sp)) (seqs (scan sp)) fun _ _ => True := by
  rw [scan_eq]
  refine RelCT.seq (R := Two fun a t => 0 < lead a.bs + 1 ∧ ScanJ a 0 t)
    (two_piece [.x0] (pins_of (fun a _ => a.B) fun a s h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.1.x0) hT₁ fun a s h => ?_)
    (RelCT.seq (R := Two fun a t => ScanJ a (lead a.bs) t)
      (two_loop (fun a => lead a.bs + 1)
        (two_taint [.x1, .x2] (pins_of (fun (p : ScanPub × Nat) r => if r = .x1 then off p.1.p p.2 else
            BitVec.ofNat 64 (p.1.bs.length - p.2)) fun p t h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h.2.1
          · exact h.2.2.1) (by taint_decide))
        fun a j t hj h => scanJ_step a j t hj h)
      (two_taint [.x0, .x1] (pins_of (fun a r => if r = .x0 then a.B else off a.p (lead a.bs)) fun a t h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.2.2.2.2.2
        · exact h.1) hT₂))
  obtain ⟨hO, hp, hk, hne, hl, hsrc, hsp⟩ := h
  have l1 := hO.ld hsp
  have l2 := hO.ld (show sK < 32 by decide)
  exact WP.mono (WP.keep [.x1, .x2] (Q := fun t => t.gpr .x1 = a.p ∧ t.gpr .x2 = BitVec.ofNat 64 a.bs.length ∧
      t.mem = s.mem)
    (by brun [hO.x0, hdr_enc hsp, hdr_enc (show sK < 32 by decide), l1, l2, hp, hk])
    rfl rfl rfl)
    fun t ⟨⟨h1, h2, hm⟩, k⟩ => ⟨by omega, by rw [h1]; simp, by rw [h2]; simp, hne, hl,
      hsrc.congr (by rw [hm]; exact InScr.refl _ _ _) k.rd k.wr, (k.gpr .x0 (by decide)).trans hO.x0⟩

/-- What `scan` changes: two header slots. -/
theorem scanR_le : ∀ r ∈ [(8 * sEp, 8), (8 * sEl, 8)], 8 * 16 ≤ r.1 ∧ r.1 + r.2 ≤ 256 := by decide

/-- A header slot other than those `scan` writes is outside what it changes. -/
theorem scanR_word {i : Nat} (h1 : i ≠ sEp) (h2 : i ≠ sEl) :
    ∀ r ∈ [(8 * sEp, 8), (8 * sEl, 8)], 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  unfold sEp sEl sFn at *
  exact ⟨by omega, by omega⟩

end VG.Proof.Ffdh.AArch64
