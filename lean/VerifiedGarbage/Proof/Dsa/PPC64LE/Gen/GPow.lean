module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Power
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Pieces
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Bytes
import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KSLoad
import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KSStore
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Test
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # DSA parameter generation on PPC64LE: `h^((p − 1) / q) mod p` as a piece

`power_vp`: `power`, from a stage of the search whose claims hold p at
`sPBE` and `(p − 1) / q` at `sE`, apart from the P space, and whose header
word `fH` points at the `pLen` bytes of `h`: the stage kept, array 4 of the
P space `h^((p − 1) / q) mod p`, and `r0 = 0` exactly when it is above 1 and
below p. Its three pieces (`powA`, `h`'s pointer, `powC`) are analysed
apart, the last with the P space's registers and `h`'s pointer public; the
certificate of `powC`, whose code depends on the lengths, is a hypothesis,
which each instance discharges.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Proof.Bignum (slot)

/-- An address outside `[S + a, S + a + Z)`, by its distance from `S`, is
at least `Z` past `S + a`. -/
theorem le_ofs_off {S x : Addr} {a Z : Nat} (ha0 : a < 2 ^ 64) (ha : a + Z ≤ 2 ^ 64)
    (h : (x - S).toNat < a ∨ a + Z ≤ (x - S).toNat) : Z ≤ VG.Proof.Bignum.ofs (off S a) x := by
  have hlt := (x - S).isLt
  simp only [VG.Proof.Bignum.ofs, off]
  rw [Offset.toNat_sub_add x S (by omega)]
  rcases h with h | h
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - a + (x - S).toNat = (x - S).toNat - a + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- The P space's base. -/
abbrev GP.pS (G : GP) : Addr := off G.scr pB

/-- The certificate of `powC`. -/
abbrev CertC (pLen qLen : Nat) : Prop := ∃ hc, (VG.Taint.check VG.PPC64LE.taint
  (Taint.ofRegs [.r28, .r12, .r6, .r10, .r11, .r21, .r23, .r29, .r31]) (powC pLen qLen) hc).isSome = true

section
variable {G : GP} {STK : Nat} {σ : State} {V : Nat → BitVec 64} {LS : List Nat} {s : State}

theorem GI.pBig (h : GI G STK σ V LS s) : pB + pZ G.pLen ≤ G.scrLen * 8 ∧ pB ≤ kB G.pLen := by
  have := h.wBig; have := h.kBig
  have : pB ≤ kB G.pLen := by rcases h.lens3 with e | e | e <;> rw [e] <;> decide
  exact ⟨by simp only [pZ]; omega, this⟩

/-- A range of `scratch` as a working space. -/
theorem GI.scrAt (h : GI G STK σ V LS s) {o n : Nat} (ho : o + n ≤ G.scrLen * 8) (hn : 0 < n) : Scr s (off G.scr o) n := by
  have := h.scrFit
  refine ⟨⟨G.scr, o, G.scrLen * 8, by rw [h.wr, h.pre.wr, h.hG]; simp, rfl, ho, by omega⟩, ?_⟩
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show o < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- The bytes of `scratch` at `a`, below the P space, as a source of a load into it. -/
theorem GI.srcBelow (h : GI G STK σ V LS s) {a n : Nat} (ha : a + n ≤ pB) :
    (∀ i < n, InRegions (s.rd ++ s.wr) (off (off G.scr a) i) 1) ∧
      ∀ i < n, ∀ x, VG.Proof.Bignum.ofs G.pS x < pZ G.pLen → off (off G.scr a) i ≠ x := by
  have ⟨pb, _⟩ := h.pBig
  have fit := h.scrFit
  refine ⟨fun i hi => ?_, fun i hi x hx e => ?_⟩
  · rw [show off (off G.scr a) i = G.sa (a + i) from G.sa_add a i]
    exact h.inRdWr (by omega)
  · subst e
    have d : (off (off G.scr a) i - G.scr).toNat = a + i := by
      rw [show off (off G.scr a) i = G.scr + BitVec.ofNat 64 (a + i) from G.sa_add a i, Offset.add_sub_cancel_left,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have : pZ G.pLen ≤ VG.Proof.Bignum.ofs G.pS (off (off G.scr a) i) :=
      le_ofs_off (S := G.scr) (a := pB) (by decide) (by omega) (.inl (by omega))
    omega

end

/-- Bytes apart from `scratch` are apart from the P space. -/
theorem src_apart {G : GP} {H : Addr} {n : Nat} (hd : Region.Disjoint ⟨H, n⟩ G.rScr) (hfit : H.toNat + n ≤ 2 ^ 64)
    (hp : pB + pZ G.pLen ≤ G.scrLen * 8) :
    ∀ i < n, ∀ x, VG.Proof.Bignum.ofs G.pS x < pZ G.pLen → off H i ≠ x := by
  intro i hi x hx e
  subst e
  have := past_of_disjoint' hd (a := off H i) (Offset.contains_base _ (show i + 1 ≤ n by omega) (by omega))
  have : pZ G.pLen ≤ VG.Proof.Bignum.ofs G.pS (off H i) :=
    le_ofs_off (S := G.scr) (a := pB) (by decide) (by omega) (.inr (by omega))
  omega

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- A step that writes the P space alone keeps a stage whose claims are apart from it. -/
theorem SS.of_pspace {σ s t : State} {ws : List Reg} (h : SS G 176 σ c s) (k : BKeep ws s t)
    {lo n : Nat} (o : VG.Proof.Bignum.Outside G.pS lo n s.mem t.mem) (hn : lo + n ≤ pZ G.pLen)
    (hcl : ∀ x ∈ c.cl, Apart pB (pZ G.pLen) x) (h28 : .r28 ∉ ws := by decide) : SS G 176 σ c t := by
  have ⟨pb, pk⟩ := h.gi.pBig
  have hE := h.gi.hEnd_le
  have f0 : Frame [G.rs pB (pZ G.pLen)] s.mem t.mem :=
    frame_of_outside (L := pZ G.pLen) (o.mono (Nat.zero_le _) (by omega))
  have f : Frame (G.rss [(pB, pZ G.pLen)] ++ [rBelow σ 176]) s.mem t.mem :=
    f0.mono fun r hr => List.mem_append_left _ hr
  exact h.of_scrs (ws := ws) ⟨k.gpr, k.rd, k.wr⟩ k.sp (os := [(pB, pZ G.pLen)])
    (fun p hp => by
      rw [List.mem_singleton] at hp; subst hp
      refine ⟨by simp only [hEnd, fSave, pB]; omega, .inl (by simp only [List.length_replicate, pZ]; omega),
        by simp only [List.length_replicate]; omega⟩) f (cl' := c.cl)
    (fun x hx => .inl ⟨hx, fun p hp => by rw [List.mem_singleton] at hp; subst hp; exact hcl x hx⟩) h28

/-- After `powA`: p in array 0, its word `w` zero, and `R² mod p` in array 1. -/
abbrev PA (G : GP) (c : Cfg) (X : State → Prop) (pv : Nat) (σ s : State) : Prop :=
  St G c X σ s ∧ Env s G.pS (pZ G.pLen) (pw G.pLen) ∧ s.gpr .r21 = G.pS ∧ s.gpr .r23 = G.pS ∧
    arr s.mem G.pS (pw G.pLen) 0 = pv ∧ word s.mem G.pS (slot (pw G.pLen) 0 + 8 * pw G.pLen) = 0 ∧
    arr s.mem G.pS (pw G.pLen) 1 = 2 ^ (128 * pw G.pLen) % pv

/-- p from `sPBE` into the P space. -/
theorem powA_vp {pv : Nat} (hPc : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c.cl) (hpv : pv < 256 ^ G.pLen)
    (hp2 : 2 ≤ pv) (hcl : ∀ x ∈ c.cl, Apart pB (pZ G.pLen) x) :
    VP (St G c X) (powA G.pLen) (PA G c X pv) := by
  refine VP.pub (SS.pub fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (powA G.pLen), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_
  have gi := h.gi
  have ⟨pb, _⟩ := gi.pBig
  have l := gi.lens3
  have hb' : Spec.Rsa.bytesAt s.mem (off G.scr sPBE) G.pLen = Spec.Rsa.i2osp pv G.pLen := by
    have := h.sb _ hPc
    simp only [VG.Proof.Rsa.i2osp_length] at this
    exact this
  have ev : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off G.scr sPBE) G.pLen) = pv := by
    rw [hb', VG.Proof.Rsa.os2ip_i2osp, Nat.mod_eq_of_lt hpv]
  have hsrc := gi.srcBelow (a := sPBE) (n := G.pLen) (by rcases l with e | e | e <;> rw [e] <;> decide)
  refine WP.mono (powA_ok l gi.r28 (gi.scrAt pb (by simp only [pZ]; rcases l with e | e | e <;> rw [e] <;> decide)) hsrc.1 hsrc.2 (by rw [ev]; exact hp2))
    fun t ⟨⟨en, a21, a23, v0, z0, v1, o⟩, k⟩ => ?_
  rw [ev] at v0 v1
  refine ⟨⟨h.of_pspace k o ?_ hcl, x⟩, en, a21, a23, v0, z0, v1⟩
  have hZ := pZ_eq l
  have e : ∀ j, slot (pw G.pLen) j = hdrBytes + j * (8 * (pw G.pLen + 2)) := fun _ => rfl
  rw [← hZ, e, e]; simp only [hdrBytes]; omega

/-- After `h`'s pointer and its length. -/
abbrev PE (G : GP) (c : Cfg) (X : State → Prop) (pv : Nat) (H : Addr) (σ s : State) : Prop :=
  PA G c X pv σ s ∧ s.gpr .r12 = H ∧ s.gpr .r6 = BitVec.ofNat 64 G.pLen

/-- `h`'s pointer, from the header word `fH`, and its length. -/
theorem hPtr_vp {pv : Nat} {H : Addr} (hH : fH ∈ c.LS) (hHv : c.V fH = H) :
    VP (PA G c X pv) (.block [ld .r12 fH, .li .r6 G.pLen]) (PE G c X pv H) := by
  refine VP.pub (SS.pub fun σ s h => h.1.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (.block [ld .r12 fH, .li .r6 G.pLen]), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s ⟨⟨h, x⟩, en, a21, a23, v0, z0, v1⟩ => ?_
  have l := h.lens
  have hE := h.gi.hEnd_le
  have p15 : G.pLen < 2 ^ 15 := by rcases l with e | e | e <;> rw [e] <;> decide
  refine WP.cons (s' := s.write .r12 H) ?_ (WP.cons (s' := (s.write .r12 H).write .r6 (BitVec.ofNat 64 G.pLen))
    (exec_li p15) (WP.block_nil ?_))
  · rw [show ld .r12 fH = .load .d .r12 .r28 fH from rfl, exec_load_d (by decide) ⟨by decide, by decide⟩
      (by rw [h.gi.r28]; exact h.gi.inRdWr (by simp only [hEnd, fSave, fH] at hE ⊢; omega)), h.gi.r28,
      show s.mem.readW (G.scr + BitVec.ofNat 64 fH) 64 = H from (h.gi.slotV hH).trans hHv]
  have k : BKeep [.r12, .r6] s ((s.write .r12 H).write .r6 (BitVec.ofNat 64 G.pLen)) :=
    (VG.Proof.Bignum.PPC64LE.Keep.write s .r12 H).trans (VG.Proof.Bignum.PPC64LE.Keep.write _ .r6 _)
  refine ⟨⟨⟨h.of_keep ⟨k.gpr, k.rd, k.wr⟩ rfl k.sp, x⟩, en.keep k (by decide), (k.gpr .r21 (by decide)).trans a21,
    (k.gpr .r23 (by decide)).trans a23, v0, z0, v1⟩, ?_, (Upd.write _ _ _).gpr⟩
  rw [(Upd.write _ .r6 _).other .r12 (by decide), (Upd.write _ _ _).gpr]

/-- h into array 4, its power, and the range check. -/
theorem powC_vp {pv ev : Nat} {H : Addr} {hb : List Byte} (cert : CertC G.pLen G.qLen)
    (hEc : (sE, Spec.Rsa.i2osp ev (eBytes G.pLen G.qLen)) ∈ c.cl) (hev : ev < 256 ^ eBytes G.pLen G.qLen)
    (hp2 : 2 ≤ pv) (hpo : pv % 2 = 1) (hcl : ∀ x ∈ c.cl, Apart pB (pZ G.pLen) x)
    (hsrc : ∀ σ s, St G c X σ s → (∀ i < G.pLen, InRegions (s.rd ++ s.wr) (off H i) 1) ∧
      Region.Disjoint ⟨H, G.pLen⟩ G.rScr ∧ H.toNat + G.pLen ≤ 2 ^ 64 ∧ Spec.Rsa.bytesAt s.mem H G.pLen = hb) :
    VP (PE G c X pv H) (powC G.pLen G.qLen) (fun σ t => St G c X σ t ∧ Env t G.pS (pZ G.pLen) (pw G.pLen) ∧
      arr t.mem G.pS (pw G.pLen) 4 = Spec.Rsa.os2ip hb ^ ev % pv ∧
      (t.gpr .r0 = 0 ↔ 1 < arr t.mem G.pS (pw G.pLen) 4 ∧ arr t.mem G.pS (pw G.pLen) 4 < pv)) := by
  refine VP.taint _ cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
      rw [(SS.pub (G := G) (fun σ s (h : PE G c X pv H σ s) => h.1.1.1) σ₁ s₁ h₁).2,
        (SS.pub (G := G) (fun σ s (h : PE G c X pv H σ s) => h.1.1.1) σ₂ s₂ h₂).2])
    (fun σ₁ σ₂ s₁ s₂ ⟨⟨⟨h₁, _⟩, e₁, b21, b23, _⟩, c12, c6⟩ ⟨⟨⟨h₂, _⟩, e₂, d21, d23, _⟩, f12, f6⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₁.gi.r28, h₂.gi.r28]
      · rw [c12, f12]
      · rw [c6, f6]
      · rw [e₁.h10, e₂.h10]
      · rw [e₁.h11, e₂.h11]
      · rw [b21, d21]
      · rw [b23, d23]
      · rw [e₁.h29, e₂.h29]
      · rw [e₁.h31, e₂.h31]) fun σ s ⟨⟨⟨h, x⟩, en, a21, a23, v0, z0, v1⟩, a12, a6⟩ => ?_
  have gi := h.gi
  have ⟨pb, _⟩ := gi.pBig
  have l := gi.lens
  have l3 := gi.lens3
  have heB : 1 ≤ eBytes G.pLen G.qLen ∧ eBytes G.pLen G.qLen < 2 ^ 15 ∧ sE + eBytes G.pLen G.qLen ≤ pB := by
    simp only [eBytes]; rcases l with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> decide
  have hEb : Spec.Rsa.bytesAt s.mem (off G.scr sE) (eBytes G.pLen G.qLen) =
      Spec.Rsa.i2osp ev (eBytes G.pLen G.qLen) := by
    have := h.sb _ hEc
    simp only [VG.Proof.Rsa.i2osp_length] at this
    exact this
  have ev' : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off G.scr sE) (eBytes G.pLen G.qLen)) = ev := by
    rw [hEb, VG.Proof.Rsa.os2ip_i2osp, Nat.mod_eq_of_lt hev]
  obtain ⟨hrd, hdj, hfit, hbs⟩ := hsrc σ s ⟨h, x⟩
  have hE := gi.srcBelow (a := sE) (n := eBytes G.pLen G.qLen) heB.2.2
  refine WP.mono (powC_ok l3 en a23 gi.r28 a12 a6 hrd (src_apart hdj hfit pb) heB.1 heB.2.1 hE.1 hE.2 v0 z0 hp2
    hpo v1) fun t ⟨⟨v4, r0, en', o⟩, k⟩ => ?_
  rw [ev', hbs] at v4
  refine ⟨⟨h.of_pspace k o ?_ hcl, x⟩, en', v4, r0⟩
  have hZ := pZ_eq l3
  have e : ∀ j, slot (pw G.pLen) j = hdrBytes + j * (8 * (pw G.pLen + 2)) := fun _ => rfl
  rw [← hZ, e, e]; simp only [hdrBytes]; omega

/-- `power`: `h^e mod p` into array 4 of the P space, for p at `sPBE`, `e`
at `sE` and `h` at the header word `fH`, and `r0 = 0` exactly when it is
above 1 and below p. -/
theorem power_vp {pv ev : Nat} {H : Addr} {hb : List Byte} (cert : CertC G.pLen G.qLen)
    (hPc : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c.cl) (hpv : pv < 256 ^ G.pLen) (hp2 : 2 ≤ pv) (hpo : pv % 2 = 1)
    (hEc : (sE, Spec.Rsa.i2osp ev (eBytes G.pLen G.qLen)) ∈ c.cl) (hev : ev < 256 ^ eBytes G.pLen G.qLen)
    (hH : fH ∈ c.LS) (hHv : c.V fH = H) (hcl : ∀ x ∈ c.cl, Apart pB (pZ G.pLen) x)
    (hsrc : ∀ σ s, St G c X σ s → (∀ i < G.pLen, InRegions (s.rd ++ s.wr) (off H i) 1) ∧
      Region.Disjoint ⟨H, G.pLen⟩ G.rScr ∧ H.toNat + G.pLen ≤ 2 ^ 64 ∧ Spec.Rsa.bytesAt s.mem H G.pLen = hb) :
    VP (St G c X) (power G.pLen G.qLen) (fun σ t => St G c X σ t ∧ Env t G.pS (pZ G.pLen) (pw G.pLen) ∧
      arr t.mem G.pS (pw G.pLen) 4 = Spec.Rsa.os2ip hb ^ ev % pv ∧
      (t.gpr .r0 = 0 ↔ 1 < arr t.mem G.pS (pw G.pLen) 4 ∧ arr t.mem G.pS (pw G.pLen) 4 < pv)) :=
  VP.assoc (VP.assoc (VP.assoc (VP.seq (powA_vp hPc hpv hp2 hcl)
    (VP.seq (hPtr_vp hH hHv) (powC_vp cert hEc hev hp2 hpo hcl hsrc)))))

/-- `g`, array 4 of the P space, big-endian at `sG`. -/
theorem gStore_vp {g : Nat} (hg : g < 2 ^ (8 * G.pLen)) (hcl : ∀ x ∈ c.cl, Apart sG G.pLen x) :
    VP (fun σ s => St G c X σ s ∧ Env s G.pS (pZ G.pLen) (pw G.pLen) ∧ arr s.mem G.pS (pw G.pLen) 4 = g)
      (.seq (.block [scr .r12 sG, .li .r6 G.pLen]) (VG.Impl.Dsa.PPC64LE.storeBE 4))
      (St G { c with cl := (sG, Spec.Rsa.i2osp g G.pLen) :: c.cl } X) := by
  refine VP.pub (SS.pub fun σ s h => h.1.1) [.r10, .r29] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28, .r10, .r29]) (.seq (.block [scr .r12 sG, .li .r6 G.pLen]) (VG.Impl.Dsa.PPC64LE.storeBE 4)),
    by kernel_rfl⟩ (fun σ₁ σ₂ s₁ s₂ ⟨_, e₁, _⟩ ⟨_, e₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [e₁.h10, e₂.h10]
      · rw [e₁.h29, e₂.h29]) fun σ s ⟨⟨h, x⟩, en, v4⟩ => ?_
  have gi := h.gi
  have l := gi.lens3
  have ⟨pb, pk⟩ := gi.pBig
  have hE := gi.hEnd_le
  have hl : G.pLen < 2 ^ 15 ∧ 1 ≤ G.pLen ∧ G.pLen ≤ 8 * pw G.pLen ∧ sG + G.pLen ≤ pB := by
    rcases l with e | e | e <;> rw [e] <;> decide
  refine WP.seq (WP.cons (s' := s.write .r12 (off G.scr sG)) ?_ (WP.cons
    (s' := (s.write .r12 (off G.scr sG)).write .r6 (BitVec.ofNat 64 G.pLen)) (exec_li hl.1) (WP.block_nil ?_)))
  · rw [show scr .r12 sG = .addi .r12 .r28 sG from rfl, exec_addi (by decide) (by decide), gi.r28]
  have k : BKeep [.r12, .r6] s ((s.write .r12 (off G.scr sG)).write .r6 (BitVec.ofNat 64 G.pLen)) :=
    (VG.Proof.Bignum.PPC64LE.Keep.write s .r12 _).trans (VG.Proof.Bignum.PPC64LE.Keep.write _ .r6 _)
  refine WP.mono (VG.Proof.Dsa.PPC64LE.storeBE_ok (j := 4) (O := off G.scr sG) (k := G.pLen)
    (en.keep k (by decide)) (by decide) ((gi.scrAt (o := sG) (n := G.pLen) (by omega) hl.2.1).congr k.wr)
    (by rw [(Upd.write _ .r6 _).other .r12 (by decide), (Upd.write _ _ _).gpr]) (Upd.write _ _ _).gpr hl.2.1
    hl.2.2.1 ?_) fun t ⟨⟨vt, ot⟩, kt⟩ => ?_
  · intro x hx
    have fit := gi.scrFit
    have e := Offset.toNat_sub_add x G.scr (d := sG) (by decide)
    have hlt := (x - G.scr).isLt
    change (x - (G.scr + BitVec.ofNat 64 sG)).toNat < G.pLen at hx
    rw [e] at hx
    exact le_ofs_off (by decide) (by omega) (.inl (by
      by_cases hy : sG ≤ (x - G.scr).toNat
      · rw [show 2 ^ 64 - sG + (x - G.scr).toNat = (x - G.scr).toNat - sG + 2 ^ 64 by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)] at hx
        omega
      · rw [Nat.mod_eq_of_lt (by omega)] at hx; omega))
  have kk := k.trans kt
  have bt : Spec.Rsa.bytesAt t.mem (off G.scr sG) G.pLen = Spec.Rsa.i2osp g G.pLen := by
    have e1 : Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (off G.scr sG) G.pLen) = g := by
      rw [vt, VG.Proof.Dsa.PPC64LE.read_low _ _ hl.2.2.1 (by
        show arr s.mem G.pS (pw G.pLen) 4 < _; rw [v4]; exact hg)]
      exact v4
    have := VG.Proof.Rsa.i2osp_os2ip (Spec.Rsa.bytesAt t.mem (off G.scr sG) G.pLen)
    rw [e1, show (Spec.Rsa.bytesAt t.mem (off G.scr sG) G.pLen).length = G.pLen by simp [Spec.Rsa.bytesAt]] at this
    exact this.symm
  have f0 : Frame [G.rs sG G.pLen] s.mem t.mem := frame_of_outside (L := G.pLen) ot
  refine ⟨h.of_scrs (ws := [.r12, .r6] ++ VG.Proof.Dsa.PPC64LE.storeRegs) ⟨kk.gpr, kk.rd, kk.wr⟩ kk.sp
    (os := [(sG, G.pLen)]) (fun p hp => by
      rw [List.mem_singleton] at hp; subst hp
      refine ⟨by show hEnd ≤ sG; decide, .inl (by simp only [List.length_replicate]; omega),
        by simp only [List.length_replicate]; omega⟩)
    (f0.mono fun r hr => List.mem_append_left _ hr) (fun y hy => ?_), x⟩
  rcases List.mem_cons.mp hy with rfl | hy
  · refine .inr ⟨by simp only [VG.Proof.Rsa.i2osp_length]; exact bt, ?_⟩
    refine ⟨by show hEnd ≤ sG; decide, .inl (by simp only [VG.Proof.Rsa.i2osp_length]; omega),
      by simp only [VG.Proof.Rsa.i2osp_length]; omega⟩
  · exact .inl ⟨hy, fun p hp => by rw [List.mem_singleton] at hp; subst hp; exact hcl y hy⟩

/-- `g` stored, and `fG` := 1. -/
theorem gOut_vp {g : Nat} (hg : g < 2 ^ (8 * G.pLen)) (hcl : ∀ x ∈ c.cl, Apart sG G.pLen x) :
    VP (fun σ s => St G c X σ s ∧ Env s G.pS (pZ G.pLen) (pw G.pLen) ∧ arr s.mem G.pS (pw G.pLen) 4 = g)
      (VG.Impl.Rsa.PPC64LE.Keys.seqs [.block [scr .r12 sG, .li .r6 G.pLen], VG.Impl.Dsa.PPC64LE.storeBE 4, .block (stImm fG 1)])
      (St G ({ c with cl := (sG, Spec.Rsa.i2osp g G.pLen) :: c.cl }.setV fG 1) X) :=
  VP.assoc (VP.seq (gStore_vp hg hcl) (stImm_vp (o := fG) (v := 1) (fun σ s h => h.1) (by decide) (varOk_of (by decide))
    fun σ s t h h' _ => ⟨h', h.2⟩))

end

end VG.Proof.Dsa.PPC64LE.Gen
