import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCTBase
import VerifiedGarbage.Proof.RsaPss.AArch64.MgfCT

/-!
# RSASSA-PSS verification on AArch64: the checks of `EM` are constant time

After the call, each run is described by the registers and slots of the
frame that the anchor's public data fix (`VR`), and by what it knows of its
own secrets: the position of the salt (`pos`, in `sPos`), the bytes of `Y`
that are zero, and the length of `M'` (in `x22`). The pieces are checked by
the taint analysis from the registers `VR` fixes; the loads of the digest's
address and of `any_salt_len` are related by correctness; the hash is
`ctHash_ct` and MGF1 is `mgfXor_ct`.
-/

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil eval_zero eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked Two Pins two_taint two_post two_map two_ite pdCallCT wp_ldrSp)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64.Sgn (kR fb frame_sub0)

/-! ## The public values -/

abbrev kV (a : State) : Nat := (a.gpr .x1).toNat
abbrev loA (a : State) : Nat := loV (nxV a)
abbrev dbA (D : Nat) (a : State) : Nat := kV a - loA a - D - 1
abbrev cbA (a : State) : Byte := (maskV (nxV a)).setWidth 8
abbrev nbA (H : Hash) (a : State) : Nat := (dbA H.D a + 7 + H.D + H.P.L) / H.P.B + 1

/-- The encoding fits: the checks passed. -/
structure VOk (D : Nat) (a : State) : Prop where
  k1 : 64 ≤ kV a
  k2 : kV a ≤ 1024
  fit : D + 2 ≤ kV a - loA a
  lo : loA a ≤ 1

/-- A run after the call, from an entry state with the anchor's public data:
the frame and the working space, and registers (`rs`) and slots (`sl`) the
anchor fixes. -/
structure VR (D K : Nat) (rs : List (Reg × (State → BitVec 64))) (sl : List (Nat × (State → BitVec 64)))
    (a t : State) : Prop where
  ex : ∃ s, E D K a s ∧ t.rd = s.rd ∧ t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  L : Lay t (fb a) (scr a)
  r : ∀ q ∈ rs, t.gpr q.1 = q.2 a
  sl : ∀ q ∈ sl, t.mem.readW (off (fb a) q.1) 64 = q.2 a
  ok : VOk D a

namespace VR
variable {D K : Nat} {rs rs' : List (Reg × (State → BitVec 64))} {sl sl' : List (Nat × (State → BitVec 64))}

theorem pins {qs : List Reg} {X : State → State → Prop} (h : ∀ r ∈ qs, r = .x20 ∨ ∃ f, (r, f) ∈ rs) :
    Pins (fun a u => VR D K rs sl a u ∧ X a u) qs :=
  fun a s₁ s₂ h₁ h₂ => by
    refine ⟨by rw [h₁.1.L.sp, h₂.1.L.sp], fun r hr => ?_⟩
    rcases h r hr with rfl | ⟨f, hf⟩
    · rw [h₁.1.L.x20, h₂.1.L.x20]
    · rw [h₁.1.r _ hf, h₂.1.r _ hf]

theorem pins' {qs : List Reg} (h : ∀ r ∈ qs, r = .x20 ∨ ∃ f, (r, f) ∈ rs) : Pins (VR D K rs sl) qs :=
  fun a s₁ s₂ h₁ h₂ => pins (X := fun _ _ => True) h a s₁ s₂ ⟨h₁, trivial⟩ ⟨h₂, trivial⟩

variable {a u u' : State} (h : VR D K rs sl a u)
include h

theorem congr (sp : u'.sp = u.sp) (rd : u'.rd = u.rd) (wr : u'.wr = u.wr) (h20 : u'.gpr .x20 = u.gpr .x20)
    (hr : ∀ q ∈ rs', u'.gpr q.1 = q.2 a) (hs : ∀ q ∈ sl', u'.mem.readW (off (fb a) q.1) 64 = q.2 a) :
    VR D K rs' sl' a u' where
  ex := let ⟨s, e, hrd, hwr⟩ := h.ex; ⟨s, e, rd.trans hrd, wr.trans hwr⟩
  L := h.L.congr sp wr h20
  r := hr
  sl := hs
  ok := h.ok

theorem keep {ks : List Reg} (k : Keep ks u u') (hk : ∀ q ∈ rs, q.1 ∉ ks) (h20 : Reg.x20 ∉ ks)
    {ws : List Region} (hf : Frame ws u.mem u'.mem)
    (hs : ∀ q ∈ sl, ∀ r ∈ ws, Region.Disjoint (slotR (fb a) q.1) r) : VR D K rs sl a u' :=
  h.congr k.sp k.rd k.wr (k.gpr .x20 h20) (fun q hq => by rw [k.gpr q.1 (hk q hq)]; exact h.r q hq)
    fun q hq => by rw [slot_keep hf (hs q hq)]; exact h.sl q hq

theorem only {ks : List Reg} (o : Only ks u u') (hk : ∀ q ∈ rs, q.1 ∉ ks) (h20 : Reg.x20 ∉ ks) :
    VR D K rs sl a u' :=
  h.congr o.sp o.rd o.wr (o.get .x20 h20) (fun q hq => by rw [o.get q.1 (hk q hq)]; exact h.r q hq)
    fun q hq => by rw [o.mem]; exact h.sl q hq

/-- The digest is readable and apart from our working space. -/
theorem dig : (∀ j < D, InRegions (u.rd ++ u.wr) (a.gpr .x4 + BitVec.ofNat 64 j) 1) ∧
    Region.Disjoint ⟨a.gpr .x4, D⟩ ⟨scr a, oRsa⟩ := by
  obtain ⟨s, e, hrd, hwr⟩ := h.ex
  have hp := e.1
  rw [← e.gpr (r := .x4) (by decide), ← e.scr]
  refine ⟨fun j hj => ?_, hp.dgs.sub_right (rsa_sub hp)⟩
  rw [hrd, hwr]
  exact Covers.left (Covers.trans (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; simp) hp.hrd) _ _
    ⟨dgR D s, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by have := hp.wdg; omega)⟩

end VR

/-- The registers of the checks: `st`, the digest, `k`, `DB` and `dbLen`. -/
def vregs (D : Nat) : List (Reg × (State → BitVec 64)) :=
  [(.x19, fun a => off (scr a) oSt), (.x21, fun a => off (scr a) oDig), (.x23, fun a => a.gpr .x1),
    (.x24, fun a => off (scr a) (oEm + loA a)), (.x25, fun a => BitVec.ofNat 64 (dbA D a))]

/-- The slots they read: `lo`, the mask, `any_salt_len`, `salt_len` and the
digest's address. -/
def vslots : List (Nat × (State → BitVec 64)) :=
  [(sLo, fun a => BitVec.ofNat 64 (loA a)), (sC, fun a => (cbA a).setWidth 64), (sAny, fun a => anyV a),
    (sSaltLen, fun a => a.gpr .x7), (sDig, fun a => a.gpr .x4)]

theorem vregs_fst {D : Nat} {q : Reg × (State → BitVec 64)} (hq : q ∈ vregs D) :
    q.1 ∈ [Reg.x19, .x21, .x23, .x24, .x25] := by
  simp only [vregs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp

theorem nk_of {D : Nat} {ks : List Reg} (h : ∀ r ∈ [Reg.x19, .x21, .x23, .x24, .x25], r ∉ ks) :
    ∀ q ∈ vregs D, q.1 ∉ ks :=
  fun _ hq => h _ (vregs_fst hq)

theorem vslots_fb : ∀ q ∈ vslots, q.1 + 8 ≤ frameBytes := by
  intro q hq
  simp only [vslots, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The slots are apart from `pos`', `nbm`'s and `done`'s. -/
theorem vslots_d {F : Addr} : ∀ q ∈ vslots, ∀ d ∈ [sPos, sNb, sDone], Region.Disjoint (slotR F q.1) (slotR F d) := by
  intro q hq d hd
  simp only [vslots, List.mem_cons, List.not_mem_nil, or_false] at hq hd
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;>
    exact Offset.disjoint _ (by decide) (by decide) (by decide)

theorem vslots_S {F S : Addr} {t : State} (L : Lay t F S) :
    ∀ q ∈ vslots, ∀ r ∈ [(⟨S, oRsa⟩ : Region)], Region.Disjoint (slotR F q.1) r := fun q hq r hr => by
  rw [List.mem_singleton.mp hr]; exact L.dFS.sub_left (Offset.sub_base F (vslots_fb q hq))

theorem vslots_sNb {F : Addr} : ∀ q ∈ vslots, ∀ r ∈ [slotR F sNb], Region.Disjoint (slotR F q.1) r :=
  fun q hq r hr => by rw [List.mem_singleton.mp hr]; exact vslots_d q hq sNb (by simp)

theorem vslots_sPos {F : Addr} : ∀ q ∈ vslots, ∀ r ∈ [slotR F sPos], Region.Disjoint (slotR F q.1) r :=
  fun q hq r hr => by rw [List.mem_singleton.mp hr]; exact vslots_d q hq sPos (by simp)

theorem sPos_S {F S : Addr} {t : State} (L : Lay t F S) : ∀ r ∈ [(⟨S, oRsa⟩ : Region)],
    Region.Disjoint (slotR F sPos) r :=
  L.slotSd (by decide)

section
variable {D K : Nat} {rs : List (Reg × (State → BitVec 64))} {sl : List (Nat × (State → BitVec 64))}

/-- Facts of `VR vregs vslots`, by name. -/
theorem VR.x19 {a u : State} (h : VR D K (vregs D) sl a u) : u.gpr .x19 = off (scr a) oSt :=
  h.r (.x19, fun a => off (scr a) oSt) (by simp [vregs])
theorem VR.x21 {a u : State} (h : VR D K (vregs D) sl a u) : u.gpr .x21 = off (scr a) oDig :=
  h.r (.x21, fun a => off (scr a) oDig) (by simp [vregs])
theorem VR.x23 {a u : State} (h : VR D K (vregs D) sl a u) : u.gpr .x23 = BitVec.ofNat 64 (kV a) := by
  rw [h.r (.x23, fun a => a.gpr .x1) (by simp [vregs]), BitVec.ofNat_toNat, BitVec.setWidth_eq]
theorem VR.x24 {a u : State} (h : VR D K (vregs D) sl a u) : u.gpr .x24 = off (scr a) (oEm + loA a) :=
  h.r (.x24, fun a => off (scr a) (oEm + loA a)) (by simp [vregs])
theorem VR.x25 {a u : State} (h : VR D K (vregs D) sl a u) : u.gpr .x25 = BitVec.ofNat 64 (dbA D a) :=
  h.r (.x25, fun a => BitVec.ofNat 64 (dbA D a)) (by simp [vregs])

theorem VR.slo {a u : State} (h : VR D K rs vslots a u) : u.mem.readW (off (fb a) sLo) 64 = BitVec.ofNat 64 (loA a) :=
  h.sl (sLo, fun a => BitVec.ofNat 64 (loA a)) (by simp [vslots])
theorem VR.sc {a u : State} (h : VR D K rs vslots a u) : u.mem.readW (off (fb a) sC) 64 = (cbA a).setWidth 64 :=
  h.sl (sC, fun a => (cbA a).setWidth 64) (by simp [vslots])
theorem VR.sany {a u : State} (h : VR D K rs vslots a u) : u.mem.readW (off (fb a) sAny) 64 = anyV a :=
  h.sl (sAny, fun a => anyV a) (by simp [vslots])
theorem VR.ssl {a u : State} (h : VR D K rs vslots a u) : u.mem.readW (off (fb a) sSaltLen) 64 = a.gpr .x7 :=
  h.sl (sSaltLen, fun a => a.gpr .x7) (by simp [vslots])
theorem VR.sdig {a u : State} (h : VR D K rs vslots a u) : u.mem.readW (off (fb a) sDig) 64 = a.gpr .x4 :=
  h.sl (sDig, fun a => a.gpr .x4) (by simp [vslots])

/-- The bounds of `VOk`, for `omega`. -/
theorem VOk.db {a : State} (h : VOk D a) :
    dbA D a + D + 1 + loA a = kV a ∧ 1 ≤ dbA D a ∧ dbA D a ≤ 1024 ∧ kV a ≤ 1024 ∧ loA a ≤ 1 := by
  have := h.fit; have := h.k2; have := h.lo
  show kV a - loA a - D - 1 + D + 1 + loA a = kV a ∧ 1 ≤ kV a - loA a - D - 1 ∧ kV a - loA a - D - 1 ≤ 1024 ∧
    kV a ≤ 1024 ∧ loA a ≤ 1
  omega

end

/-! ## The pieces -/

/-- `pos` is in its slot. -/
def PS (D : Nat) (a u : State) : Prop := ∃ pos, pos < dbA D a ∧ u.mem.readW (off (fb a) sPos) 64 = BitVec.ofNat 64 pos

/-- The bytes `[n, 2048)` of `Y` are zero. -/
def Z (n : Nat) (a u : State) : Prop := ∀ i, n ≤ i → i < 2048 → u.mem (off (scr a) (oY + i)) = 0

theorem acc0_vct {D K : Nat} :
    RelCT isa (Two (VR D K (vregs D) vslots)) (.block acc0) (Two (VR D K (vregs D) vslots)) :=
  two_post (two_taint [.x20, .x23, .x24] (VR.pins' fun r hr => by
      simp at hr; rcases hr with rfl | rfl | rfl <;> simp [vregs]) (by taint_decide))
    fun a u h => by
      have ok := h.ok; have := ok.k1; have := ok.k2
      exact WP.mono (acc0_ok h.L (fun _ _ => rfl) (k := kV a) (lo := loA a) (by omega) ok.k2 ok.lo h.x23 h.x24
        h.slo h.sc) fun _ ⟨O, _⟩ => h.only O (nk_of (by decide)) (by decide)

section
variable {H : Hash} (hH : HashOK H)

include hH in
theorem mgfXor_vct {K : Nat} {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x) (hGl : G.len = H.D)
    (hG : Proof.Mgf1.Valid G) (hc : PssChecks H.P H.D) :
    RelCT isa (Two (VR H.D K (vregs H.D) vslots)) (mgfXor H) (Two (VR H.D K (vregs H.D) vslots)) := by
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have hd : ∀ a : State, VOk H.D a → DbAt H.D (oEm + loA a) (dbA H.D a) := fun a ok => by
    have := ok.db
    exact ⟨by omega, by omega, by omega⟩
  refine two_post (two_map (fun a => (⟨fb a, scr a, oEm + loA a, dbA H.D a⟩ : MA))
    (fun a u h => ⟨h.L, hd a h.ok, h.x19, h.x21, h.x24, h.x25⟩) (mgfXor_ct hH hGh hGl hG hc))
    fun a u h => WP.mono (mgfXor_ok hH hGh hGl hG h.L (fun _ _ => rfl) (hd a h.ok) h.x19 h.x21 h.x24 h.x25)
      fun u' ⟨sp, rd, wr, cs, _, fr, _⟩ => h.congr sp rd wr (cs .x20 (by decide)) (fun q hq => ?_) fun q hq => ?_
  · rw [cs q.1 ((by decide : ∀ r ∈ [Reg.x19, .x21, .x23, .x24, .x25], r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25,
      .x26]) _ (vregs_fst hq))]
    exact h.r q hq
  · rw [slot_keep fr (h.L.slotW (vslots_fb q hq) ?_ ?_)]
    · exact h.sl q hq
    · simp only [vslots, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [vslots, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide

end

theorem clearTop_vct {D K : Nat} :
    RelCT isa (Two (VR D K (vregs D) vslots)) (.block clearTop) (Two (VR D K (vregs D) vslots)) :=
  two_post (two_taint [.x24] (VR.pins' fun r hr => by simp at hr; subst hr; simp [vregs]) (by taint_decide))
    fun a u h => by
      have := h.ok.lo
      exact WP.mono (clearTop_ok h.L (fun _ _ => rfl) (e := oEm + loA a) (c := cbA a) h.x24
        (by unfold oEm oRsa; omega) h.sc) fun _ ⟨k, f, _⟩ =>
          h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L)

theorem posScan_vct {D K : Nat} :
    RelCT isa (Two (VR D K (vregs D) vslots)) posScan
      (Two fun a u => VR D K (vregs D) vslots a u ∧ ∃ pos, pos < dbA D a ∧ u.gpr .x14 = BitVec.ofNat 64 pos) :=
  two_post (two_taint [.x24, .x25] (VR.pins' fun r hr => by
      simp at hr; rcases hr with rfl | rfl <;> simp [vregs]) (by taint_decide))
    fun a u h => by
      have := h.ok.db; have := h.ok.lo
      exact WP.mono (posScan_ok h.L (fun _ _ => rfl) (e := oEm + loA a) (db := dbA D a) (by unfold oEm oRsa; omega)
        (by omega) h.x24 h.x25) fun _ ⟨O, _, x14, _⟩ =>
          ⟨h.only O (nk_of (by decide)) (by decide), _, nz_lt (by omega), x14⟩

theorem posCheck_vct {D K : Nat} :
    RelCT isa (Two fun a u => VR D K (vregs D) vslots a u ∧ ∃ pos, pos < dbA D a ∧ u.gpr .x14 = BitVec.ofNat 64 pos)
      posCheck (Two fun a u => VR D K (vregs D) vslots a u ∧ PS D a u) := by
  refine two_post ?_ fun a u ⟨h, pos, hpos, x14⟩ => WP.mono (posCheck_ok h.L rfl x14 rfl rfl h.x25 hpos h.sany h.ssl)
    fun t ⟨k, hm, _⟩ => ⟨h.keep k (nk_of (by decide)) (by decide) (by rw [hm]; exact frame_slot _ _ sPos _)
      vslots_sPos, pos, hpos, by rw [hm, Mem.readW_writeW_self64]⟩
  unfold posCheck
  refine two_step (Ψ := fun a t => t.sp = fb a ∧ t.gpr .x9 = anyV a)
    (two_taint [] (pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h₁.1.L.sp, h₂.1.L.sp]) (by taint_decide))
    (fun a u ⟨h, pos, hpos, x14⟩ => WP.mono (posCheckBlk_ok h.L rfl x14 rfl rfl h.x25 hpos h.sany)
      fun t ⟨k, _, _, _, x9⟩ => ⟨by rw [k.sp, h.L.sp], x9⟩) ?_
  have pin : ∀ {Φ : State → State → Prop}, (∀ a t, Φ a t → t.sp = fb a) → Pins Φ [] := fun h =>
    pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h a s₁ h₁, h a s₂ h₂]
  exact two_ite (fun a s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2])
    (two_taint [] (pin fun a t h => h.1.1) (by taint_decide)) (two_taint [] (pin fun a t h => h.1.1) (by taint_decide))

theorem PS.keep {D : Nat} {a u u' : State} {F S : Addr} (L : Lay u F S) (hF : F = fb a) (h : PS D a u)
    (hf : Frame [⟨S, oRsa⟩] u.mem u'.mem) : PS D a u' :=
  let ⟨pos, hpos, e⟩ := h
  ⟨pos, hpos, by rw [← hF] at e ⊢; rw [slot_keep hf (sPos_S L)]; exact e⟩

theorem clearY_vct {D K : Nat} :
    RelCT isa (Two fun a u => VR D K (vregs D) vslots a u ∧ PS D a u) clearY
      (Two fun a u => VR D K (vregs D) vslots a u ∧ PS D a u ∧ Z 0 a u) :=
  two_post (two_taint [.x20] (VR.pins fun r hr => by simp at hr; exact .inl hr) (by taint_decide))
    fun a u ⟨h, p⟩ => WP.mono (clearY_ok h.L (fun _ _ => rfl)) fun _ ⟨k, f, R⟩ =>
      ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L), p.keep h.L rfl f, fun i _ hi => by
        rw [R _ (by unfold oY oRsa; omega)]; unfold clr; exact ite_eq_left ⟨by omega, by omega⟩⟩

section
variable {H : Hash} (hH : HashOK H)

include hH in
theorem copyDigest_vct {K : Nat} :
    RelCT isa (Two fun a u => VR H.D K (vregs H.D) vslots a u ∧ PS H.D a u ∧ Z 0 a u) (copyDigest H)
      (Two fun a u => VR H.D K (vregs H.D) vslots a u ∧ PS H.D a u ∧ Z (8 + H.D) a u) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  refine two_post (Φ := fun a u => VR H.D K (vregs H.D) vslots a u ∧ PS H.D a u ∧ Z 0 a u) ?_ fun a u hu => ?_
  rotate_left
  · obtain ⟨h, p, z⟩ := hu
    exact WP.mono (copyDigest_ok hH h.L (fun _ _ => rfl) (dig := a.gpr .x4)
      h.sdig h.dig.1 h.dig.2) fun _ ⟨k, f, R⟩ =>
        ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L), p.keep h.L rfl f, fun i hi hi' => by
          rw [R _ (by unfold oY oRsa; omega)]; unfold updL
          rw [ite_eq_right (by rw [bytesAt_length]; omega)]; exact z i (by omega) hi'⟩
  unfold copyDigest
  refine RelCT.seq_block_append (M := isa) (l₁ := [ld .x11 sDig]) ?_
  refine two_step (Ψ := fun a u => VR H.D K (vregs H.D ++ [(.x11, fun a => a.gpr .x4)]) vslots a u)
    (two_taint [] (pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h₁.1.L.sp, h₂.1.L.sp]) (by taint_decide))
    (fun a u hu => ?_)
    (two_taintE [.x11, .x20] (VR.pins' fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
      (c' := Code.eraseOff (.seq (.block [.addImm .x .x14 .x20 (oY + 8), movi .x12 zH.D])
        Impl.RsaPkcs1Sig.AArch64.copyLoop)) rfl (by taint_decide))
  obtain ⟨h, _⟩ := hu
  have nk : ∀ q ∈ vregs H.D, q.1 ∉ [Reg.x11] := nk_of (by decide)
  unfold ld
  refine wp_ldrSp (by decide) (by rw [h.L.sp]; exact h.L.fld (by decide)) fun u' o e =>
    wp_nil (h.congr o.sp o.rd o.wr (o.get .x20) (fun q hq => ?_) fun q hq => by rw [o.mem]; exact h.sl q hq)
  rcases List.mem_append.mp hq with hq | hq
  · rw [o.get q.1 (nk q hq)]; exact h.r q hq
  · rw [List.mem_singleton.mp hq, e, h.L.sp]; exact h.sdig

include hH in
theorem copyDb_vct {K : Nat} :
    RelCT isa (Two fun a u => VR H.D K (vregs H.D) vslots a u ∧ PS H.D a u ∧ Z (8 + H.D) a u) (copyDb H)
      (Two fun a u => VR H.D K (vregs H.D) vslots a u ∧ PS H.D a u ∧ Z (8 + H.D + dbA H.D a) a u) :=
  two_post (two_taintE [.x20, .x24, .x25] (VR.pins fun r hr => by
      simp at hr; rcases hr with rfl | rfl | rfl <;> simp [vregs])
    (c' := Code.eraseOff (copyDb zH)) rfl (by taint_decide))
    fun a u ⟨h, p, z⟩ => by
      have := h.ok.db; have := h.ok.lo
      exact WP.mono (copyDb_ok hH h.L (fun _ _ => rfl) (e := oEm + loA a) (db := dbA H.D a) (by omega)
        (by unfold oEm oY; omega) h.x24 h.x25) fun _ ⟨k, f, R⟩ =>
          ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L), p.keep h.L rfl f, fun i hi hi' => by
            have hDN := hH.sizes.DN; have hN := hH.N_le
            rw [R _ (by unfold oY oRsa; omega)]; unfold updL
            rw [ite_eq_right (by rw [List.length_map, List.length_range]; omega)]; exact z i (by omega) hi'⟩

/-- The length of `M'`, at most `8 + hLen + dbLen - 1`. -/
def LX (D : Nat) (a u : State) : Prop := ∃ ℓ, u.gpr .x22 = BitVec.ofNat 64 ℓ ∧ ℓ ≤ 7 + D + dbA D a

include hH in
theorem shift_vct {K : Nat} :
    RelCT isa (Two fun a u => VR H.D K (vregs H.D) vslots a u ∧ PS H.D a u ∧ Z (8 + H.D + dbA H.D a) a u) (shift H)
      (Two fun a u => VR H.D K (vregs H.D) vslots a u ∧ LX H.D a u) :=
  two_post (two_taintE [.x20, .x25] (VR.pins fun r hr => by
      simp at hr; rcases hr with rfl | rfl <;> simp [vregs])
    (c' := Code.eraseOff (shift zH)) rfl (by taint_decide))
    fun a u ⟨h, ⟨pos, hpos, hP⟩, z⟩ => by
      have := h.ok.db; have hDN := hH.sizes.DN; have hN := hH.N_le
      refine WP.mono (shift_ok H (by omega) h.L (fun _ _ => rfl)
        (W := fun m => u.mem (off (scr a) (oY + 8 + H.D + m))) hpos (by omega) (by unfold oY oRsa; omega)
        (fun m hm => ?_) h.x25 hP) fun _ ⟨k, f, _, x22⟩ =>
          ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L), _, x22, by omega⟩
      unfold zf
      by_cases hm' : m < dbA H.D a
      · rw [ite_eq_left hm']
      · rw [ite_eq_right hm']
        have := z (8 + H.D + m) (by omega) (by omega)
        rwa [show oY + (8 + H.D + m) = oY + 8 + H.D + m by omega] at this

include hH in
theorem verifyNb_vct {K : Nat} :
    RelCT isa (Two fun a u => VR H.D K (vregs H.D) vslots a u ∧ LX H.D a u) (.block (verifyNb H))
      (Two fun a u => VR H.D K (vregs H.D) (vslots ++ [(sNb, fun a => BitVec.ofNat 64 (nbA H a))]) a u ∧
        LX H.D a u) :=
  two_post (two_taintE [.x25] (VR.pins fun r hr => by simp at hr; subst hr; simp [vregs])
    (c' := Code.eraseOff (.block (verifyNb zH))) rfl (by taint_decide))
    fun a u ⟨h, ℓ, x22, hℓ⟩ => by
      have := h.ok.db
      refine WP.mono (verifyNb_ok hH h.L (db := dbA H.D a) (by omega) h.x25) fun u' ⟨k, m⟩ =>
        ⟨h.congr k.sp k.rd k.wr (k.get .x20) (fun q hq => ?_) (fun q hq => ?_), ℓ, by rw [k.get .x22]; exact x22, hℓ⟩
      · rw [k.get q.1 (nk_of (by decide) q hq)]; exact h.r q hq
      · rcases List.mem_append.mp hq with hq | hq
        · rw [m, slot_keep (frame_slot _ _ sNb _) (vslots_sNb q hq)]; exact h.sl q hq
        · rw [List.mem_singleton.mp hq, m, Mem.readW_writeW_self64]

include hH in
theorem ctHash_vct {K : Nat} (hc : PssChecks H.P H.D) :
    RelCT isa (Two fun a u => VR H.D K (vregs H.D) (vslots ++ [(sNb, fun a => BitVec.ofNat 64 (nbA H a))]) a u ∧
        LX H.D a u) (ctHash H) (Two (VR H.D K (vregs H.D) vslots)) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have hL := hH.L
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hlg : 2 ^ lgB H = H.P.B ∧ lgB H < 64 := by
    unfold lgB
    rcases hH.sizes.B with h | h <;> rw [h]
    · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
    · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide
  have hb : ∀ a : State, dbA H.D a ≤ 1024 → ∀ ℓ, ℓ ≤ 7 + H.D + dbA H.D a →
      ℓ + 1 + H.P.L ≤ nbA H a * H.P.B ∧ nbA H a * H.P.B ≤ 2048 := fun a hs ℓ hℓ => by
    have hnb1 := Nat.lt_div_mul_add (a := dbA H.D a + 7 + H.D + H.P.L) (b := H.P.B) hB0
    have hnb2 := Nat.div_mul_le_self (dbA H.D a + 7 + H.D + H.P.L) H.P.B
    have hnbB : ((dbA H.D a + 7 + H.D + H.P.L) / H.P.B + 1) * H.P.B =
        (dbA H.D a + 7 + H.D + H.P.L) / H.P.B * H.P.B + H.P.B := Nat.succ_mul _ _
    show _ ≤ ((dbA H.D a + 7 + H.D + H.P.L) / H.P.B + 1) * H.P.B ∧
      ((dbA H.D a + 7 + H.D + H.P.L) / H.P.B + 1) * H.P.B ≤ 2048
    rw [hnbB]; omega
  have nb : ∀ {a u : State}, VR H.D K (vregs H.D) (vslots ++ [(sNb, fun a => BitVec.ofNat 64 (nbA H a))]) a u →
      u.mem.readW (off (fb a) sNb) 64 = BitVec.ofNat 64 (nbA H a) := fun h =>
    h.sl (sNb, fun a => BitVec.ofNat 64 (nbA H a)) (by simp)
  refine two_post (two_map (fun a => (⟨fb a, scr a, nbA H a, none⟩ : HA)) (fun a u ⟨h, ℓ, x22, hℓ⟩ => {
      L := h.L
      x19 := h.x19
      x21 := h.x21
      nb := nb h
      len := ⟨ℓ, x22, (hb a h.ok.db.2.2.1 ℓ hℓ).1⟩
      hnb := (hb a h.ok.db.2.2.1 ℓ hℓ).2
      fx := fun _ e => nomatch e }) (ctHash_ct hH hc)) fun a u ⟨h, ℓ, x22, hℓ⟩ => ?_
  have hs := hb a h.ok.db.2.2.1 ℓ hℓ
  refine WP.mono (ctHashWith_out hH (pad80 H) h.L (fun _ _ => rfl) h.x19 h.x21 x22 (nb h) hs.1 hs.2
    fun L' R' h22' hNb' => ?_) fun u' O => ?_
  · exact WP.mono (pad80_ok H L' R' hlg.1 hlg.2 (by omega) hs.2 (by have := hs.1; omega) h22' hNb')
      fun _ ⟨k, f, r⟩ => ⟨k.mono, f, r⟩
  refine h.congr O.sp O.rd O.wr (O.cs .x20 (by decide)) (fun q hq => ?_) fun q hq => ?_
  · rw [O.cs q.1 ((by decide : ∀ r ∈ [Reg.x19, .x21, .x23, .x24, .x25], r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24,
      .x25, .x26, .x28]) _ (vregs_fst hq))]
    exact h.r q hq
  · rw [slot_keep O.fr fun r hr => ?_]
    · exact h.sl q (List.mem_append_left _ hq)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.L.dFS.sub_left (Offset.sub_base _ (vslots_fb q hq))
    · exact slot_not_below _ (vslots_fb q hq)

include hH in
theorem cmpH_vct {K : Nat} :
    RelCT isa (Two (VR H.D K (vregs H.D) vslots)) (cmpH H) (Two fun a t => t.sp = fb a) :=
  two_post (two_taintE [.x21, .x24, .x25] (VR.pins' fun r hr => by
      simp at hr; rcases hr with rfl | rfl | rfl <;> simp [vregs])
    (c' := Code.eraseOff (cmpH zH)) rfl (by taint_decide))
    fun a u h => by
      have := h.ok.db; have := h.ok.lo; have hDN := hH.sizes.DN; have hN := hH.N_le
      exact WP.mono (cmpH_ok hH h.L (fun _ _ => rfl) (e := oEm + loA a) (db := dbA H.D a) (acc := u.gpr .x26)
        (by unfold oEm oY; omega) h.x21 h.x24 h.x25 rfl) fun _ ⟨O, _⟩ => by rw [O.sp, h.L.sp]

/-- The checks of `EM` are constant time. -/
theorem check_ct {K : Nat} {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x) (hGl : G.len = H.D)
    (hG : Proof.Mgf1.Valid G) (hc : PssChecks H.P H.D) :
    RelCT isa (Two (VR H.D K (vregs H.D) vslots))
      (seqs [.block acc0, mgfXor H, .block clearTop, posScan, posCheck, clearY, copyDigest H, copyDb H, shift H,
        .block (verifyNb H), ctHash H, cmpH H]) (Two fun a t => t.sp = fb a) := by
  unfold seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  exact RelCT.seq acc0_vct (RelCT.seq (mgfXor_vct hH hGh hGl hG hc) (RelCT.seq clearTop_vct (RelCT.seq posScan_vct
    (RelCT.seq posCheck_vct (RelCT.seq clearY_vct (RelCT.seq (copyDigest_vct hH) (RelCT.seq (copyDb_vct hH)
      (RelCT.seq (shift_vct hH) (RelCT.seq (verifyNb_vct hH) (RelCT.seq (ctHash_vct hH hc) (cmpH_vct hH)))))))))))

end

end VG.Proof.RsaPss.AArch64.Vfy
