module

public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkCTBase
public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
public import VerifiedGarbage.Proof.RsaPss.AArch64.Checks
import VerifiedGarbage.Proof.RsaPss.AArch64.MgfCT
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyParts
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyB1
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyShift
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEncOk
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.RsaPss.AArch64.ChkCTBase
meta import VerifiedGarbage.Proof.RsaPss.AArch64.ChkCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Proof.RsaPss.AArch64.Checks
meta import VerifiedGarbage.Proof.RsaPss.AArch64.MgfCT
meta import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyParts
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
meta import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyB1
meta import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyShift
meta import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignEncOk
meta import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
meta import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# EMSA-PSS's check of an encoding on AArch64: the checks of `EM` are constant time

As in verification: after the copy and the checks of the lengths, each run is described by the registers and slots of the
frame that the anchor's public data fix (`VR`), and by what it knows of its
own secrets: the position of the salt (`pos`, in `sPos`), the bytes of `Y`
that are zero, and the length of `M'` (in `x22`). The pieces are checked by
the taint analysis from the registers `VR` fixes; the loads of the digest's
address and of `any_salt_len` are related by correctness; the hash is
`ctHash_ct` and MGF1 is `mgfXor_ct`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Chk

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil eval_zero eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_map two_ite wp_ldrSp)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64.Sgn (kR fb frame_sub0)

/-! ## The public values -/

abbrev kV (a : State) : Nat := (a.gpr .x2).toNat
abbrev loA (_a : State) : Nat := 0
abbrev dbA (D : Nat) (a : State) : Nat := kV a - loA a - D - 1
abbrev cbA (a : State) : Byte := cC a
abbrev nbA (H : Hash) (a : State) : Nat := (dbA H.D a + 7 + H.D + H.P.L) / H.P.B + 1

/-- The encoding fits: the checks passed. -/
structure VOk (D : Nat) (a : State) : Prop where
  k1 : 1 ≤ kV a
  k2 : kV a ≤ 1024
  fit : D + 2 ≤ kV a - loA a
  lo : loA a ≤ 1
  salt : anyC a = 0 → (a.gpr .x4).toNat < dbA D a

/-- A run after the call, from an entry state with the anchor's public data:
the frame and the working space, and registers (`rs`) and slots (`sl`) the
anchor fixes. -/
structure VR (T : Tabs) (D : Nat) (rs : List (Reg × (State → BitVec 64))) (sl : List (Nat × (State → BitVec 64)))
    (a t : State) : Prop where
  ex : ∃ s t₀, E T a s ∧ AtCT s t₀ ∧ Frame (mgfWr (fb a) (scr a) ++ [slotR (fb a) sPos]) t₀.mem t.mem ∧
    t.syms = t₀.syms ∧ t.rd = s.rd ∧ t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  L : Lay t (fb a) (scr a)
  r : ∀ q ∈ rs, t.gpr q.1 = q.2 a
  sl : ∀ q ∈ sl, t.mem.readW (off (fb a) q.1) 64 = q.2 a
  ok : VOk D a
  hD : D = T.H.D

namespace VR
variable {T : Tabs} {D : Nat} {rs rs' : List (Reg × (State → BitVec 64))} {sl sl' : List (Nat × (State → BitVec 64))}

theorem pins {qs : List Reg} {X : State → State → Prop} (h : ∀ r ∈ qs, r = .x20 ∨ ∃ f, (r, f) ∈ rs) :
    Pins (fun a u => VR T D rs sl a u ∧ X a u) qs :=
  fun a s₁ s₂ h₁ h₂ => by
    refine ⟨by rw [h₁.1.L.sp, h₂.1.L.sp], fun r hr => ?_⟩
    rcases h r hr with rfl | ⟨f, hf⟩
    · rw [h₁.1.L.x20, h₂.1.L.x20]
    · rw [h₁.1.r _ hf, h₂.1.r _ hf]

theorem pins' {qs : List Reg} (h : ∀ r ∈ qs, r = .x20 ∨ ∃ f, (r, f) ∈ rs) : Pins (VR T D rs sl) qs :=
  fun a s₁ s₂ h₁ h₂ => pins (X := fun _ _ => True) h a s₁ s₂ ⟨h₁, trivial⟩ ⟨h₂, trivial⟩

variable {a u u' : State} (h : VR T D rs sl a u)
include h

theorem congr (sp : u'.sp = u.sp) (rd : u'.rd = u.rd) (wr : u'.wr = u.wr) (h20 : u'.gpr .x20 = u.gpr .x20)
    (hr : ∀ q ∈ rs', u'.gpr q.1 = q.2 a) (hs : ∀ q ∈ sl', u'.mem.readW (off (fb a) q.1) 64 = q.2 a)
    (hsy : u'.syms = u.syms) (hfm : Frame (mgfWr (fb a) (scr a) ++ [slotR (fb a) sPos]) u.mem u'.mem) :
    VR T D rs' sl' a u' where
  ex := let ⟨s, t₀, e, h0, fm, sy, hrd, hwr⟩ := h.ex
    ⟨s, t₀, e, h0, fm.trans hfm, hsy.trans sy, rd.trans hrd, wr.trans hwr⟩
  L := h.L.congr sp wr h20
  r := hr
  sl := hs
  ok := h.ok
  hD := h.hD

theorem keep {ks : List Reg} (k : Keep ks u u') (hk : ∀ q ∈ rs, q.1 ∉ ks) (h20 : Reg.x20 ∉ ks)
    {ws : List Region} (hf : Frame ws u.mem u'.mem)
    (hs : ∀ q ∈ sl, ∀ r ∈ ws, Region.Disjoint (slotR (fb a) q.1) r) (hsy : u'.syms = u.syms)
    (hws : ∀ r ∈ ws, r ∈ mgfWr (fb a) (scr a) ++ [slotR (fb a) sPos] := by simp [mgfWr]) : VR T D rs sl a u' :=
  h.congr k.sp k.rd k.wr (k.gpr .x20 h20) (fun q hq => by rw [k.gpr q.1 (hk q hq)]; exact h.r q hq)
    (fun q hq => by rw [slot_keep hf (hs q hq)]; exact h.sl q hq) hsy (hf.mono hws)

theorem only {ks : List Reg} (o : Only ks u u') (hk : ∀ q ∈ rs, q.1 ∉ ks) (h20 : Reg.x20 ∉ ks)
    (hsy : u'.syms = u.syms) : VR T D rs sl a u' :=
  h.congr o.sp o.rd o.wr (o.get .x20 h20) (fun q hq => by rw [o.get q.1 (hk q hq)]; exact h.r q hq)
    (fun q hq => by rw [o.mem]; exact h.sl q hq) hsy (by rw [o.mem]; exact Frame.refl _ _)

/-- The digest is readable and apart from our working space. -/
theorem dig : (∀ j < D, InRegions (u.rd ++ u.wr) (a.gpr .x0 + BitVec.ofNat 64 j) 1) ∧
    Region.Disjoint ⟨a.gpr .x0, D⟩ ⟨scr a, oRsa⟩ := by
  obtain ⟨s, _, e, _, _, _, hrd, hwr⟩ := h.ex
  have hp := e.1
  have hD := h.hD
  subst hD
  rw [← e.gpr (r := .x0) (by decide), ← e.scr]
  refine ⟨fun j hj => ?_, hp.ds.sub_right (rsa_sub hp)⟩
  rw [hrd, hp.hrd]
  exact ⟨dgR T.H.D s, by simp, Offset.contains_base _ (by omega) (by have := hp.wd; omega)⟩

/-- The addresses of the tables' functions are the anchor's. -/
theorem names : ∀ n ∈ T.names, u.syms n = a.syms n := by
  obtain ⟨s, t₀, e, h0, _, sy, _, _⟩ := h.ex
  exact fun n hn => by rw [sy, h0.sy]; exact e.sym hn

/-- The slots of the table of `MdHash`. -/
theorem ht : HT T.H T.dn T.f (fb a) u.mem u.syms := by
  obtain ⟨s, t₀, e, h0, fm, sy, _, _⟩ := h.ex
  have L0 := lay_of e.1 h0.e.sp h0.e.x20 h0.e.wr
  rw [e.fb, show s.gpr .x6 = scr a from e.scr] at L0
  have h1 := ht_of e.2.2.1 h0
  rw [e.fb] at h1
  rw [sy]
  exact h1.stepWP L0 fm

/-- Where MGF1 works, and the table of `Hash`. -/
theorem env : Env T.G T.g u (fb a) (scr a) (stackArg a 1) := by
  obtain ⟨s, t₀, e, h0, fm, sy, hrd, hwr⟩ := h.ex
  have L0 := lay_of e.1 h0.e.sp h0.e.x20 h0.e.wr
  have E0 := env_of e.1 e.2.2.1 h0
  rw [e.fb, show s.gpr .x6 = scr a from e.scr] at L0 E0
  rw [e.arg (j := 1) (by decide)] at E0
  exact E0.stepP L0 fm (hrd.trans h0.e.rd.symm) (hwr.trans h0.e.wr.symm) sy

end VR

/-- The registers of the checks: `st`, the digest, `k`, `DB` and `dbLen`. -/
def vregs (D : Nat) : List (Reg × (State → BitVec 64)) :=
  [(.x19, fun a => off (scr a) oSt), (.x21, fun a => off (scr a) oDig), (.x23, fun a => a.gpr .x2),
    (.x24, fun a => off (scr a) (oEm + loA a)), (.x25, fun a => BitVec.ofNat 64 (dbA D a))]

/-- The slots they read: `lo`, the mask, `any_salt_len`, `salt_len` and the
digest's address. -/
def vslots : List (Nat × (State → BitVec 64)) :=
  [(sLo, fun a => BitVec.ofNat 64 (loA a)), (sC, fun a => (cbA a).setWidth 64), (sAny, fun a => anyC a),
    (sSaltLen, fun a => a.gpr .x4), (sDig, fun a => a.gpr .x0)]

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
variable {T : Tabs} {D : Nat} {rs : List (Reg × (State → BitVec 64))} {sl : List (Nat × (State → BitVec 64))}

/-- Facts of `VR vregs vslots`, by name. -/
theorem VR.x19 {a u : State} (h : VR T D (vregs D) sl a u) : u.gpr .x19 = off (scr a) oSt :=
  h.r (.x19, fun a => off (scr a) oSt) (by simp [vregs])
theorem VR.x21 {a u : State} (h : VR T D (vregs D) sl a u) : u.gpr .x21 = off (scr a) oDig :=
  h.r (.x21, fun a => off (scr a) oDig) (by simp [vregs])
theorem VR.x23 {a u : State} (h : VR T D (vregs D) sl a u) : u.gpr .x23 = BitVec.ofNat 64 (kV a) := by
  rw [h.r (.x23, fun a => a.gpr .x2) (by simp [vregs]), BitVec.ofNat_toNat, BitVec.setWidth_eq]
theorem VR.x24 {a u : State} (h : VR T D (vregs D) sl a u) : u.gpr .x24 = off (scr a) (oEm + loA a) :=
  h.r (.x24, fun a => off (scr a) (oEm + loA a)) (by simp [vregs])
theorem VR.x25 {a u : State} (h : VR T D (vregs D) sl a u) : u.gpr .x25 = BitVec.ofNat 64 (dbA D a) :=
  h.r (.x25, fun a => BitVec.ofNat 64 (dbA D a)) (by simp [vregs])

theorem VR.slo {a u : State} (h : VR T D rs vslots a u) : u.mem.readW (off (fb a) sLo) 64 = BitVec.ofNat 64 (loA a) :=
  h.sl (sLo, fun a => BitVec.ofNat 64 (loA a)) (by simp [vslots])
theorem VR.sc {a u : State} (h : VR T D rs vslots a u) : u.mem.readW (off (fb a) sC) 64 = (cbA a).setWidth 64 :=
  h.sl (sC, fun a => (cbA a).setWidth 64) (by simp [vslots])
theorem VR.sany {a u : State} (h : VR T D rs vslots a u) : u.mem.readW (off (fb a) sAny) 64 = anyC a :=
  h.sl (sAny, fun a => anyC a) (by simp [vslots])
theorem VR.ssl {a u : State} (h : VR T D rs vslots a u) : u.mem.readW (off (fb a) sSaltLen) 64 = a.gpr .x4 :=
  h.sl (sSaltLen, fun a => a.gpr .x4) (by simp [vslots])
theorem VR.sdig {a u : State} (h : VR T D rs vslots a u) : u.mem.readW (off (fb a) sDig) 64 = a.gpr .x0 :=
  h.sl (sDig, fun a => a.gpr .x0) (by simp [vslots])

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

theorem acc0_vct {T : Tabs} {D : Nat} :
    RelCT isa (Two (VR T D (vregs D) vslots)) (.block acc0) (Two (VR T D (vregs D) vslots)) :=
  two_post (two_taint [.x20, .x23, .x24] (VR.pins' fun r hr => by
      simp at hr; rcases hr with rfl | rfl | rfl <;> simp [vregs]) (by taint_decide))
    fun a u h => by
      have ok := h.ok; have := ok.k1; have := ok.k2
      exact WP.mono_syms (acc0_ok h.L (fun _ _ => rfl) (k := kV a) (lo := loA a) (by omega) ok.k2 ok.lo h.x23 h.x24
        h.slo h.sc) fun _ ⟨O, _⟩ sy => h.only O (nk_of (by decide)) (by decide) sy


theorem clearTop_vct {T : Tabs} {D : Nat} :
    RelCT isa (Two (VR T D (vregs D) vslots)) (.block clearTop) (Two (VR T D (vregs D) vslots)) :=
  two_post (two_taint [.x24] (VR.pins' fun r hr => by simp at hr; subst hr; simp [vregs]) (by taint_decide))
    fun a u h => by
      have := h.ok.lo
      exact WP.mono_syms (clearTop_ok h.L (fun _ _ => rfl) (e := oEm + loA a) (c := cbA a) h.x24
        (by unfold oEm oRsa; omega) h.sc) fun _ ⟨k, f, _⟩ sy =>
          h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L) sy

theorem posScan_vct {T : Tabs} {D : Nat} :
    RelCT isa (Two (VR T D (vregs D) vslots)) posScan
      (Two fun a u => VR T D (vregs D) vslots a u ∧ ∃ pos, pos < dbA D a ∧ u.gpr .x14 = BitVec.ofNat 64 pos) :=
  two_post (two_taint [.x24, .x25] (VR.pins' fun r hr => by
      simp at hr; rcases hr with rfl | rfl <;> simp [vregs]) (by taint_decide))
    fun a u h => by
      have := h.ok.db; have := h.ok.lo
      exact WP.mono_syms (posScan_ok h.L (fun _ _ => rfl) (e := oEm + loA a) (db := dbA D a)
        (by unfold oEm oRsa; omega) (by omega) h.x24 h.x25) fun _ ⟨O, _, x14, _⟩ sy =>
          ⟨h.only O (nk_of (by decide)) (by decide) sy, _, nz_lt (by omega), x14⟩

theorem posCheck_vct {T : Tabs} {D : Nat} :
    RelCT isa (Two fun a u => VR T D (vregs D) vslots a u ∧ ∃ pos, pos < dbA D a ∧ u.gpr .x14 = BitVec.ofNat 64 pos)
      posCheck (Two fun a u => VR T D (vregs D) vslots a u ∧ PS D a u) := by
  refine two_post ?_ fun a u ⟨h, pos, hpos, x14⟩ =>
    WP.mono_syms (posCheck_ok h.L rfl x14 rfl rfl h.x25 hpos h.sany h.ssl)
    fun t ⟨k, hm, _⟩ sy => ⟨h.keep k (nk_of (by decide)) (by decide) (by rw [hm]; exact frame_slot _ _ sPos _)
      vslots_sPos sy, pos, hpos, by rw [hm, Mem.readW_writeW_self64]⟩
  unfold posCheck
  refine two_step (Ψ := fun a t => t.sp = fb a ∧ t.gpr .x9 = anyC a)
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

theorem clearY_vct {T : Tabs} {D : Nat} :
    RelCT isa (Two fun a u => VR T D (vregs D) vslots a u ∧ PS D a u) clearY
      (Two fun a u => VR T D (vregs D) vslots a u ∧ PS D a u ∧ Z 0 a u) :=
  two_post (two_taint [.x20] (VR.pins fun r hr => by simp at hr; exact .inl hr) (by taint_decide))
    fun a u ⟨h, p⟩ => WP.mono_syms (clearY_ok h.L (fun _ _ => rfl)) fun _ ⟨k, f, R⟩ sy =>
      ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L) sy, p.keep h.L rfl f, fun i _ hi => by
        rw [R _ (by unfold oY oRsa; omega)]; unfold clr; exact ite_eq_left ⟨by omega, by omega⟩⟩

section
variable {T : Tabs} {H : Hash} (hH : HashOK H)

include hH in
theorem copyDigest_vct :
    RelCT isa (Two fun a u => VR T H.D (vregs H.D) vslots a u ∧ PS H.D a u ∧ Z 0 a u) (copyDigest H)
      (Two fun a u => VR T H.D (vregs H.D) vslots a u ∧ PS H.D a u ∧ Z (8 + H.D) a u) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  refine two_post (Φ := fun a u => VR T H.D (vregs H.D) vslots a u ∧ PS H.D a u ∧ Z 0 a u) ?_ fun a u hu => ?_
  rotate_left
  · obtain ⟨h, p, z⟩ := hu
    exact WP.mono_syms (copyDigest_ok hH h.L (fun _ _ => rfl) (dig := a.gpr .x0)
      h.sdig h.dig.1 h.dig.2) fun _ ⟨k, f, R⟩ sy =>
        ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L) sy, p.keep h.L rfl f, fun i hi hi' => by
          rw [R _ (by unfold oY oRsa; omega)]; unfold updL
          rw [ite_eq_right (by rw [bytesAt_length]; omega)]; exact z i (by omega) hi'⟩
  unfold copyDigest
  refine RelCT.seq_block_append (M := isa) (l₁ := [ld .x11 sDig]) ?_
  refine two_step (Ψ := fun a u => VR T H.D (vregs H.D ++ [(.x11, fun a => a.gpr .x0)]) vslots a u)
    (two_taint [] (pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h₁.1.L.sp, h₂.1.L.sp]) (by taint_decide))
    (fun a u hu => ?_)
    (two_taintE [.x11, .x20] (VR.pins' fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
      (c' := Code.eraseOff (.seq (.block [.addImm .x .x14 .x20 (oY + 8), movi .x12 zH.D])
        Impl.RsaPkcs1Sig.AArch64.copyLoop)) rfl (by taint_decide))
  obtain ⟨h, _⟩ := hu
  have nk : ∀ q ∈ vregs H.D, q.1 ∉ [Reg.x11] := nk_of (by decide)
  unfold ld
  refine WP.of_syms ?_
  refine wp_ldrSp (by decide) (by rw [h.L.sp]; exact h.L.fld (by decide)) fun u' o e =>
    wp_nil fun sy => (h.congr o.sp o.rd o.wr (o.get .x20) (fun q hq => ?_)
      (fun q hq => by rw [o.mem]; exact h.sl q hq) sy (by rw [o.mem]; exact Frame.refl _ _))
  rcases List.mem_append.mp hq with hq | hq
  · rw [o.get q.1 (nk q hq)]; exact h.r q hq
  · rw [List.mem_singleton.mp hq, e, h.L.sp]; exact h.sdig

include hH in
theorem copyDb_vct :
    RelCT isa (Two fun a u => VR T H.D (vregs H.D) vslots a u ∧ PS H.D a u ∧ Z (8 + H.D) a u) (copyDb H)
      (Two fun a u => VR T H.D (vregs H.D) vslots a u ∧ PS H.D a u ∧ Z (8 + H.D + dbA H.D a) a u) :=
  two_post (two_taintE [.x20, .x24, .x25] (VR.pins fun r hr => by
      simp at hr; rcases hr with rfl | rfl | rfl <;> simp [vregs])
    (c' := Code.eraseOff (copyDb zH)) rfl (by taint_decide))
    fun a u ⟨h, p, z⟩ => by
      have := h.ok.db; have := h.ok.lo
      exact WP.mono_syms (copyDb_ok hH h.L (fun _ _ => rfl) (e := oEm + loA a) (db := dbA H.D a) (by omega)
        (by unfold oEm oY; omega) h.x24 h.x25) fun _ ⟨k, f, R⟩ sy =>
          ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L) sy, p.keep h.L rfl f, fun i hi hi' => by
            have hDN := hH.sizes.DN; have hN := hH.N_le
            rw [R _ (by unfold oY oRsa; omega)]; unfold updL
            rw [ite_eq_right (by rw [List.length_map, List.length_range]; omega)]; exact z i (by omega) hi'⟩

/-- The length of `M'`, at most `8 + hLen + dbLen - 1`. -/
def LX (D : Nat) (a u : State) : Prop := ∃ ℓ, u.gpr .x22 = BitVec.ofNat 64 ℓ ∧ ℓ ≤ 7 + D + dbA D a

include hH in
theorem shift_vct :
    RelCT isa (Two fun a u => VR T H.D (vregs H.D) vslots a u ∧ PS H.D a u ∧ Z (8 + H.D + dbA H.D a) a u) (shift H)
      (Two fun a u => VR T H.D (vregs H.D) vslots a u ∧ LX H.D a u) :=
  two_post (two_taintE [.x20, .x25] (VR.pins fun r hr => by
      simp at hr; rcases hr with rfl | rfl <;> simp [vregs])
    (c' := Code.eraseOff (shift zH)) rfl (by taint_decide))
    fun a u ⟨h, ⟨pos, hpos, hP⟩, z⟩ => by
      have := h.ok.db; have hDN := hH.sizes.DN; have hN := hH.N_le
      refine WP.mono_syms (shift_ok H (by omega) h.L (fun _ _ => rfl)
        (W := fun m => u.mem (off (scr a) (oY + 8 + H.D + m))) hpos (by omega) (by unfold oY oRsa; omega)
        (fun m hm => ?_) h.x25 hP) fun _ ⟨k, f, _, x22⟩ sy =>
          ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L) sy, _, x22, by omega⟩
      unfold zf
      by_cases hm' : m < dbA H.D a
      · rw [ite_eq_left hm']
      · rw [ite_eq_right hm']
        have := z (8 + H.D + m) (by omega) (by omega)
        rwa [show oY + (8 + H.D + m) = oY + 8 + H.D + m by omega] at this

include hH in
theorem verifyNb_vct :
    RelCT isa (Two fun a u => VR T H.D (vregs H.D) vslots a u ∧ LX H.D a u) (.block (verifyNb H))
      (Two fun a u => VR T H.D (vregs H.D) (vslots ++ [(sNb, fun a => BitVec.ofNat 64 (nbA H a))]) a u ∧
        LX H.D a u) :=
  two_post (two_taintE [.x25] (VR.pins fun r hr => by simp at hr; subst hr; simp [vregs])
    (c' := Code.eraseOff (.block (verifyNb zH))) rfl (by taint_decide))
    fun a u ⟨h, ℓ, x22, hℓ⟩ => by
      have := h.ok.db
      refine WP.mono_syms (verifyNb_ok hH h.L (db := dbA H.D a) (by omega) h.x25) fun u' ⟨k, m⟩ sy =>
        ⟨h.congr k.sp k.rd k.wr (k.get .x20) (fun q hq => ?_) (fun q hq => ?_) sy
          (by rw [m]; exact (frame_slot _ _ sNb _).mono (by simp [mgfWr])), ℓ, by rw [k.get .x22]; exact x22, hℓ⟩
      · rw [k.get q.1 (nk_of (by decide) q hq)]; exact h.r q hq
      · rcases List.mem_append.mp hq with hq | hq
        · rw [m, slot_keep (frame_slot _ _ sNb _) (vslots_sNb q hq)]; exact h.sl q hq
        · rw [List.mem_singleton.mp hq, m, Mem.readW_writeW_self64]

include hH in
theorem cmpH_vct :
    RelCT isa (Two (VR T H.D (vregs H.D) vslots)) (cmpH H) (Two fun a t => t.sp = fb a) :=
  two_post (two_taintE [.x21, .x24, .x25] (VR.pins' fun r hr => by
      simp at hr; rcases hr with rfl | rfl | rfl <;> simp [vregs])
    (c' := Code.eraseOff (cmpH zH)) rfl (by taint_decide))
    fun a u h => by
      have := h.ok.db; have := h.ok.lo; have hDN := hH.sizes.DN; have hN := hH.N_le
      exact WP.mono (cmpH_ok hH h.L (fun _ _ => rfl) (e := oEm + loA a) (db := dbA H.D a) (acc := u.gpr .x26)
        (by unfold oEm oY; omega) h.x21 h.x24 h.x25 rfl) fun _ ⟨O, _⟩ => by rw [O.sp, h.L.sp]

end

theorem mgfXor_vct {T : Tabs} {Gs : Spec.Mgf1.Hash} (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK T.G)
    (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = T.G.D) (hGv : Proof.Mgf1.Valid Gs) :
    RelCT isa (Two (VR T T.H.D (vregs T.H.D) vslots)) (mgfXor T.H T.g) (Two (VR T T.H.D (vregs T.H.D) vslots)) := by
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have hd : ∀ a : State, VOk T.H.D a → DbAt T.H.D (oEm + loA a) (dbA T.H.D a) := fun a ok => by
    have := ok.db
    exact ⟨by omega, by omega, by omega⟩
  refine two_post (two_map (fun a => (⟨fb a, scr a, oEm + loA a, dbA T.H.D a, stackArg a 1, a.syms T.G.initN,
      a.syms T.G.updN, a.syms T.G.finN⟩ : MA))
    (fun a u h => ⟨h.L, hd a h.ok, h.x24, h.x25, h.env, h.names _ (by simp [Tabs.names]),
      h.names _ (by simp [Tabs.names]), h.names _ (by simp [Tabs.names])⟩) (mgfXor_ct hGm (H := T.H)))
    fun a u h => WP.mono (mgfXor_ok hGm hGh hGl hGv h.L (fun _ _ => rfl) (hd a h.ok) h.x24 h.x25 h.env)
      fun u' ⟨sp, rd, wr, cs, _, fr, sy, _⟩ => h.congr sp rd wr (cs .x20 (by decide) (by decide)) (fun q hq => ?_)
        (fun q hq => ?_) sy (fr.mono (by simp))
  · rw [cs q.1 ((by decide : ∀ r ∈ [Reg.x19, .x21, .x23, .x24, .x25], r ∈ preserved) _ (vregs_fst hq))
      ((by decide : ∀ r ∈ [Reg.x19, .x21, .x23, .x24, .x25], r ≠ .x30) _ (vregs_fst hq))]
    exact h.r q hq
  · rw [slot_keep fr (h.L.slotW (vslots_fb q hq) ?_ ?_)]
    · exact h.sl q hq
    · simp only [vslots, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [vslots, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide

theorem ctHash_vct {T : Tabs} (hH : HashOK T.H) (hc : PssChecks T.H.P T.H.D) (hdo : DigOK T.H.P) :
    RelCT isa (Two fun a u => VR T T.H.D (vregs T.H.D) (vslots ++ [(sNb, fun a => BitVec.ofNat 64 (nbA T.H a))]) a u ∧
        LX T.H.D a u) (ctHash T.f T.H) (Two (VR T T.H.D (vregs T.H.D) vslots)) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have hL := hH.L
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hlg : 2 ^ lgB T.H = T.H.P.B ∧ lgB T.H < 64 := by
    unfold lgB
    rcases hH.sizes.B with h | h <;> rw [h]
    · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
    · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide
  have hb : ∀ a : State, dbA T.H.D a ≤ 1024 → ∀ ℓ, ℓ ≤ 7 + T.H.D + dbA T.H.D a →
      ℓ + 1 + T.H.P.L ≤ nbA T.H a * T.H.P.B ∧ nbA T.H a * T.H.P.B ≤ 2048 := fun a hs ℓ hℓ => by
    have hnb1 := Nat.lt_div_mul_add (a := dbA T.H.D a + 7 + T.H.D + T.H.P.L) (b := T.H.P.B) hB0
    have hnb2 := Nat.div_mul_le_self (dbA T.H.D a + 7 + T.H.D + T.H.P.L) T.H.P.B
    have hnbB : ((dbA T.H.D a + 7 + T.H.D + T.H.P.L) / T.H.P.B + 1) * T.H.P.B =
        (dbA T.H.D a + 7 + T.H.D + T.H.P.L) / T.H.P.B * T.H.P.B + T.H.P.B := Nat.succ_mul _ _
    show _ ≤ ((dbA T.H.D a + 7 + T.H.D + T.H.P.L) / T.H.P.B + 1) * T.H.P.B ∧
      ((dbA T.H.D a + 7 + T.H.D + T.H.P.L) / T.H.P.B + 1) * T.H.P.B ≤ 2048
    rw [hnbB]; omega
  have nb : ∀ {a u : State}, VR T T.H.D (vregs T.H.D) (vslots ++ [(sNb, fun a => BitVec.ofNat 64 (nbA T.H a))]) a u →
      u.mem.readW (off (fb a) sNb) 64 = BitVec.ofNat 64 (nbA T.H a) := fun h =>
    h.sl (sNb, fun a => BitVec.ofNat 64 (nbA T.H a)) (by simp)
  refine two_post (two_map (fun a => (⟨fb a, scr a, nbA T.H a, none, a.syms T.H.initN, a.syms T.H.compN, a.syms T.dn⟩ : HA)) (fun a u ⟨h, ℓ, x22, hℓ⟩ => {
      L := h.L
      x19 := h.x19
      x21 := h.x21
      nb := nb h
      len := ⟨ℓ, x22, (hb a h.ok.db.2.2.1 ℓ hℓ).1⟩
      hnb := (hb a h.ok.db.2.2.1 ℓ hℓ).2
      fx := fun _ e => nomatch e
      ht := h.ht
      ai := h.names _ (by simp [Tabs.names])
      ac := h.names _ (by simp [Tabs.names])
      ad := h.names _ (by simp [Tabs.names]) }) (ctHash_ct hH hc hdo)) fun a u ⟨h, ℓ, x22, hℓ⟩ => ?_
  have hs := hb a h.ok.db.2.2.1 ℓ hℓ
  refine WP.mono_syms (ctHashWith_out hH (pad80 T.H) h.L (fun _ _ => rfl) h.x19 h.x21 x22 (nb h) hs.1 hs.2
    (fun L' R' h22' hNb' => ?_) h.ht hdo) fun u' O sy => ?_
  · exact WP.mono (pad80_ok T.H L' R' hlg.1 hlg.2 (by omega) hs.2 (by have := hs.1; omega) h22' hNb')
      fun _ ⟨k, f, r⟩ => ⟨k.mono, f, r⟩
  refine h.congr O.sp O.rd O.wr (O.cs .x20 (by decide)) (fun q hq => ?_) (fun q hq => ?_) sy
    (O.fr.mono (by simp [mgfWr]))
  · rw [O.cs q.1 ((by decide : ∀ r ∈ [Reg.x19, .x21, .x23, .x24, .x25], r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24,
      .x25, .x26, .x28]) _ (vregs_fst hq))]
    exact h.r q hq
  · rw [slot_keep O.fr fun r hr => ?_]
    · exact h.sl q (List.mem_append_left _ hq)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.L.dFS.sub_left (Offset.sub_base _ (vslots_fb q hq))
    · exact slot_not_below _ (vslots_fb q hq)

end VG.Proof.RsaPss.AArch64.Chk
