module

import VerifiedGarbage.Proof.RsaPss.AArch64.EncCT
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkCorrect
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.RsaPss.AArch64.EncCT
meta import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
meta import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
meta import VerifiedGarbage.Proof.RsaPss.AArch64.ChkCorrect
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPss.AArch64.Restore
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Wp
meta import VerifiedGarbage.Proof.RsaPss.AArch64.Restore
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
meta import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
public import VerifiedGarbage.Proof.RsaPss.AArch64.Checks
import VerifiedGarbage.Proof.RsaPss.AArch64.MgfCT
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyShift
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEncOk
meta import VerifiedGarbage.Proof.RsaPss.AArch64.Checks
meta import VerifiedGarbage.Proof.RsaPss.AArch64.MgfCT
meta import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyShift
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignEncOk
public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkFrame
public import VerifiedGarbage.Proof.RsaPss.AArch64.Mgf
meta import VerifiedGarbage.Proof.RsaPss.AArch64.ChkFrame
meta import VerifiedGarbage.Proof.RsaPss.AArch64.Mgf

/-! ### `RsaPss.AArch64.ChkFixedSaltCT`, which this module and modules that import it used -/

section

/-! ### `RsaPss.AArch64.ChkCTMain`, which this module and modules that import it used -/

section

/-! ### `RsaPss.AArch64.ChkCTBase`, which this module and modules that import it used -/

section

/-!
# EMSA-PSS's check of an encoding on AArch64: constant time, the public data

The pointers, the lengths, the salt length, `any_salt_len` and the tables'
addresses are public (`PubC`), and so are the addresses of the tables'
functions; the digest and the encoding are secret. Two runs with the same
public data as an anchor `a` (`E`) are related at each point of the code by
what correctness says there.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Chk

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64.Sgn (fb)

/-- The working space. -/
abbrev scr (s : State) : Addr := s.gpr .x6

/-- The public data of an entry state `s` is the anchor `a`'s: the
pointers, the lengths, the salt length's arguments and the tables'
addresses. -/
structure PubC (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x6, .x7], s.gpr r = a.gpr r
  a5 : (s.gpr .x5).setWidth 32 = (a.gpr .x5).setWidth 32
  sa : ∀ j < 2, stackArg s j = stackArg a j

theorem PubC.refl (s : State) : PubC s s := ⟨rfl, fun _ _ => rfl, rfl, fun _ _ => rfl⟩

/-- An entry state with the anchor's public data, whose tables name `T`'s
functions at the anchor's addresses. -/
def E (T : Tabs) (a s : State) : Prop :=
  PreC T.H.D T.tsH T.tsG s ∧ PubC a s ∧ T.At s ∧ ∀ n ∈ T.names, s.syms n = a.syms n

namespace E
variable {T : Tabs} {a s : State} (h : E T a s)
include h

theorem gpr {r : Reg} (hr : r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x6, .x7]) : s.gpr r = a.gpr r := h.2.1.g r hr

theorem fb : fb s = fb a := by show s.sp - _ = a.sp - _; rw [h.2.1.sp]

theorem scr : scr s = scr a := h.gpr (r := .x6) (by decide)

theorem any : anyC s = anyC a := by rw [anyC, anyC, h.2.1.a5]

theorem arg {j : Nat} (hj : j < 2) : stackArg s j = stackArg a j := h.2.1.sa j hj

theorem sym {n : String} (hn : n ∈ T.names) : s.syms n = a.syms n := h.2.2.2 n hn

theorem z : zC s = zC a := by rw [zC, zC, h.gpr (r := .x2) (by decide), h.gpr (r := .x3) (by decide)]

end E

end VG.Proof.RsaPss.AArch64.Chk

end

end

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
  exact ⟨dgR T.H.D s, by simp, Offset.contains_base _ (by omega_using [hj]) (by have := hp.wd; omega_using [hj, this])⟩

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

/-- Where MGF1 works, and the table of `MdHash`. -/
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
  omega_arith

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
      exact WP.mono_syms (acc0_ok h.L (fun _ _ => rfl) (k := kV a) (lo := loA a) (by omega_arith) ok.k2 ok.lo h.x23 h.x24
        h.slo h.sc) fun _ ⟨O, _⟩ sy => h.only O (nk_of (by decide)) (by decide) sy


theorem clearTop_vct {T : Tabs} {D : Nat} :
    RelCT isa (Two (VR T D (vregs D) vslots)) (.block clearTop) (Two (VR T D (vregs D) vslots)) :=
  two_post (two_taint [.x24] (VR.pins' fun r hr => by simp at hr; subst hr; simp [vregs]) (by taint_decide))
    fun a u h => by
      have := h.ok.lo
      exact WP.mono_syms (clearTop_ok h.L (fun _ _ => rfl) (e := oEm + loA a) (c := cbA a) h.x24
        (by unfold oEm oRsa; omega_using [this]) h.sc) fun _ ⟨k, f, _⟩ sy =>
          h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L) sy

theorem posScan_vct {T : Tabs} {D : Nat} :
    RelCT isa (Two (VR T D (vregs D) vslots)) posScan
      (Two fun a u => VR T D (vregs D) vslots a u ∧ ∃ pos, pos < dbA D a ∧ u.gpr .x14 = BitVec.ofNat 64 pos) :=
  two_post (two_taint [.x24, .x25] (VR.pins' fun r hr => by
      simp at hr; rcases hr with rfl | rfl <;> simp [vregs]) (by taint_decide))
    fun a u h => by
      have := h.ok.db; have := h.ok.lo
      exact WP.mono_syms (posScan_ok h.L (fun _ _ => rfl) (e := oEm + loA a) (db := dbA D a)
        (by unfold oEm oRsa; omega_arith) (by omega_arith) h.x24 h.x25) fun _ ⟨O, _, x14, _⟩ sy =>
          ⟨h.only O (nk_of (by decide)) (by decide) sy, _, nz_lt (by omega_arith), x14⟩

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
        rw [R _ (by unfold oY oRsa; omega_using [hi])]; unfold clr; exact ite_eq_left ⟨by omega_using [], by omega_using [hi]⟩⟩

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
          rw [R _ (by unfold oY oRsa; omega_using [hi'])]; unfold updL
          rw [ite_eq_right (by rw [bytesAt_length]; omega_using [hi])]; exact z i (by omega_using []) hi'⟩
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
      exact WP.mono_syms (copyDb_ok hH h.L (fun _ _ => rfl) (e := oEm + loA a) (db := dbA H.D a) (by omega_arith)
        (by unfold oEm oY; omega_arith) h.x24 h.x25) fun _ ⟨k, f, R⟩ sy =>
          ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L) sy, p.keep h.L rfl f, fun i hi hi' => by
            have hDN := hH.sizes.DN; have hN := hH.N_le
            rw [R _ (by unfold oY oRsa; omega_using [hi'])]; unfold updL
            rw [ite_eq_right (by rw [List.length_map, List.length_range]; omega_using [hi])]; exact z i (by omega_using [hi]) hi'⟩

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
      refine WP.mono_syms (shift_ok H (by omega_using [hDN, hN]) h.L (fun _ _ => rfl)
        (W := fun m => u.mem (off (scr a) (oY + 8 + H.D + m))) hpos (by omega_using [this]) (by unfold oY oRsa; omega_using [this])
        (fun m hm => ?_) h.x25 hP) fun _ ⟨k, f, _, x22⟩ sy =>
          ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L) sy, _, x22, by omega_using [hpos]⟩
      unfold zf
      by_cases hm' : m < dbA H.D a
      · rw [ite_eq_left hm']
      · rw [ite_eq_right hm']
        have := z (8 + H.D + m) (by omega_using [hm']) (by omega_using [this, hm])
        rwa [show oY + (8 + H.D + m) = oY + 8 + H.D + m by omega_using []] at this

include hH in
theorem verifyNb_vct :
    RelCT isa (Two fun a u => VR T H.D (vregs H.D) vslots a u ∧ LX H.D a u) (.block (verifyNb H))
      (Two fun a u => VR T H.D (vregs H.D) (vslots ++ [(sNb, fun a => BitVec.ofNat 64 (nbA H a))]) a u ∧
        LX H.D a u) :=
  two_post (two_taintE [.x25] (VR.pins fun r hr => by simp at hr; subst hr; simp [vregs])
    (c' := Code.eraseOff (.block (verifyNb zH))) rfl (by taint_decide))
    fun a u ⟨h, ℓ, x22, hℓ⟩ => by
      have := h.ok.db
      refine WP.mono_syms (verifyNb_ok hH h.L (db := dbA H.D a) (by omega_using [this]) h.x25) fun u' ⟨k, m⟩ sy =>
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
        (by unfold oEm oY; omega_arith) h.x21 h.x24 h.x25 rfl) fun _ ⟨O, _⟩ => by rw [O.sp, h.L.sp]

end

theorem mgfXor_vct {T : Tabs} {Gs : Spec.Mgf1.Hash} (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK T.G)
    (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = T.G.D) (hGv : Proof.Mgf1.Valid Gs) :
    RelCT isa (Two (VR T T.H.D (vregs T.H.D) vslots)) (mgfXor T.H T.g) (Two (VR T T.H.D (vregs T.H.D) vslots)) := by
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have hd : ∀ a : State, VOk T.H.D a → DbAt T.H.D (oEm + loA a) (dbA T.H.D a) := fun a ok => by
    have := ok.db
    exact ⟨by omega_using [], by omega_using [this], by omega_using [c1, c2, this]⟩
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
    rw [hnbB]; omega_arith
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
  · exact WP.mono (pad80_ok T.H L' R' hlg.1 hlg.2 (by omega_using [hs]) hs.2 (by have := hs.1; omega_using [hs]) h22' hNb')
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

end

end

/-! Fixed-length verification copies and hashes only public lengths. -/

@[expose] public section
namespace VG.Proof.RsaPss.AArch64.Chk.Fixed
open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_add wp_sub wp_addImm eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_map two_ite wp_ldrSp)
open VG.Proof.RsaPss.AArch64.Sgn (fb)

abbrev salt (a : State) : Nat := (a.gpr .x4).toNat
abbrev blocks (H : Hash) (a : State) : Nat := (8 + H.D + salt a + H.P.L) / H.P.B + 1
abbrev FV (T : Tabs) (D : Nat) (a u : State) : Prop :=
  VR T D (vregs D) vslots a u ∧ salt a < dbA D a

theorem clear_ct {T : Tabs} {D : Nat} : RelCT isa (Two (FV T D)) clearY (Two (FV T D)) :=
  two_post (two_taint [.x20] (VR.pins fun r hr => by simp at hr; exact .inl hr) (by taint_decide))
    fun a u ⟨h, hs⟩ => WP.mono_syms (clearY_ok h.L (fun _ _ => rfl)) fun _ ⟨k, f, _⟩ sy =>
      ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L) sy, hs⟩

variable {T : Tabs} (hH : HashOK T.H)
include hH in
theorem digest_ct : RelCT isa (Two (FV T T.H.D)) (copyDigest T.H) (Two (FV T T.H.D)) := by
  refine two_post (Φ := FV T T.H.D) ?_ fun a u ⟨h, hs⟩ => WP.mono_syms
    (copyDigest_ok hH h.L (fun _ _ => rfl) h.sdig h.dig.1 h.dig.2) fun _ ⟨k, f, _⟩ sy =>
      ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L) sy, hs⟩
  unfold copyDigest
  refine RelCT.seq_block_append (M := isa) (l₁ := [ld .x11 sDig]) ?_
  refine two_step (Ψ := fun a u => VR T T.H.D (vregs T.H.D ++ [(.x11, fun a => a.gpr .x0)]) vslots a u)
    (two_taint [] (pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h₁.1.L.sp, h₂.1.L.sp]) (by taint_decide))
    (fun a u hu => ?_)
    (two_taintE [.x11, .x20] (VR.pins' fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
      (c' := Code.eraseOff (.seq (.block [.addImm .x .x14 .x20 (oY + 8), movi .x12 zH.D])
        Impl.RsaPkcs1Sig.AArch64.copyLoop)) rfl (by taint_decide))
  obtain ⟨h, _⟩ := hu
  unfold ld
  refine WP.of_syms ?_
  refine wp_ldrSp (by decide) (ld_slot h.L (by decide)) fun u' o e =>
    wp_nil fun sy => (h.congr o.sp o.rd o.wr (o.get .x20) (fun q hq => ?_)
      (fun q hq => by rw [o.mem]; exact h.sl q hq) sy (by rw [o.mem]; exact Frame.refl _ _))
  rcases List.mem_append.mp hq with hq | hq
  · rw [o.get q.1 (nk_of (by decide) q hq)]; exact h.r q hq
  · rw [List.mem_singleton.mp hq, e, h.L.sp]; exact h.sdig

include hH in
theorem copy_ct : RelCT isa (Two (FV T T.H.D)) (Impl.RsaPss.AArch64.FixedSalt.copySalt T.H)
    (Two (FV T T.H.D)) := by
  refine two_post (Φ := FV T T.H.D) ?_ fun a u ⟨h, hs⟩ => ?_
  rotate_left
  · have := h.ok.db
    refine WP.mono_syms (VG.Proof.RsaPss.AArch64.FixedSalt.copySalt_ok hH h.L (fun _ _ => rfl)
      (e := oEm + loA a) (db := dbA T.H.D a) (sl := salt a) (by omega_arith) (by unfold oEm oY; omega_arith)
      (by omega_arith) (by omega_arith) h.x24 h.x25
      (by rw [h.ssl, BitVec.ofNat_toNat, BitVec.setWidth_eq])) fun _ ⟨k, f, _⟩ sy =>
        ⟨h.keep k (nk_of (by decide)) (by decide) f (vslots_S h.L) sy, hs⟩
  unfold Impl.RsaPss.AArch64.FixedSalt.copySalt
  refine two_step (Ψ := fun a t => t.sp = fb a ∧
      t.gpr .x11 = off (scr a) (oEm + loA a) + BitVec.ofNat 64 (dbA T.H.D a) - a.gpr .x4 ∧
      t.gpr .x12 = a.gpr .x4 ∧ t.gpr .x14 = off (scr a) (oY + 8 + T.H.D))
    (two_taintE [] (pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h₁.1.L.sp, h₂.1.L.sp])
      (c' := Code.eraseOff (.block [.add .x .x11 .x24 .x25, ld .x12 sSaltLen,
        .sub .x .x11 .x11 .x12, .addImm .x .x14 .x20 (oY + 8 + zH.D)])) rfl (by taint_decide))
    (fun a u ⟨h, _⟩ => ?_) ?_
  · refine wp_add fun u₁ o₁ e₁ => wp_ldrSp (by decide)
      (by rw [o₁.sp, o₁.rd, o₁.wr]; exact ld_slot h.L (by decide)) fun u₂ o₂ e₂ =>
      wp_sub fun u₃ o₃ e₃ => wp_addImm (by have := hH.sizes.DN; have := hH.N_le; unfold oY; omega_arith)
        fun u₄ o₄ e₄ => wp_nil ?_
    refine ⟨by rw [o₄.sp, o₃.sp, o₂.sp, o₁.sp, h.L.sp], ?_, ?_, ?_⟩
    · rw [o₄.get .x11, e₃, o₂.get .x11, e₁, h.x24, h.x25, e₂, o₁.sp, h.L.sp, o₁.mem, h.ssl]
    · rw [o₄.get .x12, o₃.get .x12, e₂, o₁.sp, h.L.sp, o₁.mem, h.ssl]
    · rw [e₄, o₃.get .x20, o₂.get .x20, o₁.get .x20, h.L.x20]
  · exact two_taint [.x11, .x12, .x14] (fun a s₁ s₂ h₁ h₂ =>
      ⟨by rw [h₁.1, h₂.1], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2.1, h₂.2.2.1]
        · rw [h₁.2.2.2, h₂.2.2.2]⟩) (by taint_decide)

def regs (D : Nat) : List (Reg × (State → BitVec 64)) :=
  vregs D ++ [(.x22, fun a => BitVec.ofNat 64 (8 + D + salt a))]
def slots (H : Hash) : List (Nat × (State → BitVec 64)) :=
  vslots ++ [(sNb, fun a => BitVec.ofNat 64 (blocks H a))]

include hH in
theorem len_ct : RelCT isa (Two (FV T T.H.D)) (.block (signLen T.H))
    (Two fun a u => VR T T.H.D (regs T.H.D) (slots T.H) a u ∧ salt a < dbA T.H.D a) := by
  refine two_post (two_taintE [] (pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h₁.1.L.sp, h₂.1.L.sp])
    (c' := Code.eraseOff (.block (signLen zH))) rfl (by taint_decide)) fun a u ⟨h, hs⟩ => ?_
  have := h.ok.db
  refine WP.mono_syms (signLen_ok hH h.L (sl := salt a)
    (by rw [h.ssl, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_arith)) fun u' ⟨k, x22, m⟩ sy =>
      ⟨h.congr k.sp k.rd k.wr (k.get .x20) (fun q hq => ?_) (fun q hq => ?_) sy
        (by rw [m]; exact (frame_slot _ _ sNb _).mono (by simp [mgfWr])), hs⟩
  · rcases List.mem_append.mp hq with hq | hq
    · rw [k.get q.1 (nk_of (by decide) q hq)]; exact h.r q hq
    · rw [List.mem_singleton.mp hq]; exact x22
  · rcases List.mem_append.mp hq with hq | hq
    · rw [m, slot_keep (frame_slot _ _ sNb _) (vslots_sNb q hq)]; exact h.sl q hq
    · rw [List.mem_singleton.mp hq, m, Mem.readW_writeW_self64]

include hH in
theorem hash_ct (hc : PssChecks T.H.P T.H.D) (hdo : DigOK T.H.P) :
    RelCT isa (Two fun a u => VR T T.H.D (regs T.H.D) (slots T.H) a u ∧ salt a < dbA T.H.D a) (ctHash T.f T.H) (Two (VR T T.H.D (vregs T.H.D) vslots)) := by
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
  have hb : ∀ a : State, salt a ≤ 1024 → 8 + T.H.D + salt a + 1 + T.H.P.L ≤ blocks T.H a * T.H.P.B ∧ blocks T.H a * T.H.P.B ≤ 2048 :=
    fun a hs => by
      have hnb1 := Nat.lt_div_mul_add (a := 8 + T.H.D + salt a + T.H.P.L) (b := T.H.P.B) hB0
      have hnb2 := Nat.div_mul_le_self (8 + T.H.D + salt a + T.H.P.L) T.H.P.B
      have hnbB : ((8 + T.H.D + salt a + T.H.P.L) / T.H.P.B + 1) * T.H.P.B =
          (8 + T.H.D + salt a + T.H.P.L) / T.H.P.B * T.H.P.B + T.H.P.B := Nat.succ_mul _ _
      show _ ≤ ((8 + T.H.D + salt a + T.H.P.L) / T.H.P.B + 1) * T.H.P.B ∧ ((8 + T.H.D + salt a + T.H.P.L) / T.H.P.B + 1) * T.H.P.B ≤ 2048
      rw [hnbB]; omega_arith
  have x19 : ∀ {a u : State}, VR T T.H.D (regs T.H.D) (slots T.H) a u → u.gpr .x19 = off (scr a) oSt := fun h =>
    h.r (.x19, fun a => off (scr a) oSt) (by simp [regs, vregs])
  have x21 : ∀ {a u : State}, VR T T.H.D (regs T.H.D) (slots T.H) a u → u.gpr .x21 = off (scr a) oDig := fun h =>
    h.r (.x21, fun a => off (scr a) oDig) (by simp [regs, vregs])
  have x22 : ∀ {a u : State}, VR T T.H.D (regs T.H.D) (slots T.H) a u → u.gpr .x22 = BitVec.ofNat 64 (8 + T.H.D + salt a) :=
    fun h => h.r (.x22, fun a => BitVec.ofNat 64 (8 + T.H.D + salt a)) (by simp [regs])
  have nb : ∀ {a u : State}, VR T T.H.D (regs T.H.D) (slots T.H) a u →
      u.mem.readW (off (fb a) sNb) 64 = BitVec.ofNat 64 (blocks T.H a) := fun h =>
    h.sl (sNb, fun a => BitVec.ofNat 64 (blocks T.H a)) (by simp [slots])
  refine two_post (two_map (fun a => (⟨fb a, scr a, blocks T.H a, none, a.syms T.H.initN, a.syms T.H.compN, a.syms T.dn⟩ : HA)) (fun a u ⟨h, hsalt⟩ => {
      L := h.L
      x19 := x19 h
      x21 := x21 h
      nb := nb h
      len := ⟨8 + T.H.D + salt a, x22 h, (hb a (by have := h.ok.db; omega_arith)).1⟩
      hnb := (hb a (by have := h.ok.db; omega_arith)).2
      fx := fun _ e => nomatch e
      ht := h.ht
      ai := h.names _ (by simp [Tabs.names])
      ac := h.names _ (by simp [Tabs.names])
      ad := h.names _ (by simp [Tabs.names]) }) (ctHash_ct hH hc hdo)) fun a u ⟨h, hsalt⟩ => ?_
  have hs : salt a ≤ 1024 := by have := h.ok.db; omega_arith
  refine WP.mono_syms (ctHashWith_out hH (pad80 T.H) h.L (fun _ _ => rfl) (x19 h) (x21 h) (x22 h) (nb h)
    (hb a hs).1 (hb a hs).2 (fun L' R' h22' hNb' => ?_) h.ht hdo) fun u' O sy => ?_
  · exact WP.mono (pad80_ok T.H L' R' hlg.1 hlg.2 (by omega_arith) (hb a hs).2 (by have := (hb a hs).1; omega_arith) h22' hNb')
      fun _ ⟨k, f, r⟩ => ⟨k.mono, f, r⟩
  refine h.congr O.sp O.rd O.wr (O.cs .x20 (by decide)) (fun q hq => ?_) (fun q hq => ?_) sy
    (O.fr.mono (by simp [mgfWr]))
  · rw [O.cs q.1 ((by decide : ∀ r ∈ [Reg.x19, .x21, .x23, .x24, .x25], r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x28]) _ (vregs_fst hq))]; exact h.r q (List.mem_append_left _ hq)
  · rw [slot_keep O.fr fun r hr => ?_]
    · exact h.sl q (List.mem_append_left _ hq)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.L.dFS.sub_left (Offset.sub_base _ (vslots_fb q hq))
    · exact slot_not_below _ (vslots_fb q hq)

include hH in
theorem finish_ct (hc : PssChecks T.H.P T.H.D) (hdo : DigOK T.H.P) :
    RelCT isa (Two (FV T T.H.D)) (Impl.RsaPss.AArch64.FixedSalt.finish T.f T.H) (Two fun a t => t.sp = fb a) := by
  unfold Impl.RsaPss.AArch64.FixedSalt.finish seqs seqs seqs seqs seqs
  exact RelCT.seq clear_ct (RelCT.seq (digest_ct hH) (RelCT.seq (copy_ct hH)
    (RelCT.seq (len_ct hH) (RelCT.seq (hash_ct hH hc hdo) (cmpH_vct hH)))))

end VG.Proof.RsaPss.AArch64.Chk.Fixed

namespace VG.Proof.RsaPss.AArch64.Chk
open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.MlKem.AArch64 (wp_nil eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two two_taint two_post two_map two_ite wp_ldrSp)
open VG.Proof.RsaPss.AArch64.Sgn (fb)

variable {T : Tabs} (hH : HashOK T.H)
include hH in
theorem select_ct (hc : PssChecks T.H.P T.H.D) (hdo : DigOK T.H.P) :
    RelCT isa (Two fun a u => VR T T.H.D (vregs T.H.D) vslots a u ∧ PS T.H.D a u)
      (Impl.RsaPss.AArch64.FixedSalt.select T.f T.H) (Two fun a t => t.sp = fb a) := by
  unfold Impl.RsaPss.AArch64.FixedSalt.select
  refine two_step (Ψ := fun a u => (VR T T.H.D (vregs T.H.D) vslots a u ∧ PS T.H.D a u) ∧ u.gpr .x9 = anyC a)
    (two_taint [] (pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h₁.1.L.sp, h₂.1.L.sp]) (by taint_decide))
    (fun a u ⟨h, p⟩ => ?_) ?_
  · unfold ld
    refine WP.of_syms ?_
    refine wp_ldrSp (by decide) (ld_slot h.L (by decide)) fun t o e => wp_nil fun sy => ?_
    exact ⟨⟨h.only o (nk_of (by decide)) (by decide) sy, by obtain ⟨pos, hp, ep⟩ := p; exact ⟨pos, hp, by rw [o.mem]; exact ep⟩⟩, by rw [e, h.L.sp, h.sany]⟩
  · refine two_ite (fun a s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2]) ?_ ?_
    · refine two_map id (fun a u h => ?_) (Fixed.finish_ct hH hc hdo)
      have ha : anyC a = 0 := by
        have hb := h.2
        rw [eval_zero, h.1.2] at hb
        exact beq_iff_eq.mp (Option.some.inj hb)
      exact ⟨h.1.1.1, h.1.1.1.ok.salt ha⟩
    · refine two_map (Φ' := fun a u => VR T T.H.D (vregs T.H.D) vslots a u ∧ PS T.H.D a u) id (fun _ _ h => h.1.1) ?_
      unfold seqs seqs seqs seqs seqs seqs
      exact RelCT.seq clearY_vct (RelCT.seq (copyDigest_vct hH) (RelCT.seq (copyDb_vct hH)
        (RelCT.seq (shift_vct hH) (RelCT.seq (verifyNb_vct hH) (RelCT.seq (ctHash_vct hH hc hdo) (cmpH_vct hH))))))

include hH in
/-- Both verification paths branch and access memory only through public values. -/
theorem check_ct {Gs : Spec.Mgf1.Hash} (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK T.G)
    (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = T.G.D) (hGv : Proof.Mgf1.Valid Gs)
    (hc : PssChecks T.H.P T.H.D) (hdo : DigOK T.H.P) :
    RelCT isa (Two (VR T T.H.D (vregs T.H.D) vslots))
      (seqs [.block acc0, mgfXor T.H T.g, .block clearTop, posScan, posCheck,
        Impl.RsaPss.AArch64.FixedSalt.select T.f T.H])
      (Two fun a t => t.sp = fb a) := by
  unfold seqs seqs seqs seqs seqs
  exact RelCT.seq acc0_vct (RelCT.seq (mgfXor_vct hGm hGh hGl hGv) (RelCT.seq clearTop_vct
    (RelCT.seq posScan_vct (RelCT.seq posCheck_vct (select_ct hH hc hdo)))))

end VG.Proof.RsaPss.AArch64.Chk

end

end

/-! ### `RsaPss.AArch64.ChkTop`, which this module and modules that import it used -/

section

/-!
# EMSA-PSS's check of an encoding on AArch64: the whole function

`code_ok`: from the precondition, `checkEncoding` keeps the calling
convention and returns 1 exactly when `Spec.RsaPss.verifyEncoding` holds
(`Post`): the prologue (`prologue_ok`), the copy (`copyIn_okC`), the checks
of the lengths (`body_ok`), verification's checks (`chkMain_ok`), and the
restores (`restore_frame_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Chk

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (wp_nil wp_movz eval_nonzero)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (fitH_ok saltFitsR_ok expLen_ok restore_frame_ok slot_keep)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.RsaPss.AArch64.Sgn (fb stk)

/-- The result, and the calling convention. -/
def Post (D : Nat) (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ (s'.gpr .x0).setWidth 32 = if chkOut D Hs Gs s then 1 else 0

theorem anyC_eq (s : State) : anyC s = 0 ↔ (s.gpr .x5).setWidth 32 = 0 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [anyC, BitVec.toNat_setWidth] at this ⊢
    rw [show (0 : BitVec 64).toNat = 0 from rfl] at this
    rw [show (0 : BitVec 32).toNat = 0 from rfl]
    omega_using [this]
  · intro h; unfold anyC; rw [h]; rfl

theorem expected_eq (s : State) : Spec.RsaPss.expectedSaltLen (s.gpr .x4) ((s.gpr .x5).setWidth 32) =
    if anyC s = 0 then some (s.gpr .x4).toNat else none := by
  unfold Spec.RsaPss.expectedSaltLen
  by_cases h : anyC s = 0
  · rw [ite_eq_left h, ite_eq_left ((anyC_eq s).mp h)]
  · rw [ite_eq_right h, ite_eq_right fun h' => h ((anyC_eq s).mpr h')]

/-- A refusal: 0. -/
theorem ret0_ok {D : Nat} {Hs Gs : Spec.Mgf1.Hash} {s u : State} (hu : MidC s u) (hn : chkOut D Hs Gs s = false) :
    WP isa ret0 u fun t => MidC s t ∧ (t.gpr .x0).setWidth 32 = if chkOut D Hs Gs s then 1 else 0 := by
  unfold ret0
  refine wp_movz fun t o e => wp_nil ⟨⟨o.sp.trans hu.sp, o.rd.trans hu.rd, o.wr.trans hu.wr,
    fun r hr => (o.vcs r hr).trans (hu.v r hr), o.mem ▸ hu.fr⟩, ?_⟩
  rw [hn, e]
  rfl

/-- `AtCT` at a later state for which `AtC` holds, after writes only in our
working space. -/
theorem AtCT.of {D : Nat} {tsH tsG : List FnTable} {s u u' : State} (hp : PreC D tsH tsG s) (h : AtCT s u)
    (h' : AtC s u') (hf : Frame [⟨s.gpr .x6, oRsa⟩] u.mem u'.mem) (hsy : u'.syms = u.syms) : AtCT s u' := by
  have L := lay_of hp h.e.sp h.e.x20 h.e.wr
  exact ⟨h', by rw [slot_keep (d := sMgfT) hf (L.slotSd (by decide))]; exact h.wm,
    by rw [slot_keep (d := sIniH) hf (L.slotSd (by decide))]; exact h.wi,
    by rw [slot_keep (d := sCmpH) hf (L.slotSd (by decide))]; exact h.wc,
    by rw [slot_keep (d := sDigH) hf (L.slotSd (by decide))]; exact h.wd, hsy.trans h.sy⟩

section
variable {H : Hash} (hH : HashOK H) {Gm : Impl.Pbkdf2.Md.AArch64.Stream}
  (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK Gm) {Hs Gs : Spec.Mgf1.Hash}
  (hHs : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = Gm.D)
  (hGv : Proof.Mgf1.Valid Gs) {f : MdFns} {dn : String} (hdo : DigOK H.P) {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns}

include hH hHs hHl hHv hGh hGl hGv hdo in
/-- After the copy and `fitH`: the checks of the lengths, then verification's
checks or 0. -/
theorem body_ok {tsH tsG : List FnTable} {s u : State} (hp : PreC H.D tsH tsG s)
    (ht : TabsAt H dn f Gm g (stackArg s 0) (stackArg s 1) s) (hu : AtCT s u)
    (hem : ∀ i < (s.gpr .x2).toNat, u.mem (off (s.gpr .x6) (oEm + i)) = (emB s).getD i 0)
    (h9 : u.gpr .x9 = BitVec.ofNat 64 (s.gpr .x2).toNat)
    (h10 : (u.gpr .x10 != 0) = decide ((s.gpr .x2).toNat < H.D + 2)) :
    WP isa (.ite (.nonzero .x .x10) ret0 (seqs [expLen, .block (saltFits H),
      .ite (.nonzero .x .x10) ret0 (chkMain f H g)])) u fun t =>
        MidC s t ∧ (t.gpr .x0).setWidth 32 = if chkOut H.D Hs Gs s then 1 else 0 := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD : H.D + 2 < 4096 := by have := hH.sizes.DN; have := hH.N_le; omega_arith
  have hel := hp.hel
  have hshort : (s.gpr .x2).toNat < Hs.len +
      (Spec.RsaPss.expectedSaltLen (s.gpr .x4) ((s.gpr .x5).setWidth 32)).getD 0 + 2 → chkOut H.D Hs Gs s = false :=
    fun h => by
      unfold chkOut Spec.RsaPss.verifyEncoding
      exact ite_eq_left_of_eq_true _ _ (eq_true (Or.inr (Or.inr (by rw [← hel]; exact h)))) |>.trans rfl
  refine WP.ite _ (eval_nonzero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [h10, decide_eq_true_eq] at hb
    exact ret0_ok hu.e.toMid (hshort (by rw [hHl]; omega_using [hb]))
  rw [h10, decide_eq_false_iff_not] at hb
  have L := lay_of hp hu.e.sp hu.e.x20 hu.e.wr
  unfold seqs seqs
  refine WP.seq (WP.mono_syms (expLen_ok L hu.e.fr.any hu.e.fr.sl) fun u₁ ⟨O₁, x12₁⟩ sy₁ => ?_)
  refine WP.seq (WP.mono_syms (saltFitsR_ok H hD (a := (s.gpr .x2).toNat) (by omega_using [hb]) (by omega_using [hk2])
    (by rw [O₁.get .x9, h9]) x12₁) fun u₂ ⟨O₂, x9₂, x10₂⟩ sy₂ => ?_)
  have hu₂ := (hu.only O₁ sy₁).only O₂ sy₂
  have hsv : (if anyC s = 0 then s.gpr .x4 else 0).toNat =
      (Spec.RsaPss.expectedSaltLen (s.gpr .x4) ((s.gpr .x5).setWidth 32)).getD 0 := by
    rw [expected_eq]; split <;> rfl
  rw [hsv] at x10₂
  refine WP.ite _ (eval_nonzero _ _) (fun hb₂ => ?_) (fun hb₂ => ?_)
  · rw [x10₂, decide_eq_true_eq] at hb₂
    exact ret0_ok hu₂.e.toMid (hshort (by rw [hHl]; omega_using [hb₂]))
  rw [x10₂, decide_eq_false_iff_not] at hb₂
  have hs : anyC s = 0 → (s.gpr .x4).toNat < (s.gpr .x2).toNat - H.D - 1 := fun ha => by
    rw [expected_eq, ite_eq_left ha, Option.getD_some] at hb₂
    omega_using [hb, hb₂]
  refine WP.mono (chkMain_ok hH hGm hHs hHl hHv hGh hGl hGv hdo hp ht hu₂
    (fun i hi => by rw [O₂.mem, O₁.mem]; exact hem i hi) x9₂ (by omega_using [hb]) hs) fun t ⟨m, r⟩ => ⟨m, ?_⟩
  have hfit : Hs.len + (Spec.RsaPss.expectedSaltLen (s.gpr .x4) ((s.gpr .x5).setWidth 32)).getD 0 + 2 ≤
      Spec.RsaPss.emLength (s.gpr .x3).toNat := by rw [← hel, hHl]; omega_using [hb, hb₂]
  rw [r (chkOut H.D Hs Gs s) ?_]
  · split <;> rfl
  rw [chkOut, ← hHl, RsaPss.verifyEncoding_bytes₂ Gs Hs hGv (VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _)
    (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length, hel]) hfit, ← hel, expected_eq]
  exact ⟨fun h => ⟨fun h01 => absurd h01 (by decide), h⟩, fun h => h.2⟩

include hH hHs hHl hHv hGh hGl hGv hdo in
theorem code_ok {tsH tsG : List FnTable} {s : State} (hp : PreC H.D tsH tsG s)
    (ht : TabsAt H dn f Gm g (stackArg s 0) (stackArg s 1) s) :
    WP isa (checkEncoding f H g) s (Post H.D Hs Gs s) := by
  have hD : H.D + 2 < 4096 := by have := hH.sizes.DN; have := hH.N_le; omega_arith
  have hk2 := hp.k2
  unfold checkEncoding
  refine WP.alloc (by decide) (by have := fb_toNat hp; omega_using [this]) ?_
  unfold chkBody seqs seqs seqs seqs
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (prologue_ok hp (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
    (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun u hu sy => ?_
  refine WP.mono (tabSlots_ok hp hu (by rw [sy]; simp [allocated])) fun u₀ hu₀ => ?_
  refine WP.seq (WP.mono_syms (copyIn_okC hp hu₀.e) fun u₁ ⟨hu₁, hem, hf₁⟩ sy₁ => ?_)
  have hu₁' : AtCT s u₁ := hu₀.of hp hu₁ hf₁ sy₁
  refine WP.seq (WP.mono_syms (fitH_ok H hD (k := (s.gpr .x2).toNat)
    (by rw [hu₁.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_using [hk2])) fun u₂ ⟨O₂, x9₂, x10₂⟩ sy₂ => ?_)
  refine WP.seq (WP.mono (body_ok hH hGm hHs hHl hHv hGh hGl hGv hdo hp ht (hu₁'.only O₂ sy₂)
    (fun i hi => by rw [O₂.mem]; exact hem i hi) x9₂ x10₂) fun t ⟨m, r⟩ => ?_)
  exact WP.mono (restore_frame_ok m.sp m.wr m.v m.fr.sv) fun w ⟨habi, hx0, _⟩ _ _ _ =>
    ⟨⟨habi.1, habi.2.1, habi.2.2⟩, by dsimp only; rw [hx0]; exact r⟩

end

end VG.Proof.RsaPss.AArch64.Chk

end

end

/-!
# EMSA-PSS's check of an encoding on AArch64: constant time

`code_ct`: two runs of `checkEncoding` from entry states with the same
public data leak the same trace. The prologue, the copy of the encoding and
the checks of the lengths branch and address memory by the lengths only (the
taint analysis, and correctness for the branches and for `any_salt_len`,
loaded from its slot: `expLen_ct`); verification's checks are `check_ct`,
from the registers and slots the anchor fixes (`vr_of`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Chk

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only wp_nil eval_zero eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_map two_ite two_alloc wp_ldrSp)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (off two_taintE two_step pins_nil zH PssChecks fitH_ok saltFitsR_ok expLen_ok
  dbRegs_ok)
open VG.Proof.RsaPss.AArch64.Sgn (fb)
open VG.Proof.RsaPss.AArch64.Enc (ret0_ct)

/-- After the checks of the lengths. -/
structure AtS (D : Nat) (s w : State) : Prop where
  c : AtCT s w
  em : ∀ i < (s.gpr .x2).toNat, w.mem (off (s.gpr .x6) (oEm + i)) = (emB s).getD i 0
  x9 : w.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x2).toNat - (D + 2))
  x10 : (w.gpr .x10 != 0) = decide ((s.gpr .x2).toNat - (D + 2) <
    (if anyC s = 0 then s.gpr .x4 else 0).toNat)
  hk : ¬ (s.gpr .x2).toNat < D + 2

/-- `expLen`: `any_salt_len` is loaded from its slot, and branched on. -/
theorem expLen_ct {T : Tabs} {Φ : State → State → Prop} (hΦ : ∀ a u, Φ a u → ∃ s, E T a s ∧ AtC s u) :
    RelCT isa (Two Φ) expLen (Two fun a t => t.sp = fb a) := by
  refine two_post ?_ fun a u h => by
    obtain ⟨s, e, hu⟩ := hΦ a u h
    exact WP.mono (expLen_ok (lay_of e.1 hu.sp hu.x20 hu.wr) hu.fr.any hu.fr.sl) fun t ⟨O, _⟩ => by
      rw [O.sp, hu.sp, e.fb]
  unfold expLen
  have pin : ∀ {Φ : State → State → Prop}, (∀ a t, Φ a t → t.sp = fb a) → Pins Φ [] := fun h =>
    pins_nil fun a s₁ s₂ h₁ h₂ => by rw [h a s₁ h₁, h a s₂ h₂]
  refine two_step (Ψ := fun a t => t.sp = fb a ∧ t.gpr .x13 = anyC a)
    (two_taint [] (pin fun a t h => by obtain ⟨s, e, hu⟩ := hΦ a t h; rw [hu.sp, e.fb]) (by taint_decide))
    (fun a u h => ?_) ?_
  · obtain ⟨s, e, hu⟩ := hΦ a u h
    unfold ld
    have hin : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 sAny) 8 := by
      rw [hu.sp, hu.rd, hu.wr]
      exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ (by decide) (by decide)))
    refine wp_ldrSp (by decide) hin fun u' o x => wp_nil ⟨by rw [o.sp, hu.sp, e.fb], ?_⟩
    rw [x, hu.sp]; exact hu.fr.any.trans e.any
  refine two_ite (fun a s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2])
    (two_taint [] (pin fun a t h => h.1.1) (by taint_decide)) (two_taint [] (pin fun a t h => h.1.1) (by taint_decide))

/-- After `dbRegs`: the checks' start. -/
theorem vr_of {T : Tabs} {a s t : State} (ok : VOk T.H.D a) (e : E T a s) (htt : AtCT s t)
    (h24 : t.gpr .x24 = off (s.gpr .x6) (oEm + 0)) (h25 : t.gpr .x25 = BitVec.ofNat 64 (dbA T.H.D s)) :
    VR T T.H.D (vregs T.H.D) vslots a t := by
  have ht := htt.e
  have L := lay_of e.1 ht.sp ht.x20 ht.wr
  rw [e.fb, show s.gpr .x6 = scr a from e.scr] at L
  have h2 := e.gpr (r := .x2) (by decide)
  refine ⟨⟨s, t, e, htt, Frame.refl _ _, rfl, ht.rd, ht.wr⟩, L, fun q hq => ?_, fun q hq => ?_, ok, rfl⟩
  · simp only [vregs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · rw [ht.x19]; exact congrArg (off · oSt) e.scr
    · rw [ht.x21]; exact congrArg (off · oDig) e.scr
    · rw [ht.x23, h2]
    · rw [h24]; exact congrArg (off · (oEm + 0)) e.scr
    · rw [h25]; show BitVec.ofNat 64 ((s.gpr .x2).toNat - 0 - T.H.D - 1) = BitVec.ofNat 64 ((a.gpr .x2).toNat - 0 - T.H.D - 1)
      rw [h2]
  · simp only [vslots, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · rw [← e.fb]; exact ht.lo
    · rw [← e.fb]; exact ht.c.trans (by show (cC s).setWidth 64 = (cC a).setWidth 64; rw [cC, cC, e.z])
    · rw [← e.fb]; exact ht.fr.any.trans e.any
    · rw [← e.fb]; exact ht.fr.sl.trans (e.gpr (by decide))
    · rw [← e.fb]; exact ht.fr.dig.trans (e.gpr (by decide))

section
variable {T : Tabs} (hH : HashOK T.H) (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK T.G)
  {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = T.G.D)
  (hGv : Proof.Mgf1.Valid Gs) (hc : PssChecks T.H.P T.H.D) (hdo : DigOK T.H.P)

include hH hGh hGl hGv hc hdo in
theorem main_ct :
    RelCT isa (Two fun a w => (∃ s, E T a s ∧ AtS T.H.D s w) ∧ isa.eval (.nonzero .x .x10) w = some false)
      (chkMain T.f T.H T.g) (Two fun a t => t.sp = fb a) := by
  show RelCT isa _ (.seq (.block dbRegs) (seqs [.block acc0, mgfXor T.H T.g, .block clearTop, posScan, posCheck,
    FixedSalt.select T.f T.H])) _
  refine RelCT.seq (two_post (Ψ := VR T T.H.D (vregs T.H.D) vslots)
    (two_taint [] (fun a w₁ w₂ ⟨⟨s₁, h₁, j₁⟩, _⟩ ⟨⟨s₂, h₂, j₂⟩, _⟩ =>
      ⟨by rw [j₁.c.e.sp, j₂.c.e.sp, h₁.fb, h₂.fb], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a w ⟨⟨s, e, hS⟩, hcond⟩ => ?_) (check_ct hH hGm hGh hGl hGv hc hdo)
  have hk := hS.hk
  have hp := e.1
  have hk1 := hp.k1; have hk2 := hp.k2
  have h2 := e.gpr (r := .x2) (by decide)
  have ok : VOk T.H.D a := by
    refine ⟨?_, ?_, ?_, Nat.zero_le 1, ?_⟩
    · show 1 ≤ (a.gpr .x2).toNat; rw [← h2]; exact hk1
    · show (a.gpr .x2).toNat ≤ 1024; rw [← h2]; exact hk2
    · show T.H.D + 2 ≤ (a.gpr .x2).toNat - 0; rw [← h2]; omega_using [hk]
    · intro ha
      have hb := hS.x10
      have he : anyC s = 0 := e.any.trans ha
      rw [eval_nonzero] at hcond
      rw [Option.some.inj hcond, ite_eq_left he] at hb
      have hn := of_decide_eq_false hb.symm
      show (a.gpr .x4).toNat < (a.gpr .x2).toNat - 0 - T.H.D - 1
      rw [← e.gpr (r := .x4) (by decide), ← h2]
      omega_using [hk, hn]
  refine WP.mono_syms (dbRegs_ok (lay_of hp hS.c.e.sp hS.c.e.x20 hS.c.e.wr) hS.x9 hS.c.e.lo)
    fun u ⟨O, x25, x24⟩ sy => vr_of ok e (hS.c.only O sy) x24 (by
      rw [x25]; show _ = BitVec.ofNat 64 ((s.gpr .x2).toNat - 0 - T.H.D - 1); congr 1; omega_using [hk])

include hH hGh hGl hGv hc hdo in
theorem code_ct : RelCT isa (Two (E T)) (checkEncoding T.f T.H T.g) fun _ _ => True := by
  have hD : T.H.D + 2 < 4096 := by have := hH.sizes.DN; have := hH.N_le; omega_arith
  unfold checkEncoding
  refine two_alloc (R := fun _ _ => True) ?_
  unfold chkBody seqs seqs seqs seqs
  rw [show chkPrologue ++ tabSlots = (chkPrologue ++ [arg .x9 0]) ++ tabSlots.tail from rfl]
  refine RelCT.seq_block_append ?_
  -- The prologue.
  refine RelCT.seq (two_post (Ψ := fun a u₁ => ∃ s u, E T a s ∧ AtC s u ∧ Only [.x9] u u₁ ∧
      u₁.gpr .x9 = stackArg s 0 ∧ u₁.syms = s.syms)
    (two_taint [] (fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocated, h₁.2.1.sp, h₂.2.1.sp],
        fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a u ⟨s, h, hu⟩ => ?_) ?_
  · subst hu
    rw [WP.block_append_iff]
    exact WP.mono_syms (prologue_ok h.1 (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
      (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun t ht sy =>
      WP.mono_syms (arg0_ok h.1 ht) fun u₁ ⟨o, e9⟩ sy' => ⟨s, t, h, ht, o, e9, sy'.trans sy⟩
  -- The tables' words.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, E T a s ∧ AtCT s u)
    (two_taint [.x9] (fun _ u₁ u₂ ⟨s₁, v₁, h₁, j₁, o₁, x₁, _⟩ ⟨s₂, v₂, h₂, j₂, o₂, x₂, _⟩ =>
        ⟨by rw [o₁.sp, o₂.sp, j₁.sp, j₂.sp, h₁.fb, h₂.fb], fun r hr => by
          rw [List.mem_singleton.mp hr, x₁, x₂, h₁.arg (by decide), h₂.arg (by decide)]⟩) (by taint_decide))
    fun a u₁ ⟨s, u, h, hu, o, e9, sy⟩ => WP.mono (tabSlotsT_ok h.1 hu o e9 sy) fun t ht => ⟨s, h, ht⟩) ?_
  -- The copy.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, E T a s ∧ AtCT s u ∧
      ∀ i < (s.gpr .x2).toNat, u.mem (off (s.gpr .x6) (oEm + i)) = (emB s).getD i 0)
    (two_taint [.x1, .x20, .x23] (fun a u₁ u₂ ⟨s₁, h₁, j₁⟩ ⟨s₂, h₂, j₂⟩ => ⟨by rw [j₁.e.sp, j₂.e.sp, h₁.fb, h₂.fb],
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [j₁.e.x1, j₂.e.x1, h₁.gpr (by decide), h₂.gpr (by decide)]
        · rw [j₁.e.x20, j₂.e.x20, h₁.gpr (by decide), h₂.gpr (by decide)]
        · rw [j₁.e.x23, j₂.e.x23, h₁.gpr (by decide), h₂.gpr (by decide)]⟩) (by taint_decide))
    fun a u ⟨s, h, hu⟩ => WP.mono_syms (copyIn_okC h.1 hu.e) fun t ⟨ht, hem, hf⟩ sy =>
      ⟨s, h, hu.of h.1 ht hf sy, hem⟩) ?_
  -- `fitH`.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, E T a s ∧ AtCT s u ∧
      (∀ i < (s.gpr .x2).toNat, u.mem (off (s.gpr .x6) (oEm + i)) = (emB s).getD i 0) ∧
      u.gpr .x9 = BitVec.ofNat 64 (s.gpr .x2).toNat ∧ (u.gpr .x10 != 0) = decide ((s.gpr .x2).toNat < T.H.D + 2))
    (two_taintE [] (fun _ _ _ ⟨s₁, h₁, j₁, _⟩ ⟨s₂, h₂, j₂, _⟩ => ⟨by rw [j₁.e.sp, j₂.e.sp, h₁.fb, h₂.fb],
        fun _ h => absurd h List.not_mem_nil⟩)
      (c' := Code.eraseOff (.block (fitH zH))) rfl (by taint_decide))
    fun a u ⟨s, h, hu, hem⟩ => ?_) ?_
  · have hk2 := h.1.k2
    exact WP.mono_syms (fitH_ok T.H hD (k := (s.gpr .x2).toNat)
      (by rw [hu.e.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_using [hk2])) fun t ⟨O, x9, x10⟩ sy =>
      ⟨s, h, hu.only O sy, fun i hi => by rw [O.mem]; exact hem i hi, x9, x10⟩
  refine RelCT.seq ?_ (two_taint (Φ := fun a t => t.sp = fb a) [] (fun a t₁ t₂ h₁ h₂ =>
    ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, _, _, _, x₁⟩ ⟨s₂, h₂, _, _, _, x₂⟩ => by
      rw [eval_nonzero, eval_nonzero, x₁, x₂, h₁.gpr (r := .x2) (by decide), h₂.gpr (r := .x2) (by decide)])
    (ret0_ct fun a u ⟨⟨s, h, j, _⟩, _⟩ => by rw [j.e.sp, h.fb]) ?_
  refine RelCT.assoc (RelCT.seq (two_post (Ψ := fun a w => ∃ s, E T a s ∧ AtS T.H.D s w)
    (RelCT.seq (expLen_ct fun a u ⟨⟨s, h, j, _⟩, _⟩ => ⟨s, h, j.e⟩) (two_taintE [] (fun a t₁ t₂ h₁ h₂ =>
      ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩)
      (c' := Code.eraseOff (.block (saltFits zH))) rfl (by taint_decide)))
    fun a u ⟨⟨s, h, j, hem, x9, x10⟩, hb⟩ => ?_) ?_)
  · rw [eval_nonzero, x10, Option.some.injEq, decide_eq_false_iff_not] at hb
    have hk2 := h.1.k2
    refine WP.seq (WP.mono_syms (expLen_ok (lay_of h.1 j.e.sp j.e.x20 j.e.wr) j.e.fr.any j.e.fr.sl)
      fun u₁ ⟨O₁, x12₁⟩ sy₁ => ?_)
    exact WP.mono_syms (saltFitsR_ok T.H hD (a := (s.gpr .x2).toNat) (by omega_using [hb]) (by omega_using [hk2])
      (by rw [O₁.get .x9, x9]) x12₁)
      fun w ⟨O₂, x9₂, x10₂⟩ sy₂ => ⟨s, h, (j.only O₁ sy₁).only O₂ sy₂,
        fun i hi => by rw [O₂.mem, O₁.mem]; exact hem i hi, x9₂, x10₂, hb⟩
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, j₁⟩ ⟨s₂, h₂, j₂⟩ => by
      rw [eval_nonzero, eval_nonzero, j₁.x10, j₂.x10, h₁.gpr (r := .x2) (by decide), h₂.gpr (r := .x2) (by decide),
        h₁.gpr (r := .x4) (by decide), h₂.gpr (r := .x4) (by decide), h₁.any, h₂.any])
    (ret0_ct fun a u ⟨⟨s, h, j⟩, _⟩ => by rw [j.c.e.sp, h.fb]) (main_ct hH hGm hGh hGl hGv hc hdo)

end

end VG.Proof.RsaPss.AArch64.Chk
