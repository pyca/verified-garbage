module

public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkFrame
public import VerifiedGarbage.Proof.RsaPss.X86_64.CtBase
public import VerifiedGarbage.Proof.RsaPss.X86_64.CtHashCT
public import VerifiedGarbage.Proof.RsaPss.X86_64.MgfCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFixed
import VerifiedGarbage.Proof.RsaPss.X86_64.PrefixCheck
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBlocks
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtBase
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.RsaPss.X86_64.SignEnc
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `RsaPss.X86_64.ChkCtMid`, which only this module used -/

section

/-! ### `RsaPss.X86_64.ChkCtBase`, which only this module used -/

section

/-!
# EMSA-PSS's check of an encoding on x86-64: two runs

As for verification (`VerifyCtBase`): two runs of `checkEncoding` from states
meeting `chkK.pre` whose public data agree (`VSib a s`) compute the same
public values (`vw`): the arguments, the encoding's length, `DB`'s place and
length, the mask of the top bits, the expected salt length and the hash's
blocks. The digest, the encoding, and what the code derives from them (the
salt's length when any is allowed) stay out of `vw`. A run's state between
two pieces is described by `VS`; both runs then start the next piece's
taint analysis from the same public values (`vtwo`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Chk

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable (T : Tabs)

/-- `chkK.pub`, which does not depend on the hash functions. -/
def CPub (s₁ s₂ : State) : Prop :=
  (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .rsp], s₁.gpr r = s₂.gpr r) ∧
    (s₁.gpr .r9).setWidth 32 = (s₂.gpr .r9).setWidth 32 ∧
    (List.range 4).map (stackArg s₁) = (List.range 4).map (stackArg s₂) ∧
    tabWords s₁.mem (stackArg s₁ 2) (stackArg s₁ 3) = tabWords s₂.mem (stackArg s₂ 2) (stackArg s₂ 3)

/-- The entry state `s` of a run, and the first's, `a`: both meet the
precondition, and their public data agree. -/
def VSib (a s : State) : Prop := Pre T a ∧ CPub a s ∧ Pre T s

/-- A predicate of the state of a run, given its entry state, for every run
whose entry state agrees with `a`. -/
def VAt (J : State → State → Prop) (a t : State) : Prop := ∃ s, VSib T a s ∧ J s t

theorem vpub_refl (s : State) : CPub s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

variable {T}

namespace VSib

variable {a s : State} (h : VSib T a s)
include h

theorem gpr {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) : s.gpr r = a.gpr r :=
  (h.2.1.1 r hr).symm

theorem rsl : s.gpr .r8 = a.gpr .r8 := h.gpr (by decide)
theorem r9 : (s.gpr .r9).setWidth 32 = (a.gpr .r9).setWidth 32 := h.2.1.2.1.symm

theorem arg {i : Nat} (hi : i < 4) : stackArg s i = stackArg a i := by
  have := congrArg (fun l => l.getD i 0) h.2.1.2.2.1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some] at this
  exact this.symm

theorem arg0 : stackArg s 0 = stackArg a 0 := h.arg (by decide)
theorem arg1 : stackArg s 1 = stackArg a 1 := h.arg (by decide)

theorem pa : Pre T a := h.1
theorem ps : Pre T s := h.2.2

/-- The words of the tables. -/
theorem tws : s.mem.readW (off (stackArg s 2) 0) 64 = a.mem.readW (off (stackArg a 2) 0) 64 ∧
    s.mem.readW (off (stackArg s 2) 24) 64 = a.mem.readW (off (stackArg a 2) 24) 64 ∧
    s.mem.readW (off (stackArg s 2) 32) 64 = a.mem.readW (off (stackArg a 2) 32) 64 ∧
    s.mem.readW (off (stackArg s 3) 0) 64 = a.mem.readW (off (stackArg a 3) 0) 64 ∧
    s.mem.readW (off (stackArg s 3) 8) 64 = a.mem.readW (off (stackArg a 3) 8) 64 ∧
    s.mem.readW (off (stackArg s 3) 16) 64 = a.mem.readW (off (stackArg a 3) 16) 64 ∧
    s.mem.readW (off (stackArg s 3) 48) 64 = a.mem.readW (off (stackArg a 3) 48) 64 := by
  have := h.2.1.2.2.2.symm
  simp only [tabWords, List.cons.injEq, and_true] at this
  exact this

/-- The runs' symbols agree on the tables' functions. -/
theorem syH : SyH T.H T.dn T.f a.syms s.syms :=
  ⟨h.ps.tabs.hf, h.ps.tabs.h0.symm.trans (h.tws.1.trans h.pa.tabs.h0),
    h.ps.tabs.h3.symm.trans (h.tws.2.1.trans h.pa.tabs.h3), h.ps.tabs.h4.symm.trans (h.tws.2.2.1.trans h.pa.tabs.h4)⟩

theorem syG : SyG T.G T.g a.syms s.syms :=
  ⟨h.ps.tabs.gf, h.ps.tabs.g0.symm.trans (h.tws.2.2.2.1.trans h.pa.tabs.g0),
    h.ps.tabs.g1.symm.trans (h.tws.2.2.2.2.1.trans h.pa.tabs.g1),
    h.ps.tabs.g2.symm.trans (h.tws.2.2.2.2.2.1.trans h.pa.tabs.g2)⟩

theorem fb : fb s = fb a := by
  simp only [VG.Proof.RsaPss.X86_64.fb, h.gpr (r := .rsp) (by decide)]

theorem wr : s.wr = a.wr := by rw [h.ps.hwr, h.pa.hwr, h.arg0, h.arg1]

theorem frR : frR s = ⟨VG.Proof.RsaPss.X86_64.fb a, frameBytes⟩ := by
  simp only [VG.Proof.RsaPss.X86_64.frR, h.fb]

end VSib

/-! ## The public values -/

/-- `lo`, always 0. -/
def vlo (_s : State) : Nat := 0

/-- `emLen`. -/
def veml (s : State) : Nat := (s.gpr .rdx).toNat - vlo s

/-- The mask of `maskedDB`'s first byte. -/
def cmask (s : State) : Byte := (0xFF : Byte) >>> (8 * (s.gpr .rdx).toNat - (s.gpr .rcx).toNat)

/-- `dbLen`. -/
def vdb (D : Nat) (s : State) : Nat := veml s - D - 1

/-- The blocks of the hash of `M'`. -/
def vnb (H : Hash) (s : State) : Nat := (vdb H.D s + (7 + H.D + H.P.L)) / H.P.B + 1

/-- The expected salt length's register, 0 if any. -/
def vrdx (s : State) : BitVec 64 := if (s.gpr .r9).setWidth 32 = 0 then s.gpr .r8 else 0

/-- The public words of the frame, by index. -/
def vw (H : Hash) (s : State) (k : Nat) : BitVec 64 :=
  match k with
  | 8 => s.mem.readW (off (stackArg s 2) 0) 64
  | 9 => s.mem.readW (off (stackArg s 2) 24) 64
  | 10 => s.mem.readW (off (stackArg s 2) 32) 64
  | 11 => s.mem.readW (off (stackArg s 3) 0) 64
  | 12 => s.mem.readW (off (stackArg s 3) 8) 64
  | 13 => s.mem.readW (off (stackArg s 3) 16) 64
  | 14 => s.mem.readW (off (stackArg s 3) 48) 64
  | 17 => s.gpr .rdx
  | 21 => stackArg s 0
  | 23 => off (stackArg s 0) (oEm + vlo s)
  | 24 => BitVec.ofNat 64 (vdb H.D s)
  | 25 => BitVec.setWidth 64 (cmask s)
  | 26 => BitVec.ofNat 64 (vlo s)
  | 28 => BitVec.ofNat 64 (vnb H s)
  | 35 => if (s.gpr .r9).setWidth 32 = 0 then 0 else 1
  | 36 => s.gpr .r8
  | 37 => s.gpr .rdi
  | 38 => s.gpr .rsi
  | _ => 0

/-- The public words `ks`. -/
def pw (H : Hash) (s : State) (ks : List Nat) : List (Nat × BitVec 64) := ks.map fun k => (k, vw H s k)

namespace VSib

variable {a s : State} (h : VSib T a s)
include h

theorem vlo : vlo s = vlo a := by have _ := h; rfl
theorem veml : veml s = veml a := by
  simp only [VG.Proof.RsaPss.X86_64.Chk.veml, h.vlo, h.gpr (r := .rdx) (by decide)]
theorem vdb {D : Nat} : vdb D s = vdb D a := by simp only [VG.Proof.RsaPss.X86_64.Chk.vdb, h.veml]
theorem vnb {H : Hash} : vnb H s = vnb H a := by simp only [VG.Proof.RsaPss.X86_64.Chk.vnb, h.vdb]
theorem vrdx : vrdx s = vrdx a := by
  simp only [VG.Proof.RsaPss.X86_64.Chk.vrdx, h.r9, h.gpr (r := .r8) (by decide)]
theorem cmask : cmask s = cmask a := by
  simp only [VG.Proof.RsaPss.X86_64.Chk.cmask, h.gpr (r := .rdx) (by decide), h.gpr (r := .rcx) (by decide)]

theorem vw {H : Hash} (k : Nat) : vw H s k = vw H a k := by
  unfold VG.Proof.RsaPss.X86_64.Chk.vw
  split <;> simp only [h.gpr (r := .rsi) (by decide), h.gpr (r := .rdi) (by decide),
    h.gpr (r := .rdx) (by decide), h.gpr (r := .r8) (by decide), h.r9, h.arg0, h.vlo, h.vdb, h.vnb, h.cmask,
    h.tws.1, h.tws.2.1, h.tws.2.2.1, h.tws.2.2.2.1, h.tws.2.2.2.2.1, h.tws.2.2.2.2.2.1, h.tws.2.2.2.2.2.2]

/-- The frame and the working space are apart. -/
theorem rest : RestOk 1 (VG.Proof.RsaPss.X86_64.fb a) a.wr := by
  have hp := h.pa
  refine ⟨by rw [hp.hwr]; rfl, ?_, ?_⟩
  · rw [hp.hwr]
    refine List.pairwise_pair.mpr ?_
    exact (hp.dKs.sub_left (frame_sub a))
  · rw [hp.hwr]; intro r hr
    rw [List.mem_singleton.mp hr]
    have := hp.wS; dsimp only; omega_using [this]

end VSib

/-! ## A run's state between pieces -/

/-- The public words after the checks. -/
def K5 : List Nat := [8, 9, 10, 11, 12, 13, 14, 17, 21, 25, 26, 35, 36, 37, 38]

/-- And with `DB`'s. -/
def KM : List Nat := [8, 9, 10, 11, 12, 13, 14, 17, 21, 23, 24, 25, 26, 35, 36, 37, 38]

theorem km_k5 {k : Nat} (h : k ∈ KM) (h23 : k ≠ 23) (h24 : k ≠ 24) : k ∈ K5 := by
  simp only [KM, K5, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega_using [h23, h24, h]

theorem km_lt {k : Nat} (h : k ∈ KM) : k < nW := by
  simp only [KM, List.mem_cons, List.not_mem_nil, or_false] at h; unfold nW frameBytes; omega_using [h]

/-- A run, with entry state `s`, between two pieces: its frame, its public
words `ks` (`vw`), the registers `rs`, and what else is true of its working
space and words (`X`). -/
structure VS (H : Hash) (s t : State) (ks : List Nat) (rs : List (Reg × BitVec 64))
    (X : (Nat → Byte) → (Nat → BitVec 64) → Prop) : Prop where
  L : Lay t (fb s) (stackArg s 0)
  wr : t.wr = frR s :: s.wr
  W : ∃ V W, Rep t.mem (fb s) (stackArg s 0) V W ∧ (∀ k ∈ ks, W k = vw H s k) ∧ X V W
  regs : ∀ p ∈ rs, t.gpr p.1 = p.2
  sy : t.syms = s.syms

variable {H : Hash}

theorem vs_pub {a s t : State} (S : VSib T a s) {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VS H s t ks rs X) :
    Pub (fb a) (stackArg a 0) a.wr (pw H a ks) rs X t := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  refine ⟨?_, ?_, ⟨V, W, ?_, fun p hp => ?_, hx⟩, h.regs⟩
  · rw [← S.fb, ← S.arg0]; exact h.L
  · rw [h.wr, S.frR, S.wr]
  · rw [← S.fb, ← S.arg0]; exact R
  · simp only [pw, List.mem_map] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rw [hw k hk, S.vw]

/-- A piece the analysis checks from `pT 1 ks rgs`. -/
theorem vtwo {Φ : State → State → Prop} {c : Prog isa} (ks : List Nat) (rgs : List Reg)
    (rs : State → List (Reg × BitVec 64))
    (hΦ : ∀ a t, Φ a t → ∃ s X, VSib T a s ∧ VS H s t ks (rs a) X) (hr : ∀ a, (rs a).map Prod.fst = rgs)
    (hks : ∀ k ∈ ks, k < nW) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (pT 1 ks rgs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_pub 1 ks rgs fb (fun a => stackArg a 0) State.wr (fun a => pw H a ks) rs
    (fun a t h => let ⟨_, X, S, v⟩ := hΦ a t h; ⟨X, vs_pub S v⟩) (fun a t h => let ⟨_, _, S, _⟩ := hΦ a t h; S.rest)
    (fun a => by simp [pw, Function.comp_def]) hr hks h

/-- `VS` after code that keeps the memory and the registers but `rs'`. -/
theorem VS.keep {s t t' : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VS H s t ks rs X) {rs' : List Reg} (k : Keep rs' t t')
    (hm : t'.mem = t.mem) (hsp : Reg.rsp ∉ rs') (hrs : ∀ p ∈ rs, p.1 ∉ rs') (hs : t'.syms = t.syms) :
    VS H s t' ks rs X :=
  ⟨h.L.congr (k.gpr hsp) k.2.2 (by rw [hm]), k.2.2.trans h.wr, by rw [hm]; exact h.W,
    fun p hp => (k.gpr (hrs p hp)).trans (h.regs p hp), hs.trans h.sy⟩

/-- `VS` after code that keeps the regions and the scratch slot. -/
theorem VS.next {s t t' : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VS H s t ks rs X) (L' : Lay t' (fb s) (stackArg s 0))
    (hwr : t'.wr = t.wr) {V' : Nat → Byte} {W' : Nat → BitVec 64} (R' : Rep t'.mem (fb s) (stackArg s 0) V' W')
    (hw : ∀ k ∈ ks', W' k = vw H s k) (hx : X' V' W') (hs : t'.syms = t.syms) : VS H s t' ks' [] X' :=
  ⟨L', hwr.trans h.wr, ⟨V', W', R', hw, hx⟩, (fun _ hp => by cases hp), hs.trans h.sy⟩


theorem VS.sub {s t : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VS H s t ks rs X) (hks : ∀ k ∈ ks', k ∈ ks)
    (rs' : List (Reg × BitVec 64)) (hrs : ∀ p ∈ rs', t.gpr p.1 = p.2) (hX : ∀ V W, X V W → X' V W) :
    VS H s t ks' rs' X' := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  exact ⟨h.L, h.wr, ⟨V, W, R, fun k hk => hw k (hks k hk), hX V W hx⟩, hrs, h.sy⟩

/-- A piece the analysis checks from `pT 1 (ks ++ eks) rgs`: the public
words `ks` of `vw`, and `ex`, of the anchor. -/
theorem vtwoX {α : Type} {Φ : α → State → Prop} {c : Prog isa} (π : α → State) (ks : List Nat)
    (ex : α → List (Nat × BitVec 64)) (eks : List Nat) (rgs : List Reg) (rs : α → List (Reg × BitVec 64))
    (hΦ : ∀ a t, Φ a t → ∃ s, VSib T (π a) s ∧ VS H s t ks (rs a) fun _ W => ∀ p ∈ ex a, W p.1 = p.2)
    (he : ∀ a, (ex a).map Prod.fst = eks) (hr : ∀ a, (rs a).map Prod.fst = rgs)
    (hks : ∀ k ∈ ks ++ eks, k < nW) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (pT 1 (ks ++ eks) rgs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_pub 1 (ks ++ eks) rgs (fun a => fb (π a)) (fun a => stackArg (π a) 0) (fun a => (π a).wr)
    (fun a => pw H (π a) ks ++ ex a) rs
    (fun a t h => by
      obtain ⟨s, S, v⟩ := hΦ a t h
      obtain ⟨L, w, ⟨V, W, R, hw, hx⟩, rg⟩ := vs_pub S v
      exact ⟨fun _ _ => True, L, w, ⟨V, W, R, fun p hp => (List.mem_append.mp hp).elim (hw p) (hx p), trivial⟩, rg⟩)
    (fun a t h => let ⟨_, S, _⟩ := hΦ a t h; S.rest)
    (fun a => by simp [pw, Function.comp_def, he a]) hr hks h

variable (H) in
/-- After the checks: the salt's length fits, `rax = emLen - hLen - 2`. -/
def J7 (s t : State) : Prop :=
  VS H s t K5 [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (veml s - (H.D + 2)) ∧
    t.cf = some (decide (veml s - (H.D + 2) < (vrdx s).toNat)) ∧ H.D + 2 ≤ veml s

variable (H) in
/-- After `DB`'s slots: the frame, the public words, what else `X` says. -/
def JM (X : State → (Nat → Byte) → (Nat → BitVec 64) → Prop) (s t : State) : Prop :=
  VS H s t KM [] (X s) ∧ t.rd = s.rd ∧ H.D + 2 ≤ veml s

end VG.Proof.RsaPss.X86_64.Chk

end

end


/-!
# RSASSA-PSS verification on x86-64: `DB` in two runs

After the call: `acc`'s first bits, `DB ⊕= MGF1(H)` (`mgfXor_ct`), its top
bits, and the scan for its first nonzero byte and the checks of it, each
constant time from the public words of both runs (`JM`). The scan's result,
the salt's position, is secret: only its bound is kept (`X7`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Chk

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {T : Tabs}

theorem km_ne {k j : Nat} (h : k ∈ KM) (hj : j ∉ KM) : k ≠ j := fun e => hj (e ▸ h)

theorem km_upd {s : State} {W : Nat → BitVec 64} (hw : ∀ k ∈ KM, W k = vw T.H s k) {j : Nat} (hj : j ∉ KM)
    (v : BitVec 64) : ∀ k ∈ KM, upd W j v k = vw T.H s k := fun k hk => by
  simp only [upd]; rw [ifn (km_ne hk hj)]; exact hw k hk

/-- After the call, with nothing else. -/
abbrev JT (H : Hash) : State → State → Prop := JM H fun _ _ _ => True

/-- `JM` as a public piece's start. -/
theorem jm_vs {X : State → (Nat → Byte) → (Nat → BitVec 64) → Prop} {a t : State} (h : VAt T (JM T.H X) a t)
    (ks : List Nat) (hks : ∀ k ∈ ks, k ∈ KM := by decide) :
    ∃ s X', VSib T a s ∧ VS T.H s t ks [] X' :=
  let ⟨s, S, h⟩ := h; ⟨s, _, S, h.1.sub hks [] (fun _ hp => by cases hp) fun _ _ x => x⟩

theorem vlo_le (s : State) : vlo s ≤ 1 := Nat.zero_le 1

theorem acc0_ct : RelCT isa (Two (VAt T (JT T.H))) (.block acc0) (Two (VAt T (JT T.H))) := by
  obtain ⟨_, hc⟩ := vFixed.acc0
  refine two_post (vtwo (T := T) (H := T.H) [17, 21, 23, 25, 26] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  refine X86_64.WP.mono_syms (acc0_ok v.L R (c := cmask s) (k := (s.gpr .rdx).toNat) (lo := vlo s)
    (by rw [hw 17 (by decide)]; show s.gpr .rdx = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (hw 23 (by decide)) (by rw [hw 25 (by decide)]; rfl) (hw 26 (by decide))
    (by omega_arith) hk2 (by omega_arith)) fun u ⟨L', k', R'⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' (km_upd hw (by decide) _) trivial sy, k'.2.1.trans hrd, hok⟩

/-- `MGF1`'s anchor: `DB`'s place and length. -/
def mgfA (H : Hash) (a : State) : MA := ⟨fb a, stackArg a 0, a.wr, oEm + vlo a, vdb H.D a, a.syms⟩

/-- A public word of the entry state `a`. -/
theorem pw_w {H : Hash} {a : State} {ks : List Nat} {W : Nat → BitVec 64} (hw : ∀ p ∈ pw H a ks, W p.1 = p.2)
    {k : Nat} (hk : k ∈ ks) : W k = vw H a k :=
  hw (k, vw H a k) (List.mem_map.mpr ⟨k, hk, rfl⟩)

/-- The slots of the table of `MdHash`, in a run. -/
theorem vs_ht {s t : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (hp : Pre T s) (v : VS T.H s t ks rs X) {W : Nat → BitVec 64}
    (hw : ∀ k ∈ ks, W k = vw T.H s k) (h8 : 8 ∈ ks := by decide) (h9 : 9 ∈ ks := by decide)
    (h10 : 10 ∈ ks := by decide) : HT T.H T.dn T.f W t.syms := by
  rw [v.sy]; exact hp.tabs.hf.ht ((hw 8 h8).trans hp.tabs.h0) ((hw 9 h9).trans hp.tabs.h3) ((hw 10 h10).trans hp.tabs.h4)

/-- The slots of the table of `MdHash`, in a run. -/
theorem vs_gt {s t : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (hp : Pre T s) (v : VS T.H s t ks rs X) {W : Nat → BitVec 64}
    (hw : ∀ k ∈ ks, W k = vw T.H s k) (h11 : 11 ∈ ks := by decide) (h12 : 12 ∈ ks := by decide)
    (h13 : 13 ∈ ks := by decide) (h14 : 14 ∈ ks := by decide) : GT T.G T.g W t.syms := by
  rw [v.sy]
  exact hp.tabs.gf.gt ((hw 11 h11).trans hp.tabs.g0) ((hw 12 h12).trans hp.tabs.g1) ((hw 13 h13).trans hp.tabs.g2)
    ((hw 14 h14).trans hp.tabs.g4)

theorem jt_me {a t : State} (h : VAt T (JT T.H) a t) : ME T.G T.g 1 T.H (mgfA T.H a) t := by
  obtain ⟨s, S, v, -, hok⟩ := h
  have hp := S.pa
  have hk1 := hp.k1; have hk2 := hp.k2
  have tb := hp.tabs
  have : vlo a = 0 := rfl; have : veml a = (a.gpr .rdx).toNat - vlo a := rfl
  rw [S.veml] at hok
  obtain ⟨L, w, ⟨V, W, R, hw, -⟩, rg⟩ := vs_pub S v
  refine ⟨⟨S.rest, ⟨by simp only [mgfA]; omega_arith, by simp only [mgfA, vdb]; omega_arith, ?_⟩⟩,
    ⟨L, w, ⟨V, W, R, fun p hp => ?_, trivial⟩, rg⟩, S.syG.tr v.sy⟩
  · simp only [mgfA, vdb, veml] at hok ⊢; omega_arith
  · simp only [mgfA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pw_w hw (k := 21) (by decide)
    · exact pw_w hw (k := 23) (by decide)
    · exact pw_w hw (k := 24) (by decide)
    · exact (pw_w hw (k := 14) (by decide)).trans tb.g4
    · exact (pw_w hw (k := 11) (by decide)).trans tb.g0
    · exact (pw_w hw (k := 12) (by decide)).trans tb.g1
    · exact (pw_w hw (k := 13) (by decide)).trans tb.g2

variable (hH : HashOK T.H) (K : Callees T.H) (hG : Pbkdf2.Md.X86_64.Calls.StreamOK T.G) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = T.G.D) (hGv : Proof.Mgf1.Valid Gs)

include hG hGh hGl hGv in
theorem mgf_ct (hc : HashChecks T.H.P T.H.D 1) :
    RelCT isa (Two (VAt T (JT T.H))) (mgfXor T.H T.g) (Two (VAt T (JT T.H))) := by
  refine two_post (two_map (mgfA T.H) (fun a t h => jt_me h)
    (mgfXor_ct hG hGh hGl hGv hc (fixedChecks (.inl rfl)))) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  refine X86_64.WP.mono_syms (mgfXor_ok hG hGh hGl hGv T.H v.L R (vs_gt hp v hw) (e := oEm + vlo s)
    (db := vdb T.H.D s)
    ⟨by omega_arith, by unfold vdb; omega_arith, by unfold vdb veml at *; unfold oEm; omega_arith⟩ (hw 23 (by decide))
    (hw 24 (by decide))) fun u ⟨L', rd', wr', _, V', W', R', hW', _⟩ sy =>
    ⟨s, S, ⟨L', wr'.trans v.wr, ⟨V', W', R', fun k hk => (hW' k (km_lt hk) (by
      simp only [KM, List.mem_cons, List.not_mem_nil, or_false] at hk; omega_arith)).trans (hw k hk), trivial⟩,
      (fun _ hp => by cases hp), sy.trans v.sy⟩, rd'.trans hrd, hok⟩

theorem clearTop_ct : RelCT isa (Two (VAt T (JT T.H))) (.block clearTop) (Two (VAt T (JT T.H))) := by
  obtain ⟨_, hc⟩ := vFixed.clearTop
  refine two_post (vtwo (T := T) (H := T.H) [23] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  exact X86_64.WP.mono_syms (clearTop_ok v.L R (e := oEm + vlo s) (c := cmask s) (hw 23 (by decide))
    (by rw [hw 25 (by decide)]; rfl) (by unfold oEm oRsa; omega_arith))
    fun u ⟨L', k', R'⟩ sy => ⟨s, S, v.next L' k'.2.2 R' hw trivial sy, k'.2.1.trans hrd, hok⟩

/-- After the scan: its registers. -/
def JC6 (H : Hash) (s t : State) : Prop :=
  JT H s t ∧ ∃ (fd : Bool) (pos : Nat) (val : Byte), pos < vdb H.D s ∧
    t.gpr .rdx = (if fd then BitVec.allOnes 64 else 0) ∧ t.gpr .rsi = BitVec.ofNat 64 pos ∧
    t.gpr .r11 = BitVec.setWidth 64 val

theorem posScan_ct : RelCT isa (Two (VAt T (JT T.H))) posScan (Two (VAt T (JC6 T.H))) := by
  obtain ⟨_, hc⟩ := vFixed.posScan
  refine two_post (vtwo (T := T) (H := T.H) [23, 24] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  have hdb1 : 1 ≤ vdb T.H.D s := by unfold vdb; omega_arith
  exact X86_64.WP.mono_syms (posScan_ok v.L R (e := oEm + vlo s) (db := vdb T.H.D s) (hw 23 (by decide)) (hw 24 (by decide))
    hdb1 (by unfold vdb veml oEm oRsa; omega_arith)) fun u ⟨k', hm', hdx, hsi, h11⟩ sy =>
    ⟨s, S, ⟨v.keep k' hm' (by decide) (fun _ hp => by cases hp) sy, k'.2.1.trans hrd, hok⟩, _, _, _,
      fnz_getD_lt hdb1, hdx, hsi, h11⟩

/-- The length of `M'`, from the salt's position, which is secret. -/
def X7 (H : Hash) (s : State) (_ : Nat → Byte) (W : Nat → BitVec 64) : Prop :=
  ∃ pos, pos < vdb H.D s ∧ W 27 = BitVec.ofNat 64 (vdb H.D s - pos - 1 + (8 + H.D)) ∧
    W 34 = BitVec.ofNat 64 pos

include hH in
theorem posCheck_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JC6 T.H))) (posCheck T.H) (Two (VAt T (JM T.H (X7 T.H)))) := by
  obtain ⟨_, hc⟩ := hc.posCheck
  refine two_post (vtwo (T := T) (H := T.H) [24, 35, 36] [] (fun _ => []) (fun a t h => jm_vs (let ⟨s, S, h⟩ := h;
    ⟨s, S, h.1⟩) _) (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hok⟩, fd, pos, val, hpos, hdx, hsi, h11⟩ => ?_
  obtain ⟨V, W, R, hw, -⟩ := v.W
  exact X86_64.WP.mono_syms (posCheck_ok hH v.L R (db := vdb T.H.D s) (pos := pos) (fd := fd) (val := val)
    (fixed := decide ((s.gpr .r9).setWidth 32 = 0)) (hw 24 (by decide))
    (by rw [hw 35 (by decide)]; simp only [vw, decide_eq_true_eq]) hpos hdx hsi h11) fun u ⟨L', k', R'⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' (km_upd (km_upd (km_upd hw (by decide) _) (by decide) _) (by decide) _)
      ⟨pos, hpos, by simp [upd], by simp [upd]⟩ sy, k'.2.1.trans hrd, hok⟩

/-- Testing the public salt mode before the scan. -/
theorem scanAny_ct : RelCT isa (Two (VAt T (JT T.H)))
    (.block [.mov .rax (.mem (sp sAny)), .alu .test .rax (.reg .rax)])
    (Two fun a t => VAt T (JT T.H) a t ∧
      isa.eval .e t = some (decide (vw T.H a 35 = 0))) := by
  obtain ⟨_, hc⟩ := vFixed.scanAny
  refine two_post (vtwo (T := T) (H := T.H) [35] [] (fun _ => [])
    (fun a t h => jm_vs h _) (fun _ => rfl) (by decide) hc)
    fun a t ⟨s, S, v, hrd, hok⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  refine X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧
    u.zf = some (decide (W 35 = 0))) ?_ rfl) fun u ⟨⟨hm, hz⟩, ku⟩ sy => ?_
  · xrun [ea_sp, v.L.rsp, v.L.ld (d := sAny) (by decide), R.rd (d := sAny) 35 rfl (by decide)]
    rw [BitVec.and_self]
    rfl
  · refine ⟨⟨s, S, v.keep ku hm (by decide) (fun _ hp => by cases hp) sy, ku.2.1.trans hrd, hok⟩, ?_⟩
    change u.zf = _
    rw [hz, hw 35 (by decide), S.vw]

/-- And the bound on the requested length. -/
theorem scanLen_ct : RelCT isa (Two (VAt T (JT T.H)))
    (.block [.mov .rax (.mem (sp sSlen)), .alu .cmp .rax (.mem (sp sDb))])
    (Two fun a t => VAt T (JT T.H) a t ∧
      isa.eval .b t = some (decide ((a.gpr .r8).toNat < vdb T.H.D a))) := by
  obtain ⟨_, hc⟩ := vFixed.scanLen
  refine two_post (vtwo (T := T) (H := T.H) [24, 36] [] (fun _ => [])
    (fun a t h => jm_vs h _) (fun _ => rfl) (by decide) hc)
    fun a t ⟨s, S, v, hrd, hok⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  have hk2 := S.ps.k2
  refine X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧
    u.cf = some (decide ((s.gpr .r8).toNat < vdb T.H.D s))) ?_ rfl) fun u ⟨⟨hm, hz⟩, ku⟩ sy => ?_
  · xrun [ea_sp, v.L.rsp, v.L.ld (d := sSlen) (by decide), v.L.ld (d := sDb) (by decide),
      R.rd (d := sSlen) 36 rfl (by decide), R.rd (d := sDb) 24 rfl (by decide),
      hw 36 (by decide), hw 24 (by decide)]
    simp only [vw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vdb T.H.D s < 2 ^ 64 by unfold vdb veml; omega_arith)]
  · refine ⟨⟨s, S, v.keep ku hm (by decide) (fun _ hp => by cases hp) sy, ku.2.1.trans hrd, hok⟩, ?_⟩
    change u.cf = _
    rw [hz, S.rsl, S.vdb]

/-- After the call, with the salt's length given and less than `DB`'s. -/
def JTF (H : Hash) (s t : State) : Prop := JT H s t ∧ (s.gpr .r8).toNat < vdb H.D s

include hH in
theorem prefixCheck_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JTF T.H))) (prefixCheck T.H) (Two (VAt T (JM T.H (X7 T.H)))) := by
  obtain ⟨_, hc⟩ := hc.prefixCheck
  refine two_post (vtwo (T := T) (H := T.H) [23, 24, 36] [] (fun _ => []) (fun a t h => jm_vs (let ⟨s, S, h⟩ := h;
    ⟨s, S, h.1⟩) _) (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hok⟩, hlt⟩ => ?_
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  refine X86_64.WP.mono_syms (prefixCheck_ok hH v.L R (e := oEm + vlo s) (db := vdb T.H.D s) (sl := (s.gpr .r8).toNat)
    (hw 23 (by decide)) (hw 24 (by decide)) (by rw [hw 36 (by decide)]; simp [vw]) hlt
    (by unfold vdb veml oEm oRsa; omega_arith) (by unfold vdb veml; omega_arith)) fun u ⟨L', k', a', _, R'⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' (km_upd (km_upd (km_upd hw (by decide) _) (by decide) _) (by decide) _)
      ⟨vdb T.H.D s - (s.gpr .r8).toNat - 1, by omega_arith, ?_, by simp [upd]⟩ sy, k'.2.1.trans hrd, hok⟩
  simp only [upd, Nat.reduceEqDiff, ite_true]
  congr 1
  omega_arith

include hH in
theorem scanCheck_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JT T.H))) (scanCheck T.H) (Two (VAt T (JM T.H (X7 T.H)))) := by
  have generic := (posScan_ct (T := T)).seq (posCheck_ct hH hc)
  unfold scanCheck
  refine scanAny_ct.seq (two_ite (fun a t₁ t₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_
    (generic.mono (fun _ _ => two_mono fun _ _ h => h.1.1) fun _ _ h => h))
  refine (scanLen_ct.seq (two_ite (fun a t₁ t₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_
    (generic.mono (fun _ _ => two_mono fun _ _ h => h.1.1) fun _ _ h => h))).mono
    (fun _ _ => two_mono fun _ _ h => h.1.1) (fun _ _ h => h)
  refine (prefixCheck_ct hH hc).mono (fun _ _ => two_mono fun a t ⟨⟨⟨s, S, h⟩, hz⟩, hb⟩ => ?_) fun _ _ h => h
  have hf : (a.gpr .r8).toNat < vdb T.H.D a := by
    rw [hz, Option.some.injEq, decide_eq_true_eq] at hb
    exact hb
  exact ⟨s, S, h, by rwa [S.rsl, S.vdb]⟩

end VG.Proof.RsaPss.X86_64.Chk

end

end


/-!
# RSASSA-PSS verification on x86-64: `M'` and its hash in two runs

`mHash`, `DB` and the shift by the salt's position into `Y`, the hash of
`M'` over the blocks the longest salt needs (`vnb`), and the comparison:
each constant time from the public words of both runs. The shift's ten
passes and the hash's blocks do not depend on the salt's position.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Chk

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {T : Tabs}

/-- After `mHash`: `rcx` is `Y`. -/
def JC8 (H : Hash) (s t : State) : Prop := JM H (X7 H) s t ∧ t.gpr .rcx = off (stackArg s 0) oY

/-- Before pass `j` of the shift. -/
def JS (H : Hash) (j : Nat) (s t : State) : Prop :=
  VS H s t KM [] (fun V W => X7 H s V W ∧ W 46 = BitVec.ofNat 64 (2 ^ j) ∧ W 44 = BitVec.ofNat 64 (10 - j) ∧
    ∃ x, W 45 = BitVec.ofNat 64 x ∧ x < 2 ^ 64) ∧ t.rd = s.rd ∧ H.D + 2 ≤ veml s

/-- After `nbm`. -/
def JN (H : Hash) (s t : State) : Prop := VS H s t (KM ++ [28]) [] (X7 H s) ∧ t.rd = s.rd ∧ H.D + 2 ≤ veml s

/-- At the end. -/
def JR (H : Hash) (s t : State) : Prop := VS H s t [] [] fun _ _ => True

variable (hH : HashOK T.H) (K : Callees T.H) (hdk : DigOK T.H)

include hH in
theorem cyd_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JM T.H (X7 T.H)))) (.seq clearY (copyDigest T.H)) (Two (VAt T (JC8 T.H))) := by
  obtain ⟨_, hc⟩ := hc.copyDigest
  refine two_post (vtwo (T := T) (H := T.H) [21, 37] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have wDg := hp.wDg
  have hDN := hH.hDN
  have hN := hH.N_le
  refine WP.seq (X86_64.WP.mono_syms (clearY_ok v.L R) fun u1 ⟨L1, k1, hcx1, R1⟩ sy1 => ?_)
  refine X86_64.WP.mono_syms (copyDigest_ok hH L1 R1 (p := s.gpr .rdi) (hw 37 (by decide)) hcx1
    (fun i hi => by
      rw [k1.2.1, hrd]
      exact ⟨⟨s.gpr .rdi, T.H.D⟩, List.mem_append_left _ (by rw [hp.hrd]; simp),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun i hi j hj => Outside.ne L1 (by
      have := hp.outside hp.ddgs hp.dKdg (a := s.gpr .rdi + BitVec.ofNat 64 i)
        (Offset.contains_base _ (by omega_arith) (by omega_arith))
      rwa [k1.2.2, v.wr]) (by unfold oY oRsa; omega_arith))) fun u2 ⟨L2, k2, R2⟩ sy2 =>
    ⟨s, S, ⟨v.next L2 (k2.2.2.trans k1.2.2) R2 hw hx (sy2.trans sy1), k2.2.1.trans (k1.2.1.trans hrd), hok⟩,
      (k2.gpr (by decide)).trans hcx1⟩

include hH in
theorem copyDb_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JC8 T.H))) (copyDb T.H) (Two (VAt T (JM T.H (X7 T.H)))) := by
  obtain ⟨_, hc⟩ := hc.copyDb
  refine two_post (vtwo (T := T) (H := T.H) [23, 24] [.rcx] (fun a => [(.rcx, off (stackArg a 0) oY)])
    (fun a t ⟨s, S, ⟨v, _⟩, hcx⟩ => ⟨s, _, S, v.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.arg0]; exact hcx) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hok⟩, hcx⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  exact X86_64.WP.mono_syms (copyDb_ok v.L R (e := oEm + vlo s) (db := vdb T.H.D s) (hw 23 (by decide)) (hw 24 (by decide)) hcx
    (by unfold vdb; omega_arith) (by unfold vdb veml oEm oY; omega_arith) (by unfold vdb veml; omega_arith)) fun u ⟨L', k', R'⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' hw hx sy, k'.2.1.trans hrd, hok⟩

/-- `shift`'s first slots. -/
theorem shiftPro_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {pos : Nat} (hpos : W 34 = BitVec.ofNat 64 pos) :
    WP isa (.block shiftPro) u fun v => Lay v F S ∧ Keep [.rax] u v ∧
      Rep v.mem F S V (upd (upd (upd W 45 (BitVec.ofNat 64 (pos + 1))) 46 (BitVec.ofNat 64 1)) 44
        (BitVec.ofNat 64 10)) := by
  have G' := L.geo
  have R1 := R.wf G' (k := 45) (by decide) (BitVec.ofNat 64 (pos + 1))
  rw [show off F (8 * 45) = off F sA from rfl] at R1
  have R2 := R1.wf G' (k := 46) (by decide) (BitVec.ofNat 64 1)
  rw [show off F (8 * 46) = off F sD from rfl] at R2
  have R3 := R2.wf G' (k := 44) (by decide) (BitVec.ofNat 64 10)
  rw [show off F (8 * 44) = off F sJ from rfl] at R3
  refine WP.mono (WP.keep [.rax] (Q := fun v => v.mem = ((u.mem.writeW (off F sA) (BitVec.ofNat 64 (pos + 1))).writeW
      (off F sD) (BitVec.ofNat 64 1)).writeW (off F sJ) (BitVec.ofNat 64 10)) ?_ rfl) fun v ⟨hm, hk⟩ =>
    ⟨L.of_rep' R (hm ▸ R3) (by simp [upd]) (hk.gpr (by decide)) hk.2.2, hk, hm ▸ R3⟩
  xrun [shiftPro, ea_sp, L.rsp, L.ld (d := sPos) (by decide), R.rd (d := sPos) 34 rfl (by decide), hpos,
    L.st (d := sA) (by decide), L.st (d := sD) (by decide), L.st (d := sJ) (by decide), ofNat_add_lit]
  rfl

theorem shiftPro_ct : RelCT isa (Two (VAt T (JM T.H (X7 T.H)))) (.block shiftPro) (Two (VAt T (JS T.H 0))) := by
  obtain ⟨_, hc⟩ := vFixed.shiftPro
  refine two_post (vtwo (T := T) (H := T.H) [] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, pos, hpos, h27, h34⟩ := v.W
  have hk2 := S.ps.k2
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  have hp1 : pos + 1 < 2 ^ 64 := by unfold vdb veml at hpos; omega_arith
  exact X86_64.WP.mono_syms (shiftPro_ok v.L R h34) fun u ⟨L', k', R'⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' (km_upd (km_upd (km_upd hw (by decide) _) (by decide) _) (by decide) _)
      ⟨⟨pos, hpos, by simp [upd, h27], by simp [upd, h34]⟩, by simp [upd], by simp [upd], pos + 1, by simp [upd], hp1⟩
      sy, k'.2.1.trans hrd, hok⟩

include hH in
theorem pass_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two fun (p : State × Nat) t => p.2 < 10 ∧ VAt T (JS T.H p.2) p.1 t)
      (.seq (shiftPass T.H) (.block nextPass)) fun _ _ => True := by
  obtain ⟨_, hs⟩ := hc.shiftPass
  obtain ⟨_, hn⟩ := vFixed.nextPass
  refine RelCT.seq (two_post (Ψ := fun p t => VAt T (JS T.H p.2) p.1 t)
    (vtwoX (T := T) (H := T.H) Prod.fst [21, 24] (fun p => [(46, BitVec.ofNat 64 (2 ^ p.2))]) [46] [] (fun _ => [])
      (fun p t ⟨_, s, S, v, _⟩ => ⟨s, S, v.sub (by decide) [] (fun _ hp => by cases hp)
        fun _ _ ⟨_, h46, _⟩ q hq => by rw [List.mem_singleton.mp hq]; exact h46⟩)
      (fun _ => rfl) (fun _ => rfl) (by decide) hs) fun p t ⟨_, s, S, ⟨v, hrd, hok⟩⟩ => ?_)
    (vtwoX (T := T) (H := T.H) Prod.fst [] (fun _ => []) [] [] (fun _ => [])
      (fun p t ⟨s, S, v, _⟩ => ⟨s, S, v.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ _ q hq => by cases hq⟩)
      (fun _ => rfl) (fun _ => rfl) (by decide) hn)
  obtain ⟨V, W, R, hw, hx, h46, h44, x, h45, hxl⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  have hpp : 2 ^ p.2 ≤ 512 := by
    calc 2 ^ p.2 ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_arith)
      _ = 512 := rfl
  exact X86_64.WP.mono_syms (shiftPass_ok hH v.L R h45 h46 (hw 24 (by decide)) hxl Nat.one_le_two_pow
    (by unfold vdb; omega_arith) (by unfold vdb veml oY oRsa; omega_arith)) fun u ⟨L', k', R'⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' hw ⟨hx, h46, h44, x, h45, hxl⟩ sy, k'.2.1.trans hrd, hok⟩

include hH in
theorem pass_wp {a : State} {j : Nat} {t : State} (hj : j < 10) (h : VAt T (JS T.H j) a t) :
    WP isa (.seq (shiftPass T.H) (.block nextPass)) t fun t' =>
      isa.eval .ne t' = some (decide (j + 1 < 10)) ∧ (j + 1 < 10 → VAt T (JS T.H (j + 1)) a t') ∧
      (j + 1 = 10 → VAt T (JM T.H (X7 T.H)) a t') := by
  obtain ⟨s, S, v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, hx, h46, h44, x, h45, hxl⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  have hpp : 2 ^ j ≤ 512 := by
    calc 2 ^ j ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_arith)
      _ = 512 := rfl
  refine WP.seq (X86_64.WP.mono_syms (shiftPass_ok hH v.L R h45 h46 (hw 24 (by decide)) hxl Nat.one_le_two_pow
    (by unfold vdb; omega_arith) (by unfold vdb veml oY oRsa; omega_arith)) fun u ⟨Lu, ku, Ru⟩ syu => ?_)
  refine X86_64.WP.mono_syms (nextPass_ok Lu Ru h45 h46 h44 hxl (by omega_arith) (by omega_arith))
    fun y ⟨Ly, ky, Ry, hzy⟩ syy => ?_
  obtain ⟨pos, hpos, h27, h34⟩ := hx
  have hw' := km_upd (j := 44) (km_upd (j := 46) (km_upd (j := 45) hw (by decide) (BitVec.ofNat 64 (x / 2)))
    (by decide) (BitVec.ofNat 64 (2 * 2 ^ j))) (by decide) (BitVec.ofNat 64 (10 - j - 1))
  have hX : X7 T.H s (shV V (decide (x % 2 = 1)) (2 ^ j) (oY + 8 + T.H.D) (vdb T.H.D s))
      (upd (upd (upd W 45 (BitVec.ofNat 64 (x / 2))) 46 (BitVec.ofNat 64 (2 * 2 ^ j))) 44
        (BitVec.ofNat 64 (10 - j - 1))) := ⟨pos, hpos, by simp [upd, h27], by simp [upd, h34]⟩
  have hwr : y.wr = t.wr := ky.2.2.trans ku.2.2
  have hrd' : y.rd = s.rd := ky.2.1.trans (ku.2.1.trans hrd)
  refine ⟨eval_ne_cnt hj (by rw [hzy]; simp only [Option.some.injEq, decide_eq_decide]; omega_arith), fun _ =>
    ⟨s, S, v.next Ly hwr Ry hw' ⟨hX, by simp [upd, Nat.pow_succ, Nat.mul_comm], by simp only [upd, Nat.reduceEqDiff, ite_true, ite_false]; congr 1,
      x / 2, by simp [upd], by have := Nat.div_le_self x 2; omega_arith⟩ (syy.trans syu), hrd', hok⟩, fun _ =>
    ⟨s, S, v.next Ly hwr Ry hw' hX (syy.trans syu), hrd', hok⟩⟩

include hH in
theorem shift_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JM T.H (X7 T.H)))) (shift T.H) (Two (VAt T (JM T.H (X7 T.H)))) := by
  rw [shift_eq]
  exact RelCT.seq shiftPro_ct ((two_loop (Φ := fun a j t => VAt T (JS T.H j) a t) (fun _ => 10) (pass_ct hH hc)
    fun a j t hj h => pass_wp hH hj h).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, ⟨by decide, h₁⟩, by decide, h₂⟩)
    fun _ _ h => h)

include hH in
theorem verifyNb_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JM T.H (X7 T.H)))) (.block (verifyNb T.H)) (Two (VAt T (JN T.H))) := by
  obtain ⟨_, hc⟩ := hc.verifyNb
  refine two_post (vtwo (T := T) (H := T.H) [24] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hk2 := S.ps.k2
  exact X86_64.WP.mono_syms (verifyNb_ok hH v.L R (db := vdb T.H.D s) (hw 24 (by decide))
    (by unfold vdb veml; omega_arith)) fun u ⟨L', k', R'⟩ sy => ⟨s, S, v.next L' k'.2.2 R' (fun k hk => by
      rcases List.mem_append.mp hk with hk | hk
      · exact km_upd hw (by decide) _ k hk
      · rw [List.mem_singleton.mp hk]; simp [upd, vw, vnb])
      (by obtain ⟨pos, hpos, h27, h34⟩ := hx; exact ⟨pos, hpos, by simp [upd, h27], by simp [upd, h34]⟩) sy,
      k'.2.1.trans hrd, hok⟩

/-- The hash's anchor: the blocks of `M'`. -/
def hashA (H : Hash) (a : State) : HA := ⟨fb a, stackArg a 0, a.wr, vnb H a, a.syms⟩

include hH in
theorem jn_he {a t : State} (h : VAt T (JN T.H) a t) : HE T.H T.dn T.f 1 (hashA T.H a) t := by
  obtain ⟨s, S, v, -, hok⟩ := h
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hk2 := S.pa.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have h1 := Nat.lt_div_mul_add (a := vdb T.H.D a + (7 + T.H.D + T.H.P.L)) (b := T.H.P.B) hB0
  have h2 := Nat.div_mul_le_self (vdb T.H.D a + (7 + T.H.D + T.H.P.L)) T.H.P.B
  have hdb : vdb T.H.D a ≤ 1024 := by unfold vdb veml; omega_arith
  have tb := S.pa.tabs
  refine ⟨⟨S.rest, Nat.succ_pos _, by simp only [hashA, vnb]; rw [Nat.succ_mul]; omega_arith⟩,
    (vs_pub S v).sub (fun p hp => ?_) (fun _ h => h) (fun _ _ ⟨pos, hpos, h27, _⟩ =>
      ⟨vdb T.H.D s - pos - 1 + (8 + T.H.D), h27, ?_⟩), S.syH.tr v.sy⟩
  · simp only [hws, hashA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · simp [pw, KM, vw]
    · simp [pw, KM, vw]
    · rw [← tb.h0]; exact List.mem_map.mpr ⟨8, by decide, rfl⟩
    · rw [← tb.h3]; exact List.mem_map.mpr ⟨9, by decide, rfl⟩
    · rw [← tb.h4]; exact List.mem_map.mpr ⟨10, by decide, rfl⟩
  · simp only [hashA, vnb]; rw [S.vdb] at hpos ⊢; rw [Nat.succ_mul]; omega_arith

include hH K hdk in
theorem mhash_ct (hc : HashChecks T.H.P T.H.D 1) :
    RelCT isa (Two (VAt T (JN T.H))) (ctHash T.f T.H) (Two (VAt T (JT T.H))) := by
  refine two_post (two_map (hashA T.H) (fun a t h => jn_he hH h)
    (ctHash_ct hH K hdk 1 hc (fixedChecks (.inl rfl))))
    fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, pos, hpos, h27, _⟩ := v.W
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have h1 := Nat.lt_div_mul_add (a := vdb T.H.D s + (7 + T.H.D + T.H.P.L)) (b := T.H.P.B) hB0
  have h2 := Nat.div_mul_le_self (vdb T.H.D s + (7 + T.H.D + T.H.P.L)) T.H.P.B
  have hdb : vdb T.H.D s ≤ 1024 := by unfold vdb veml; omega_arith
  exact X86_64.WP.mono_syms (ctHash_gen hH K v.L R h27 (hw 28 (by simp))
    (by unfold vnb; rw [Nat.succ_mul]; omega_arith) (by unfold vnb; rw [Nat.succ_mul]; omega_arith)
    (vs_ht S.ps v hw) hdk) fun u ⟨L', rd', wr', _, V', W', R', _, hW', _⟩ sy =>
    ⟨s, S, ⟨L', wr'.trans v.wr, ⟨V', W', R', fun k hk => (hW' k (km_lt hk) (km_ne hk (by decide))
      (km_ne hk (by decide))).trans (hw k (List.mem_append_left _ hk)), trivial⟩, (fun _ hp => by cases hp),
      sy.trans v.sy⟩, rd'.trans hrd, hok⟩

include hH in
theorem cmpH_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JT T.H))) (cmpH T.H) (Two (VAt T (JR T.H))) := by
  obtain ⟨_, hc⟩ := hc.cmpH
  refine two_post (vtwo (T := T) (H := T.H) [21, 23, 24] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, -, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  exact X86_64.WP.mono_syms (cmpH_ok hH v.L R (e := oEm + vlo s) (db := vdb T.H.D s) (hw 23 (by decide)) (hw 24 (by decide))
    (by unfold vdb veml oEm oRsa; omega_arith)) fun u ⟨k', hm', _⟩ sy =>
    ⟨s, S, (v.keep k' hm' (by decide) (fun _ hp => by cases hp) sy).sub (fun _ hk => by cases hk) []
      (fun _ hp => by cases hp) fun _ _ _ => trivial⟩

end VG.Proof.RsaPss.X86_64.Chk
