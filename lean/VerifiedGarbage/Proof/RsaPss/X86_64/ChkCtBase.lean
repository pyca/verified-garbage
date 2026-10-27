module

public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkFrame
public import VerifiedGarbage.Proof.RsaPss.X86_64.CtBase
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

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

variable (G : Spec.Mgf1.Hash)

/-- The entry state `s` of a run, and the first's, `a`: both meet the
precondition, and their public data agree. -/
def VSib (a s : State) : Prop := Pre G a ∧ (chkK G).pub a s ∧ Pre G s

/-- A predicate of the state of a run, given its entry state, for every run
whose entry state agrees with `a`. -/
def VAt (J : State → State → Prop) (a t : State) : Prop := ∃ s, VSib G a s ∧ J s t

theorem vpub_refl (s : State) : (chkK G).pub s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

variable {G}

namespace VSib

variable {a s : State} (h : VSib G a s)
include h

theorem gpr {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) : s.gpr r = a.gpr r :=
  (h.2.1.1 r hr).symm

theorem rsl : s.gpr .r8 = a.gpr .r8 := h.gpr (by decide)
theorem r9 : (s.gpr .r9).setWidth 32 = (a.gpr .r9).setWidth 32 := h.2.1.2.1.symm
theorem arg0 : stackArg s 0 = stackArg a 0 := h.2.1.2.2.1.symm
theorem arg1 : stackArg s 1 = stackArg a 1 := h.2.1.2.2.2.symm

theorem pa : Pre G a := h.1
theorem ps : Pre G s := h.2.2

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

variable {a s : State} (h : VSib G a s)
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
    h.gpr (r := .rdx) (by decide), h.gpr (r := .r8) (by decide), h.r9, h.arg0, h.vlo, h.vdb, h.vnb, h.cmask]

theorem pw {H : Hash} (ks : List Nat) : pw H s ks = pw H a ks := by
  simp only [VG.Proof.RsaPss.X86_64.Chk.pw, h.vw]

/-- The frame and the working space are apart. -/
theorem rest : RestOk 1 (VG.Proof.RsaPss.X86_64.fb a) a.wr := by
  have hp := h.pa
  refine ⟨by rw [hp.hwr]; rfl, ?_, ?_⟩
  · rw [hp.hwr]
    refine List.pairwise_pair.mpr ?_
    exact (hp.dKs.sub_left (frame_sub a))
  · rw [hp.hwr]; intro r hr
    rw [List.mem_singleton.mp hr]
    have := hp.wS; dsimp only; omega

end VSib

/-! ## A run's state between pieces -/

/-- The public words after the checks. -/
def K5 : List Nat := [17, 21, 25, 26, 35, 36, 37, 38]

/-- And with `DB`'s. -/
def KM : List Nat := [17, 21, 23, 24, 25, 26, 35, 36, 37, 38]

theorem km_k5 {k : Nat} (h : k ∈ KM) (h23 : k ≠ 23) (h24 : k ≠ 24) : k ∈ K5 := by
  simp only [KM, K5, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega

theorem km_lt {k : Nat} (h : k ∈ KM) : k < nW := by
  simp only [KM, List.mem_cons, List.not_mem_nil, or_false] at h; unfold nW frameBytes; omega

/-- A run, with entry state `s`, between two pieces: its frame, its public
words `ks` (`vw`), the registers `rs`, and what else is true of its working
space and words (`X`). -/
structure VS (H : Hash) (s t : State) (ks : List Nat) (rs : List (Reg × BitVec 64))
    (X : (Nat → Byte) → (Nat → BitVec 64) → Prop) : Prop where
  L : Lay t (fb s) (stackArg s 0)
  wr : t.wr = frR s :: s.wr
  W : ∃ V W, Rep t.mem (fb s) (stackArg s 0) V W ∧ (∀ k ∈ ks, W k = vw H s k) ∧ X V W
  regs : ∀ p ∈ rs, t.gpr p.1 = p.2

variable {H : Hash}

theorem vs_pub {a s t : State} (S : VSib G a s) {ks : List Nat} {rs : List (Reg × BitVec 64)}
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
    (hΦ : ∀ a t, Φ a t → ∃ s X, VSib G a s ∧ VS H s t ks (rs a) X) (hr : ∀ a, (rs a).map Prod.fst = rgs)
    (hks : ∀ k ∈ ks, k < nW) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (pT 1 ks rgs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_pub 1 ks rgs fb (fun a => stackArg a 0) State.wr (fun a => pw H a ks) rs
    (fun a t h => let ⟨_, X, S, v⟩ := hΦ a t h; ⟨X, vs_pub S v⟩) (fun a t h => let ⟨_, _, S, _⟩ := hΦ a t h; S.rest)
    (fun a => by simp [pw, Function.comp_def]) hr hks h

/-- `VS` after code that keeps the memory and the registers but `rs'`. -/
theorem VS.keep {s t t' : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VS H s t ks rs X) {rs' : List Reg} (k : Keep rs' t t')
    (hm : t'.mem = t.mem) (hsp : Reg.rsp ∉ rs') (hrs : ∀ p ∈ rs, p.1 ∉ rs') : VS H s t' ks rs X :=
  ⟨h.L.congr (k.gpr hsp) k.2.2 (by rw [hm]), k.2.2.trans h.wr, by rw [hm]; exact h.W,
    fun p hp => (k.gpr (hrs p hp)).trans (h.regs p hp)⟩

/-- `VS` after code that keeps the regions and the scratch slot. -/
theorem VS.next {s t t' : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VS H s t ks rs X) (L' : Lay t' (fb s) (stackArg s 0))
    (hwr : t'.wr = t.wr) {V' : Nat → Byte} {W' : Nat → BitVec 64} (R' : Rep t'.mem (fb s) (stackArg s 0) V' W')
    (hw : ∀ k ∈ ks', W' k = vw H s k) (hx : X' V' W') : VS H s t' ks' [] X' :=
  ⟨L', hwr.trans h.wr, ⟨V', W', R', hw, hx⟩, fun _ hp => by cases hp⟩


theorem VS.sub {s t : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VS H s t ks rs X) (hks : ∀ k ∈ ks', k ∈ ks)
    (rs' : List (Reg × BitVec 64)) (hrs : ∀ p ∈ rs', t.gpr p.1 = p.2) (hX : ∀ V W, X V W → X' V W) :
    VS H s t ks' rs' X' := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  exact ⟨h.L, h.wr, ⟨V, W, R, fun k hk => hw k (hks k hk), hX V W hx⟩, hrs⟩

/-- A piece the analysis checks from `pT 1 (ks ++ eks) rgs`: the public
words `ks` of `vw`, and `ex`, of the anchor. -/
theorem vtwoX {α : Type} {Φ : α → State → Prop} {c : Prog isa} (π : α → State) (ks : List Nat)
    (ex : α → List (Nat × BitVec 64)) (eks : List Nat) (rgs : List Reg) (rs : α → List (Reg × BitVec 64))
    (hΦ : ∀ a t, Φ a t → ∃ s, VSib G (π a) s ∧ VS H s t ks (rs a) fun _ W => ∀ p ∈ ex a, W p.1 = p.2)
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
