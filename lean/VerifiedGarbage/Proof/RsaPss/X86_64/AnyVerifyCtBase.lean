module

public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyVerifyBody
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtBase
public import VerifiedGarbage.Proof.RsaPss.X86_64.MgfCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

/-!
# RSASSA-PSS verification on x86-64: two runs

Two runs of `verify` from states meeting `verifyK.pre` whose public data
agree (`VSibA a s`: each run's entry state `s` agrees with the first's, `a`)
compute the same public values (`vwA`): the arguments, the encoding's length,
`DB`'s place and length, the mask of the top bits, the expected salt length
and the hash's blocks. The secret ones (the signature, the digest, and what
the code derives from them, such as the salt's length when any is allowed)
stay out of `vwA`. A run's state between two pieces is described by `VSA`:
its frame, and its public words, those of `vwA`; both runs then start the
next piece's taint analysis from the same public values (`vtwoA`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable (G : Spec.Mgf1.Hash) (k g : Nat)

/-- The entry state `s` of a run, and the first's, `a`: both meet the
precondition for the digest's hash function `G`, their public data agree,
and the hash functions are the `k`th and the `g`th. -/
def VSibA (a s : State) : Prop :=
  VPreA G a ∧ verifyAnyK.pub a s ∧ VPreA G s ∧ vhsel a = k ∧ vmsel a = g

/-- A predicate of the state of a run, given its entry state, for every run
whose entry state agrees with `a`. -/
def VAtA (J : State → State → Prop) (a t : State) : Prop := ∃ s, VSibA G k g a s ∧ J s t

theorem vpub_reflA (s : State) : verifyAnyK.pub s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable {G k g}

namespace VSibA

variable {a s : State} (h : VSibA G k g a s)
include h

theorem gpr {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) : s.gpr r = a.gpr r :=
  (h.2.1.1 r hr).symm

theorem arg0 : stackArg s 0 = stackArg a 0 := h.2.1.2.1.symm
theorem arg1 : stackArg s 1 = stackArg a 1 := h.2.1.2.2.1.symm
theorem arg2 : (stackArg s 2).setWidth 32 = (stackArg a 2).setWidth 32 := h.2.1.2.2.2.1.symm
theorem arg3 : stackArg s 3 = stackArg a 3 := h.2.1.2.2.2.2.1.symm
theorem arg4 : stackArg s 4 = stackArg a 4 := h.2.1.2.2.2.2.2.1.symm
theorem arg5 : stackArg s 5 = stackArg a 5 := h.2.1.2.2.2.2.2.2.1.symm
theorem arg6 : stackArg s 6 = stackArg a 6 := h.2.1.2.2.2.2.2.2.2.1.symm
theorem arg7 : stackArg s 7 = stackArg a 7 := h.2.1.2.2.2.2.2.2.2.2.1.symm
theorem arg8 : stackArg s 8 = stackArg a 8 := h.2.1.2.2.2.2.2.2.2.2.2.1.symm
theorem arg9 : stackArg s 9 = stackArg a 9 := h.2.1.2.2.2.2.2.2.2.2.2.2.1.symm

theorem nB : Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
    Spec.Rsa.bytesAt a.mem (a.gpr .rdi) (a.gpr .rsi).toNat := h.2.1.2.2.2.2.2.2.2.2.2.2.2.1.symm

theorem eB : Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
    Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := h.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1.symm

theorem preW : Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 6) (stackArg a 7).toNat := h.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.symm

theorem pa : VPreA G a := h.1
theorem ps : VPreA G s := h.2.2.1

theorem hsel_eq : vhsel s = k := by rw [← h.2.2.2.1]; simp only [vhsel, h.arg8]
theorem msel_eq : vmsel s = g := by rw [← h.2.2.2.2]; simp only [vmsel, h.arg9]

theorem fb : fb s = fb a := by
  simp only [VG.Proof.RsaPss.X86_64.fb, h.gpr (r := .rsp) (by decide)]

theorem wr : s.wr = a.wr := by rw [h.ps.hwr, h.pa.hwr, h.arg4, h.arg5]

theorem frR : frR s = ⟨VG.Proof.RsaPss.X86_64.fb a, frameBytes⟩ := by
  simp only [VG.Proof.RsaPss.X86_64.frR, h.fb]

theorem n0 : s.mem (s.gpr .rdi) = a.mem (a.gpr .rdi) := by
  have := congrArg (fun l => l.getD 0 0) h.nB
  have hk := h.ps.k1
  have hk' := h.pa.k1
  simpa [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_range (show 0 < (s.gpr .rsi).toNat by omega),
    List.getElem?_range (show 0 < (a.gpr .rsi).toNat by omega)] using this

end VSibA

/-! ## The public values -/

/-- The expected salt length's register, 0 if any. -/
def vrdxA (s : State) : BitVec 64 := if (stackArg s 2).setWidth 32 = 0 then stackArg s 3 else 0

/-- The public words of the frame, by index. -/
def vwA (H : Hash) (s : State) (k : Nat) : BitVec 64 :=
  match k with
  | 15 => s.gpr .r9
  | 17 => s.gpr .rsi
  | 18 => s.gpr .rdi
  | 19 => s.gpr .rdx
  | 20 => s.gpr .rcx
  | 21 => stackArg s 4
  | 22 => stackArg s 5
  | 23 => off (stackArg s 4) (oEm + vlo s)
  | 24 => BitVec.ofNat 64 (vdb H.D s)
  | 25 => maskV (n0v s)
  | 26 => BitVec.ofNat 64 (vlo s)
  | 28 => BitVec.ofNat 64 (vnb H s)
  | 35 => if (stackArg s 2).setWidth 32 = 0 then 0 else 1
  | 36 => stackArg s 3
  | 37 => s.gpr .r8
  | 38 => stackArg s 0
  | 47 => stackArg s 8
  | 48 => stackArg s 9
  | _ => 0

/-- The public words `ks`. -/
def pwA (H : Hash) (s : State) (ks : List Nat) : List (Nat × BitVec 64) := ks.map fun k => (k, vwA H s k)

namespace VSibA

variable {a s : State} (h : VSibA G k g a s)
include h

theorem n0v : n0v s = n0v a := by simp only [VG.Proof.RsaPss.X86_64.n0v, h.n0]
theorem vlo : vlo s = vlo a := by simp only [VG.Proof.RsaPss.X86_64.vlo, h.n0v]
theorem veml : veml s = veml a := by
  simp only [VG.Proof.RsaPss.X86_64.veml, h.vlo, h.gpr (r := .rsi) (by decide)]
theorem vdb {D : Nat} : vdb D s = vdb D a := by simp only [VG.Proof.RsaPss.X86_64.vdb, h.veml]
theorem vnb {H : Hash} : vnb H s = vnb H a := by simp only [VG.Proof.RsaPss.X86_64.vnb, h.vdb]
theorem vrdxA : vrdxA s = vrdxA a := by simp only [VG.Proof.RsaPss.X86_64.Any.vrdxA, h.arg2, h.arg3]

theorem vwA {H : Hash} (j : Nat) : vwA H s j = vwA H a j := by
  unfold VG.Proof.RsaPss.X86_64.Any.vwA
  split <;> simp only [h.gpr (r := .rsi) (by decide), h.gpr (r := .rdi) (by decide),
    h.gpr (r := .rdx) (by decide), h.gpr (r := .rcx) (by decide), h.gpr (r := .r8) (by decide),
    h.gpr (r := .r9) (by decide), h.arg0, h.arg3, h.arg2, h.arg4, h.arg5, h.arg8, h.arg9, h.vlo, h.vdb, h.n0v,
    h.vnb]

theorem pwA {H : Hash} (ks : List Nat) : pwA H s ks = pwA H a ks := by
  simp only [VG.Proof.RsaPss.X86_64.Any.pwA, h.vwA]

/-- The frame and the working space are apart. -/
theorem rest : RestOk 1 (VG.Proof.RsaPss.X86_64.fb a) a.wr := by
  have hp := h.pa
  refine ⟨by rw [hp.hwr]; rfl, ?_, ?_⟩
  · rw [hp.hwr]
    refine List.pairwise_pair.mpr ?_
    exact (hp.dKs.sub_left (vframe_sub a))
  · rw [hp.hwr]; intro r hr
    rw [List.mem_singleton.mp hr]
    have := hp.wS; dsimp only; omega

end VSibA

/-! ## A run's state between pieces -/

/-- A run, with entry state `s`, between two pieces: its frame, its public
words `ks` (`vwA`), the registers `rs`, and what else is true of its working
space and words (`X`). -/
structure VSA (H : Hash) (s t : State) (ks : List Nat) (rs : List (Reg × BitVec 64))
    (X : (Nat → Byte) → (Nat → BitVec 64) → Prop) : Prop where
  L : Lay t (fb s) (stackArg s 4)
  wr : t.wr = frR s :: s.wr
  W : ∃ V W, Rep t.mem (fb s) (stackArg s 4) V W ∧ (∀ k ∈ ks, W k = vwA H s k) ∧ X V W
  regs : ∀ p ∈ rs, t.gpr p.1 = p.2

variable {H : Hash}

theorem vs_pubA {a s t : State} (S : VSibA G k g a s) {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VSA H s t ks rs X) :
    Pub (fb a) (stackArg a 4) a.wr (pwA H a ks) rs X t := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  refine ⟨?_, ?_, ⟨V, W, ?_, fun p hp => ?_, hx⟩, h.regs⟩
  · rw [← S.fb, ← S.arg4]; exact h.L
  · rw [h.wr, S.frR, S.wr]
  · rw [← S.fb, ← S.arg4]; exact R
  · simp only [pwA, List.mem_map] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rw [hw k hk, S.vwA]

/-- A piece the analysis checks from `pT 1 ks rgs`. -/
theorem vtwoA {Φ : State → State → Prop} {c : Prog isa} (ks : List Nat) (rgs : List Reg)
    (rs : State → List (Reg × BitVec 64))
    (hΦ : ∀ a t, Φ a t → ∃ s X, VSibA G k g a s ∧ VSA H s t ks (rs a) X) (hr : ∀ a, (rs a).map Prod.fst = rgs)
    (hks : ∀ k ∈ ks, k < nW) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (pT 1 ks rgs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_pub 1 ks rgs fb (fun a => stackArg a 4) State.wr (fun a => pwA H a ks) rs
    (fun a t h => let ⟨_, X, S, v⟩ := hΦ a t h; ⟨X, vs_pubA S v⟩) (fun a t h => let ⟨_, _, S, _⟩ := hΦ a t h; S.rest)
    (fun a => by simp [pwA, Function.comp_def]) hr hks h

/-- `VSA` after code that keeps the memory and the registers but `rs'`. -/
theorem VSA.keep {s t t' : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VSA H s t ks rs X) {rs' : List Reg} (k : Keep rs' t t')
    (hm : t'.mem = t.mem) (hsp : Reg.rsp ∉ rs') (hrs : ∀ p ∈ rs, p.1 ∉ rs') : VSA H s t' ks rs X :=
  ⟨h.L.congr (k.gpr hsp) k.2.2 (by rw [hm]), k.2.2.trans h.wr, by rw [hm]; exact h.W,
    fun p hp => (k.gpr (hrs p hp)).trans (h.regs p hp)⟩

/-- `VSA` after code that keeps the regions and the scratch slot. -/
theorem VSA.next {s t t' : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VSA H s t ks rs X) (L' : Lay t' (fb s) (stackArg s 4))
    (hwr : t'.wr = t.wr) {V' : Nat → Byte} {W' : Nat → BitVec 64} (R' : Rep t'.mem (fb s) (stackArg s 4) V' W')
    (hw : ∀ k ∈ ks', W' k = vwA H s k) (hx : X' V' W') : VSA H s t' ks' [] X' :=
  ⟨L', hwr.trans h.wr, ⟨V', W', R', hw, hx⟩, fun _ hp => by cases hp⟩


theorem VSA.sub {s t : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VSA H s t ks rs X) (hks : ∀ k ∈ ks', k ∈ ks)
    (rs' : List (Reg × BitVec 64)) (hrs : ∀ p ∈ rs', t.gpr p.1 = p.2) (hX : ∀ V W, X V W → X' V W) :
    VSA H s t ks' rs' X' := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  exact ⟨h.L, h.wr, ⟨V, W, R, fun k hk => hw k (hks k hk), hX V W hx⟩, hrs⟩

/-- A piece the analysis checks from `pT 1 (ks ++ eks) rgs`: the public
words `ks` of `vwA`, and `ex`, of the anchor. -/
theorem vtwoXA {α : Type} {Φ : α → State → Prop} {c : Prog isa} (π : α → State) (ks : List Nat)
    (ex : α → List (Nat × BitVec 64)) (eks : List Nat) (rgs : List Reg) (rs : α → List (Reg × BitVec 64))
    (hΦ : ∀ a t, Φ a t → ∃ s, VSibA G k g (π a) s ∧ VSA H s t ks (rs a) fun _ W => ∀ p ∈ ex a, W p.1 = p.2)
    (he : ∀ a, (ex a).map Prod.fst = eks) (hr : ∀ a, (rs a).map Prod.fst = rgs)
    (hks : ∀ k ∈ ks ++ eks, k < nW) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (pT 1 (ks ++ eks) rgs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_pub 1 (ks ++ eks) rgs (fun a => fb (π a)) (fun a => stackArg (π a) 4) (fun a => (π a).wr)
    (fun a => pwA H (π a) ks ++ ex a) rs
    (fun a t h => by
      obtain ⟨s, S, v⟩ := hΦ a t h
      obtain ⟨L, w, ⟨V, W, R, hw, hx⟩, rg⟩ := vs_pubA S v
      exact ⟨fun _ _ => True, L, w, ⟨V, W, R, fun p hp => (List.mem_append.mp hp).elim (hw p) (hx p), trivial⟩, rg⟩)
    (fun a t h => let ⟨_, S, _⟩ := hΦ a t h; S.rest)
    (fun a => by simp [pwA, Function.comp_def, he a]) hr hks h

end VG.Proof.RsaPss.X86_64.Any
