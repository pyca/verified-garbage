module

public import VerifiedGarbage.Proof.RsaPss.X86_64.AnySignCorrect
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCtBase
public import VerifiedGarbage.Proof.RsaPss.X86_64.MgfAnyCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

/-!
# RSASSA-PSS signing on x86-64: two runs

As for verification (`VerifyCtBase`): each run's entry state `s` agrees with
the first's, `a`, on the public data (`SSibA`), from which both compute the
same public values (`swA`): the arguments, the encoding's length, `DB`'s
place and length, the mask of the top bits, the salt's length and the hash's
blocks. The digest, the salt and the private key are secret. A run's state
between two pieces is described by `SSA`; both runs then start the next
piece's taint analysis from the same public values (`stwoA`). The writable
regions after the frame are `out` and the working space.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable (G : Spec.Mgf1.Hash) (k g : Nat)

/-- The entry state `s` of a run, and the first's, `a`, whose hash functions
are the `k`th (`G`) and the `g`th. -/
def SSibA (a s : State) : Prop :=
  signAnyK.pre a ∧ signAnyK.pub a s ∧ signAnyK.pre s ∧ hsel a = k ∧ msel a = g ∧ Spec.HashId.mgf1 k = some G

/-- A predicate of the state of a run, given its entry state, for every run
whose entry state agrees with `a`. -/
def SAtA (J : State → State → Prop) (a t : State) : Prop := ∃ s, SSibA G k g a s ∧ J s t

theorem spub_reflA (s : State) : signAnyK.pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

variable {G} {k g}

namespace SSibA

variable {a s : State} (h : SSibA G k g a s)
include h

theorem gpr {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) : s.gpr r = a.gpr r :=
  (h.2.1.1 r hr).symm

theorem arg {i : Nat} (hi : i < 16) : stackArg s i = stackArg a i := by
  have := congrArg (fun l => l.getD i 0) h.2.1.2.1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some] at this
  exact this.symm

theorem nB : Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
    Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := h.2.1.2.2.2.2.1.symm

theorem eB : Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat =
    Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := h.2.1.2.2.2.2.2.symm

theorem hsel_eq : hsel s = k := by
  show (stackArg s 16).toNat = k
  rw [← h.2.1.2.2.1, ← h.2.2.2.1]

theorem msel_eq : msel s = g := by
  show (stackArg s 17).toNat = g
  rw [← h.2.1.2.2.2.1, ← h.2.2.2.2.1]

theorem pa : SPreA G a := SPreA.of G h.1 (by rw [h.2.2.2.1]; exact h.2.2.2.2.2)
theorem ps : SPreA G s := SPreA.of G h.2.2.1 (by rw [h.hsel_eq]; exact h.2.2.2.2.2)

theorem fb : fb s = fb a := by
  simp only [VG.Proof.RsaPss.X86_64.fb, h.gpr (r := .rsp) (by decide)]

theorem wr : s.wr = a.wr := by
  rw [h.ps.hwr, h.pa.hwr, h.arg (i := 14) (by decide), h.arg (i := 15) (by decide), h.gpr (r := .rdi) (by decide),
    h.gpr (r := .rsi) (by decide)]

theorem frR : frR s = ⟨VG.Proof.RsaPss.X86_64.fb a, frameBytes⟩ := by
  simp only [VG.Proof.RsaPss.X86_64.frR, h.fb]

theorem n0 : s.mem (s.gpr .rdx) = a.mem (a.gpr .rdx) := by
  have := congrArg (fun l => l.getD 0 0) h.nB
  have hk := h.ps.k1
  have hk' := h.pa.k1
  simpa [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_range (show 0 < (s.gpr .rcx).toNat by omega),
    List.getElem?_range (show 0 < (a.gpr .rcx).toNat by omega)] using this

end SSibA

/-! ## The public values -/

/-- The salt's length. -/
def sslA (s : State) : Nat := (stackArg s 13).toNat

/-- The blocks of the hash of `M'`. -/
def snbA (H : Hash) (s : State) : Nat := (8 + H.D + sslA s + H.P.L) / H.P.B + 1

/-- The public words of the frame, by index. -/
def swA (H : Hash) (s : State) (k : Nat) : BitVec 64 :=
  match k with
  | 15 => stackArg s 11
  | 16 => s.gpr .rdi
  | 17 => s.gpr .rcx
  | 18 => s.gpr .rdx
  | 19 => s.gpr .r8
  | 20 => s.gpr .r9
  | 21 => stackArg s 14
  | 22 => stackArg s 15
  | 23 => off (stackArg s 14) (oEm + slo s)
  | 24 => BitVec.ofNat 64 (sdb H.D s)
  | 25 => maskV (sn0v s)
  | 26 => BitVec.ofNat 64 (slo s)
  | 27 => BitVec.ofNat 64 (8 + H.D + sslA s)
  | 28 => BitVec.ofNat 64 (snbA H s)
  | 37 => stackArg s 10
  | 39 => stackArg s 12
  | 40 => stackArg s 13
  | 47 => BitVec.ofNat 64 (Any.hsel s)
  | 48 => BitVec.ofNat 64 (Any.msel s)
  | _ => 0

/-- The public words `ks`. -/
def spwA (H : Hash) (s : State) (ks : List Nat) : List (Nat × BitVec 64) := ks.map fun k => (k, swA H s k)

namespace SSibA

variable {a s : State} (h : SSibA G k g a s)
include h

theorem sn0v : sn0v s = sn0v a := by simp only [VG.Proof.RsaPss.X86_64.sn0v, h.n0]
theorem slo : slo s = slo a := by simp only [VG.Proof.RsaPss.X86_64.slo, h.sn0v]
theorem seml : seml s = seml a := by
  simp only [VG.Proof.RsaPss.X86_64.seml, h.slo, h.gpr (r := .rcx) (by decide)]
theorem sdb {D : Nat} : sdb D s = sdb D a := by simp only [VG.Proof.RsaPss.X86_64.sdb, h.seml]
theorem sslA : sslA s = sslA a := by simp only [VG.Proof.RsaPss.X86_64.Any.sslA, h.arg (i := 13) (by decide)]
theorem snbA {H : Hash} : snbA H s = snbA H a := by simp only [VG.Proof.RsaPss.X86_64.Any.snbA, h.sslA]

theorem swA {H : Hash} (k : Nat) : swA H s k = swA H a k := by
  unfold VG.Proof.RsaPss.X86_64.Any.swA
  split <;> simp only [h.gpr (r := .rdi) (by decide),
    h.gpr (r := .rdx) (by decide), h.gpr (r := .rcx) (by decide), h.gpr (r := .r8) (by decide),
    h.gpr (r := .r9) (by decide), h.arg (i := 10) (by decide), h.arg (i := 11) (by decide),
    h.arg (i := 12) (by decide), h.arg (i := 13) (by decide), h.arg (i := 14) (by decide),
    h.arg (i := 15) (by decide), h.slo, h.sdb, h.sn0v, h.snbA, h.sslA, h.hsel_eq, h.msel_eq, h.2.2.2.1, h.2.2.2.2.1]

/-- The frame, `out` and the working space are apart. -/
theorem rest : RestOk 2 (VG.Proof.RsaPss.X86_64.fb a) a.wr := by
  have hp := h.pa
  refine ⟨by rw [hp.hwr]; rfl, ?_, ?_⟩
  · rw [hp.hwr]
    refine List.Pairwise.cons ?_ (List.pairwise_pair.mpr hp.dOs)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dKo.sub_left (frame_sub a)
    · exact hp.dKs.sub_left (frame_sub a)
  · rw [hp.hwr]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have := hp.wO; have := hp.wS
    rcases hr with rfl | rfl <;> dsimp only <;> omega

end SSibA

/-! ## A run's state between pieces -/

/-- A run, with entry state `s`, between two pieces. -/
structure SSA (H : Hash) (s t : State) (ks : List Nat) (rs : List (Reg × BitVec 64))
    (X : (Nat → Byte) → (Nat → BitVec 64) → Prop) : Prop where
  L : Lay t (fb s) (stackArg s 14)
  wr : t.wr = frR s :: s.wr
  W : ∃ V W, Rep t.mem (fb s) (stackArg s 14) V W ∧ (∀ k ∈ ks, W k = swA H s k) ∧ X V W
  regs : ∀ p ∈ rs, t.gpr p.1 = p.2

variable {H : Hash}

theorem ss_pubA {a s t : State} (S : SSibA G k g a s) {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SSA H s t ks rs X) :
    Pub (fb a) (stackArg a 14) a.wr (spwA H a ks) rs X t := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  refine ⟨?_, ?_, ⟨V, W, ?_, fun p hp => ?_, hx⟩, h.regs⟩
  · rw [← S.fb, ← S.arg (i := 14) (by decide)]; exact h.L
  · rw [h.wr, S.frR, S.wr]
  · rw [← S.fb, ← S.arg (i := 14) (by decide)]; exact R
  · simp only [spwA, List.mem_map] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rw [hw k hk, S.swA]

/-- A piece the analysis checks from `pT 2 ks rgs`. -/
theorem stwoA {Φ : State → State → Prop} {c : Prog isa} (ks : List Nat) (rgs : List Reg)
    (rs : State → List (Reg × BitVec 64))
    (hΦ : ∀ a t, Φ a t → ∃ s X, SSibA G k g a s ∧ SSA H s t ks (rs a) X) (hr : ∀ a, (rs a).map Prod.fst = rgs)
    (hks : ∀ k ∈ ks, k < nW) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (pT 2 ks rgs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_pub 2 ks rgs fb (fun a => stackArg a 14) State.wr (fun a => spwA H a ks) rs
    (fun a t h => let ⟨_, X, S, v⟩ := hΦ a t h; ⟨X, ss_pubA S v⟩) (fun a t h => let ⟨_, _, S, _⟩ := hΦ a t h; S.rest)
    (fun a => by simp [spwA, Function.comp_def]) hr hks h

theorem SSA.keep {s t t' : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SSA H s t ks rs X) {rs' : List Reg} (k : Keep rs' t t')
    (hm : t'.mem = t.mem) (hsp : Reg.rsp ∉ rs') (hrs : ∀ p ∈ rs, p.1 ∉ rs') : SSA H s t' ks rs X :=
  ⟨h.L.congr (k.gpr hsp) k.2.2 (by rw [hm]), k.2.2.trans h.wr, by rw [hm]; exact h.W,
    fun p hp => (k.gpr (hrs p hp)).trans (h.regs p hp)⟩

theorem SSA.next {s t t' : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SSA H s t ks rs X) (L' : Lay t' (fb s) (stackArg s 14))
    (hwr : t'.wr = t.wr) {V' : Nat → Byte} {W' : Nat → BitVec 64} (R' : Rep t'.mem (fb s) (stackArg s 14) V' W')
    (hw : ∀ k ∈ ks', W' k = swA H s k) (hx : X' V' W') : SSA H s t' ks' [] X' :=
  ⟨L', hwr.trans h.wr, ⟨V', W', R', hw, hx⟩, fun _ hp => by cases hp⟩

theorem SSA.sub {s t : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SSA H s t ks rs X) (hks : ∀ k ∈ ks', k ∈ ks)
    (rs' : List (Reg × BitVec 64)) (hrs : ∀ p ∈ rs', t.gpr p.1 = p.2) (hX : ∀ V W, X V W → X' V W) :
    SSA H s t ks' rs' X' := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  exact ⟨h.L, h.wr, ⟨V, W, R, fun k hk => hw k (hks k hk), hX V W hx⟩, hrs⟩

theorem slo_le (s : State) : slo s ≤ 1 := by unfold slo loV; split <;> omega

end VG.Proof.RsaPss.X86_64.Any
