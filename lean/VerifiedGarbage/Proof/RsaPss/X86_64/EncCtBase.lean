module

public import VerifiedGarbage.Proof.RsaPss.X86_64.EncFrame
public import VerifiedGarbage.Proof.RsaPss.X86_64.CtBase
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

/-!
# EMSA-PSS's encoding on x86-64: two runs

As for signing (`SignCtBase`): each run's entry state `s` agrees with the
first's, `a`, on the public data (`Sib`): the pointers, the lengths and
`emBits`, from which both compute the same public values (`sw`): `DB`'s
place and length, the mask of the top bits, the salt's length and the
hash's blocks. The digest and the salt are secret. A run's state between
two pieces is described by `SS`; both runs then start the next piece's
taint analysis from the same public values (`stwo`). The writable regions
after the frame are `em` and the working space.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Enc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable (G : Spec.Mgf1.Hash)

/-- The entry state `s` of a run, and the first's, `a`. -/
def Sib (a s : State) : Prop := (encK G).pre a ∧ (encK G).pub a s ∧ (encK G).pre s

/-- A predicate of the state of a run, given its entry state, for every run
whose entry state agrees with `a`. -/
def At (J : State → State → Prop) (a t : State) : Prop := ∃ s, Sib G a s ∧ J s t

theorem pub_refl (s : State) : (encK G).pub s s := ⟨fun _ _ => rfl, rfl, rfl⟩

variable {G}

namespace Sib

variable {a s : State} (h : Sib G a s)
include h

theorem gpr {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) : s.gpr r = a.gpr r :=
  (h.2.1.1 r hr).symm

theorem arg0 : stackArg s 0 = stackArg a 0 := h.2.1.2.1.symm
theorem arg1 : stackArg s 1 = stackArg a 1 := h.2.1.2.2.symm

theorem pa : Pre G a := Pre.of G h.1
theorem ps : Pre G s := Pre.of G h.2.2

theorem fb : fb s = fb a := by
  simp only [VG.Proof.RsaPss.X86_64.fb, h.gpr (r := .rsp) (by decide)]

theorem wr : s.wr = a.wr := by
  rw [h.ps.hwr, h.pa.hwr, h.arg0, h.arg1, h.gpr (r := .rdi) (by decide), h.gpr (r := .rsi) (by decide)]

theorem frR : frR s = ⟨VG.Proof.RsaPss.X86_64.fb a, frameBytes⟩ := by
  simp only [VG.Proof.RsaPss.X86_64.frR, h.fb]

end Sib

/-! ## The public values -/

/-- `lo`, always 0. -/
def slo (_s : State) : Nat := 0

/-- `emLen`. -/
def seml (s : State) : Nat := (s.gpr .rsi).toNat

/-- `dbLen`. -/
def sdb (D : Nat) (s : State) : Nat := seml s - D - 1

/-- The salt's length. -/
def ssl (s : State) : Nat := (s.gpr .r8).toNat

/-- The blocks of the hash of `M'`. -/
def snb (H : Hash) (s : State) : Nat := (8 + H.D + ssl s + H.P.L) / H.P.B + 1

/-- The mask of `maskedDB`'s first byte. -/
def smask (s : State) : Byte := (0xFF : Byte) >>> (8 * seml s - (s.gpr .r9).toNat)

/-- The public words of the frame, by index. -/
def sw (H : Hash) (s : State) (k : Nat) : BitVec 64 :=
  match k with
  | 16 => s.gpr .rdi
  | 17 => s.gpr .rsi
  | 21 => stackArg s 0
  | 23 => off (stackArg s 0) (oEm + slo s)
  | 24 => BitVec.ofNat 64 (sdb H.D s)
  | 25 => BitVec.setWidth 64 (smask s)
  | 26 => BitVec.ofNat 64 (slo s)
  | 27 => BitVec.ofNat 64 (8 + H.D + ssl s)
  | 28 => BitVec.ofNat 64 (snb H s)
  | 37 => s.gpr .rdx
  | 39 => s.gpr .rcx
  | 40 => s.gpr .r8
  | _ => 0

/-- The public words `ks`. -/
def spw (H : Hash) (s : State) (ks : List Nat) : List (Nat × BitVec 64) := ks.map fun k => (k, sw H s k)

namespace Sib

variable {a s : State} (h : Sib G a s)
include h

theorem seml : seml s = seml a := by simp only [VG.Proof.RsaPss.X86_64.Enc.seml, h.gpr (r := .rsi) (by decide)]
theorem sdb {D : Nat} : sdb D s = sdb D a := by simp only [VG.Proof.RsaPss.X86_64.Enc.sdb, h.seml]
theorem ssl : ssl s = ssl a := by simp only [VG.Proof.RsaPss.X86_64.Enc.ssl, h.gpr (r := .r8) (by decide)]
theorem snb {H : Hash} : snb H s = snb H a := by simp only [VG.Proof.RsaPss.X86_64.Enc.snb, h.ssl]
theorem smask : smask s = smask a := by
  simp only [VG.Proof.RsaPss.X86_64.Enc.smask, h.seml, h.gpr (r := .r9) (by decide)]

theorem sw {H : Hash} (k : Nat) : sw H s k = sw H a k := by
  unfold VG.Proof.RsaPss.X86_64.Enc.sw
  split <;> simp only [h.gpr (r := .rdi) (by decide), h.gpr (r := .rsi) (by decide), h.gpr (r := .rdx) (by decide),
    h.gpr (r := .rcx) (by decide), h.gpr (r := .r8) (by decide), h.arg0, h.sdb, h.snb, h.ssl, h.smask, slo]

/-- The frame, `em` and the working space are apart. -/
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

end Sib

/-! ## A run's state between pieces -/

/-- A run, with entry state `s`, between two pieces. -/
structure SS (H : Hash) (s t : State) (ks : List Nat) (rs : List (Reg × BitVec 64))
    (X : (Nat → Byte) → (Nat → BitVec 64) → Prop) : Prop where
  L : Lay t (fb s) (stackArg s 0)
  wr : t.wr = frR s :: s.wr
  W : ∃ V W, Rep t.mem (fb s) (stackArg s 0) V W ∧ (∀ k ∈ ks, W k = sw H s k) ∧ X V W
  regs : ∀ p ∈ rs, t.gpr p.1 = p.2

variable {H : Hash}

theorem ss_pub {a s t : State} (S : Sib G a s) {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) :
    Pub (fb a) (stackArg a 0) a.wr (spw H a ks) rs X t := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  refine ⟨?_, ?_, ⟨V, W, ?_, fun p hp => ?_, hx⟩, h.regs⟩
  · rw [← S.fb, ← S.arg0]; exact h.L
  · rw [h.wr, S.frR, S.wr]
  · rw [← S.fb, ← S.arg0]; exact R
  · simp only [spw, List.mem_map] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rw [hw k hk, S.sw]

/-- A piece the analysis checks from `pT 2 ks rgs`. -/
theorem stwo {Φ : State → State → Prop} {c : Prog isa} (ks : List Nat) (rgs : List Reg)
    (rs : State → List (Reg × BitVec 64))
    (hΦ : ∀ a t, Φ a t → ∃ s X, Sib G a s ∧ SS H s t ks (rs a) X) (hr : ∀ a, (rs a).map Prod.fst = rgs)
    (hks : ∀ k ∈ ks, k < nW) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (pT 2 ks rgs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_pub 2 ks rgs fb (fun a => stackArg a 0) State.wr (fun a => spw H a ks) rs
    (fun a t h => let ⟨_, X, S, v⟩ := hΦ a t h; ⟨X, ss_pub S v⟩) (fun a t h => let ⟨_, _, S, _⟩ := hΦ a t h; S.rest)
    (fun a => by simp [spw, Function.comp_def]) hr hks h

theorem SS.keep {s t t' : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) {rs' : List Reg} (k : Keep rs' t t')
    (hm : t'.mem = t.mem) (hsp : Reg.rsp ∉ rs') (hrs : ∀ p ∈ rs, p.1 ∉ rs') : SS H s t' ks rs X :=
  ⟨h.L.congr (k.gpr hsp) k.2.2 (by rw [hm]), k.2.2.trans h.wr, by rw [hm]; exact h.W,
    fun p hp => (k.gpr (hrs p hp)).trans (h.regs p hp)⟩

theorem SS.next {s t t' : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) (L' : Lay t' (fb s) (stackArg s 0))
    (hwr : t'.wr = t.wr) {V' : Nat → Byte} {W' : Nat → BitVec 64} (R' : Rep t'.mem (fb s) (stackArg s 0) V' W')
    (hw : ∀ k ∈ ks', W' k = sw H s k) (hx : X' V' W') : SS H s t' ks' [] X' :=
  ⟨L', hwr.trans h.wr, ⟨V', W', R', hw, hx⟩, fun _ hp => by cases hp⟩

theorem SS.sub {s t : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) (hks : ∀ k ∈ ks', k ∈ ks)
    (rs' : List (Reg × BitVec 64)) (hrs : ∀ p ∈ rs', t.gpr p.1 = p.2) (hX : ∀ V W, X V W → X' V W) :
    SS H s t ks' rs' X' := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  exact ⟨h.L, h.wr, ⟨V, W, R, fun k hk => hw k (hks k hk), hX V W hx⟩, hrs⟩

end VG.Proof.RsaPss.X86_64.Enc
