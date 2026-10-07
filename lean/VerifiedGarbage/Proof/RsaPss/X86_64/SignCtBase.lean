import VerifiedGarbage.Proof.RsaPss.X86_64.SignVerified
import VerifiedGarbage.Proof.RsaPss.X86_64.SignFixed
import VerifiedGarbage.Proof.RsaPss.X86_64.MgfCT

/-!
# RSASSA-PSS signing on x86-64: two runs

As for verification (`VerifyCtBase`): each run's entry state `s` agrees with
the first's, `a`, on the public data (`SSib`), from which both compute the
same public values (`sw`): the arguments, the encoding's length, `DB`'s
place and length, the mask of the top bits, the salt's length and the hash's
blocks. The digest, the salt and the private key are secret. A run's state
between two pieces is described by `SS`; both runs then start the next
piece's taint analysis from the same public values (`stwo`). The writable
regions after the frame are `out` and the working space.
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable (G : Spec.Mgf1.Hash)

/-- The entry state `s` of a run, and the first's, `a`. -/
def SSib (a s : State) : Prop := (signK G).pre a ∧ (signK G).pub a s ∧ (signK G).pre s

/-- A predicate of the state of a run, given its entry state, for every run
whose entry state agrees with `a`. -/
def SAt (J : State → State → Prop) (a t : State) : Prop := ∃ s, SSib G a s ∧ J s t

theorem spub_refl (s : State) : (signK G).pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

variable {G}

namespace SSib

variable {a s : State} (h : SSib G a s)
include h

theorem gpr {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) : s.gpr r = a.gpr r :=
  (h.2.1.1 r hr).symm

theorem arg {i : Nat} (hi : i < 15) : stackArg s i = stackArg a i := by
  have := congrArg (fun l => l.getD i 0) h.2.1.2.1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some] at this
  exact this.symm

theorem nB : Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
    Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := h.2.1.2.2.1.symm

theorem eB : Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat =
    Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := h.2.1.2.2.2.symm

theorem pa : SPre G a := SPre.of G h.1
theorem ps : SPre G s := SPre.of G h.2.2

theorem fb : fb s = fb a := by
  simp only [VG.Proof.RsaPss.X86_64.fb, h.gpr (r := .rsp) (by decide)]

theorem wr : s.wr = a.wr := by
  rw [h.ps.hwr, h.pa.hwr, h.arg (i := 13) (by decide), h.arg (i := 14) (by decide), h.gpr (r := .rdi) (by decide),
    h.gpr (r := .rsi) (by decide)]

theorem frR : frR s = ⟨VG.Proof.RsaPss.X86_64.fb a, frameBytes⟩ := by
  simp only [VG.Proof.RsaPss.X86_64.frR, h.fb]

theorem n0 : s.mem (s.gpr .rdx) = a.mem (a.gpr .rdx) := by
  have := congrArg (fun l => l.getD 0 0) h.nB
  have hk := h.ps.k1
  have hk' := h.pa.k1
  simpa [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_range (show 0 < (s.gpr .rcx).toNat by omega),
    List.getElem?_range (show 0 < (a.gpr .rcx).toNat by omega)] using this

end SSib

/-! ## The public values -/

/-- The modulus' first byte. -/
def sn0v (s : State) : Nat := (s.mem (s.gpr .rdx)).toNat

/-- `lo`. -/
def slo (s : State) : Nat := loV (sn0v s)

/-- `emLen`. -/
def seml (s : State) : Nat := (s.gpr .rcx).toNat - slo s

/-- `dbLen`. -/
def sdb (D : Nat) (s : State) : Nat := seml s - D - 1

/-- The salt's length. -/
def ssl (s : State) : Nat := (stackArg s 12).toNat

/-- The blocks of the hash of `M'`. -/
def snb (H : Hash) (s : State) : Nat := (8 + H.D + ssl s + H.P.L) / H.P.B + 1

/-- The public words of the frame, by index. -/
def sw (H : Hash) (s : State) (k : Nat) : BitVec 64 :=
  match k with
  | 16 => s.gpr .rdi
  | 17 => s.gpr .rcx
  | 18 => s.gpr .rdx
  | 19 => s.gpr .r8
  | 20 => s.gpr .r9
  | 21 => stackArg s 13
  | 22 => stackArg s 14
  | 23 => off (stackArg s 13) (oEm + slo s)
  | 24 => BitVec.ofNat 64 (sdb H.D s)
  | 25 => maskV (sn0v s)
  | 26 => BitVec.ofNat 64 (slo s)
  | 27 => BitVec.ofNat 64 (8 + H.D + ssl s)
  | 28 => BitVec.ofNat 64 (snb H s)
  | 37 => stackArg s 10
  | 39 => stackArg s 11
  | 40 => stackArg s 12
  | _ => 0

/-- The public words `ks`. -/
def spw (H : Hash) (s : State) (ks : List Nat) : List (Nat × BitVec 64) := ks.map fun k => (k, sw H s k)

namespace SSib

variable {a s : State} (h : SSib G a s)
include h

theorem sn0v : sn0v s = sn0v a := by simp only [VG.Proof.RsaPss.X86_64.sn0v, h.n0]
theorem slo : slo s = slo a := by simp only [VG.Proof.RsaPss.X86_64.slo, h.sn0v]
theorem seml : seml s = seml a := by
  simp only [VG.Proof.RsaPss.X86_64.seml, h.slo, h.gpr (r := .rcx) (by decide)]
theorem sdb {D : Nat} : sdb D s = sdb D a := by simp only [VG.Proof.RsaPss.X86_64.sdb, h.seml]
theorem ssl : ssl s = ssl a := by simp only [VG.Proof.RsaPss.X86_64.ssl, h.arg (i := 12) (by decide)]
theorem snb {H : Hash} : snb H s = snb H a := by simp only [VG.Proof.RsaPss.X86_64.snb, h.ssl]

theorem sw {H : Hash} (k : Nat) : sw H s k = sw H a k := by
  unfold VG.Proof.RsaPss.X86_64.sw
  split <;> simp only [h.gpr (r := .rdi) (by decide),
    h.gpr (r := .rdx) (by decide), h.gpr (r := .rcx) (by decide), h.gpr (r := .r8) (by decide),
    h.gpr (r := .r9) (by decide), h.arg (i := 10) (by decide), h.arg (i := 11) (by decide),
    h.arg (i := 12) (by decide), h.arg (i := 13) (by decide), h.arg (i := 14) (by decide), h.slo, h.sdb, h.sn0v,
    h.snb, h.ssl]

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

end SSib

/-! ## A run's state between pieces -/

/-- A run, with entry state `s`, between two pieces. -/
structure SS (H : Hash) (s t : State) (ks : List Nat) (rs : List (Reg × BitVec 64))
    (X : (Nat → Byte) → (Nat → BitVec 64) → Prop) : Prop where
  L : Lay t (fb s) (stackArg s 13)
  wr : t.wr = frR s :: s.wr
  W : ∃ V W, Rep t.mem (fb s) (stackArg s 13) V W ∧ (∀ k ∈ ks, W k = sw H s k) ∧ X V W
  regs : ∀ p ∈ rs, t.gpr p.1 = p.2

variable {H : Hash}

theorem ss_pub {a s t : State} (S : SSib G a s) {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) :
    Pub (fb a) (stackArg a 13) a.wr (spw H a ks) rs X t := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  refine ⟨?_, ?_, ⟨V, W, ?_, fun p hp => ?_, hx⟩, h.regs⟩
  · rw [← S.fb, ← S.arg (i := 13) (by decide)]; exact h.L
  · rw [h.wr, S.frR, S.wr]
  · rw [← S.fb, ← S.arg (i := 13) (by decide)]; exact R
  · simp only [spw, List.mem_map] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rw [hw k hk, S.sw]

/-- A piece the analysis checks from `pT 2 ks rgs`. -/
theorem stwo {Φ : State → State → Prop} {c : Prog isa} (ks : List Nat) (rgs : List Reg)
    (rs : State → List (Reg × BitVec 64))
    (hΦ : ∀ a t, Φ a t → ∃ s X, SSib G a s ∧ SS H s t ks (rs a) X) (hr : ∀ a, (rs a).map Prod.fst = rgs)
    (hks : ∀ k ∈ ks, k < nW) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (pT 2 ks rgs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_pub 2 ks rgs fb (fun a => stackArg a 13) State.wr (fun a => spw H a ks) rs
    (fun a t h => let ⟨_, X, S, v⟩ := hΦ a t h; ⟨X, ss_pub S v⟩) (fun a t h => let ⟨_, _, S, _⟩ := hΦ a t h; S.rest)
    (fun a => by simp [spw, Function.comp_def]) hr hks h

theorem SS.keep {s t t' : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) {rs' : List Reg} (k : Keep rs' t t')
    (hm : t'.mem = t.mem) (hsp : Reg.rsp ∉ rs') (hrs : ∀ p ∈ rs, p.1 ∉ rs') : SS H s t' ks rs X :=
  ⟨h.L.congr (k.gpr hsp) k.2.2 (by rw [hm]), k.2.2.trans h.wr, by rw [hm]; exact h.W,
    fun p hp => (k.gpr (hrs p hp)).trans (h.regs p hp)⟩

theorem SS.next {s t t' : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) (L' : Lay t' (fb s) (stackArg s 13))
    (hwr : t'.wr = t.wr) {V' : Nat → Byte} {W' : Nat → BitVec 64} (R' : Rep t'.mem (fb s) (stackArg s 13) V' W')
    (hw : ∀ k ∈ ks', W' k = sw H s k) (hx : X' V' W') : SS H s t' ks' [] X' :=
  ⟨L', hwr.trans h.wr, ⟨V', W', R', hw, hx⟩, fun _ hp => by cases hp⟩

theorem SS.sub {s t : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) (hks : ∀ k ∈ ks', k ∈ ks)
    (rs' : List (Reg × BitVec 64)) (hrs : ∀ p ∈ rs', t.gpr p.1 = p.2) (hX : ∀ V W, X V W → X' V W) :
    SS H s t ks' rs' X' := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  exact ⟨h.L, h.wr, ⟨V, W, R, fun k hk => hw k (hks k hk), hX V W hx⟩, hrs⟩

theorem slo_le (s : State) : slo s ≤ 1 := by unfold slo loV; split <;> omega

end VG.Proof.RsaPss.X86_64
