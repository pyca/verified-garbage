import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBody
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFixed
import VerifiedGarbage.Proof.RsaPss.X86_64.MgfCT

/-!
# RSASSA-PSS verification on x86-64: two runs

Two runs of `verify` from states meeting `verifyK.pre` whose public data
agree (`VSib a s`: each run's entry state `s` agrees with the first's, `a`)
compute the same public values (`vw`): the arguments, the encoding's length,
`DB`'s place and length, the mask of the top bits, the expected salt length
and the hash's blocks. The secret ones (the signature, the digest, and what
the code derives from them, such as the salt's length when any is allowed)
stay out of `vw`. A run's state between two pieces is described by `VS`:
its frame, and its public words, those of `vw`; both runs then start the
next piece's taint analysis from the same public values (`vtwo`).
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable (G : Spec.Mgf1.Hash)

/-- The entry state `s` of a run, and the first's, `a`: both meet the
precondition, and their public data agree. -/
def VSib (a s : State) : Prop := (verifyK G).pre a ∧ (verifyK G).pub a s ∧ (verifyK G).pre s

/-- A predicate of the state of a run, given its entry state, for every run
whose entry state agrees with `a`. -/
def VAt (J : State → State → Prop) (a t : State) : Prop := ∃ s, VSib G a s ∧ J s t

theorem vpub_refl (s : State) : (verifyK G).pub s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable {G}

namespace VSib

variable {a s : State} (h : VSib G a s)
include h

theorem gpr {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) : s.gpr r = a.gpr r :=
  (h.2.1.1 r hr).symm

theorem arg0 : stackArg s 0 = stackArg a 0 := h.2.1.2.1.symm
theorem arg1 : stackArg s 1 = stackArg a 1 := h.2.1.2.2.1.symm
theorem arg2 : (stackArg s 2).setWidth 32 = (stackArg a 2).setWidth 32 := h.2.1.2.2.2.1.symm
theorem arg3 : stackArg s 3 = stackArg a 3 := h.2.1.2.2.2.2.1.symm
theorem arg4 : stackArg s 4 = stackArg a 4 := h.2.1.2.2.2.2.2.1.symm

theorem nB : Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
    Spec.Rsa.bytesAt a.mem (a.gpr .rdi) (a.gpr .rsi).toNat := h.2.1.2.2.2.2.2.2.1.symm

theorem eB : Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
    Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := h.2.1.2.2.2.2.2.2.2.symm

theorem pa : VPre G a := VPre.of G h.1
theorem ps : VPre G s := VPre.of G h.2.2

theorem fb : fb s = fb a := by
  simp only [VG.Proof.RsaPss.X86_64.fb, h.gpr (r := .rsp) (by decide)]

theorem wr : s.wr = a.wr := by rw [h.ps.hwr, h.pa.hwr, h.arg3, h.arg4]

theorem frR : frR s = ⟨VG.Proof.RsaPss.X86_64.fb a, frameBytes⟩ := by
  simp only [VG.Proof.RsaPss.X86_64.frR, h.fb]

theorem n0 : s.mem (s.gpr .rdi) = a.mem (a.gpr .rdi) := by
  have := congrArg (fun l => l.getD 0 0) h.nB
  have hk := h.ps.k1
  have hk' := h.pa.k1
  simpa [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_range (show 0 < (s.gpr .rsi).toNat by omega),
    List.getElem?_range (show 0 < (a.gpr .rsi).toNat by omega)] using this

end VSib

/-! ## The public values -/

/-- The modulus' first byte. -/
def n0v (s : State) : Nat := (s.mem (s.gpr .rdi)).toNat

/-- `lo`: 1 if the modulus' first byte is 1 (`EM` one byte shorter). -/
def vlo (s : State) : Nat := loV (n0v s)

/-- `emLen`. -/
def veml (s : State) : Nat := (s.gpr .rsi).toNat - vlo s

/-- `dbLen`. -/
def vdb (D : Nat) (s : State) : Nat := veml s - D - 1

/-- The blocks of the hash of `M'`. -/
def vnb (H : Hash) (s : State) : Nat := (vdb H.D s + (7 + H.D + H.P.L)) / H.P.B + 1

/-- The expected salt length's register, 0 if any. -/
def vrdx (s : State) : BitVec 64 := if (stackArg s 2).setWidth 32 = 0 then stackArg s 1 else 0

/-- The public words of the frame, by index. -/
def vw (H : Hash) (s : State) (k : Nat) : BitVec 64 :=
  match k with
  | 17 => s.gpr .rsi
  | 18 => s.gpr .rdi
  | 19 => s.gpr .rdx
  | 20 => s.gpr .rcx
  | 21 => stackArg s 3
  | 22 => stackArg s 4
  | 23 => off (stackArg s 3) (oEm + vlo s)
  | 24 => BitVec.ofNat 64 (vdb H.D s)
  | 25 => maskV (n0v s)
  | 26 => BitVec.ofNat 64 (vlo s)
  | 28 => BitVec.ofNat 64 (vnb H s)
  | 35 => if (stackArg s 2).setWidth 32 = 0 then 0 else 1
  | 36 => stackArg s 1
  | 37 => s.gpr .r8
  | 38 => s.gpr .r9
  | _ => 0

/-- The public words `ks`. -/
def pw (H : Hash) (s : State) (ks : List Nat) : List (Nat × BitVec 64) := ks.map fun k => (k, vw H s k)

namespace VSib

variable {a s : State} (h : VSib G a s)
include h

theorem n0v : n0v s = n0v a := by simp only [VG.Proof.RsaPss.X86_64.n0v, h.n0]
theorem vlo : vlo s = vlo a := by simp only [VG.Proof.RsaPss.X86_64.vlo, h.n0v]
theorem veml : veml s = veml a := by
  simp only [VG.Proof.RsaPss.X86_64.veml, h.vlo, h.gpr (r := .rsi) (by decide)]
theorem vdb {D : Nat} : vdb D s = vdb D a := by simp only [VG.Proof.RsaPss.X86_64.vdb, h.veml]
theorem vnb {H : Hash} : vnb H s = vnb H a := by simp only [VG.Proof.RsaPss.X86_64.vnb, h.vdb]
theorem vrdx : vrdx s = vrdx a := by simp only [VG.Proof.RsaPss.X86_64.vrdx, h.arg2, h.arg1]

theorem vw {H : Hash} (k : Nat) : vw H s k = vw H a k := by
  unfold VG.Proof.RsaPss.X86_64.vw
  split <;> simp only [h.gpr (r := .rsi) (by decide), h.gpr (r := .rdi) (by decide),
    h.gpr (r := .rdx) (by decide), h.gpr (r := .rcx) (by decide), h.gpr (r := .r8) (by decide),
    h.gpr (r := .r9) (by decide), h.arg1, h.arg2, h.arg3, h.arg4, h.vlo, h.vdb, h.n0v, h.vnb]

theorem pw {H : Hash} (ks : List Nat) : pw H s ks = pw H a ks := by
  simp only [VG.Proof.RsaPss.X86_64.pw, h.vw]

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

end VSib

/-! ## A run's state between pieces -/

/-- A run, with entry state `s`, between two pieces: its frame, its public
words `ks` (`vw`), the registers `rs`, and what else is true of its working
space and words (`X`). -/
structure VS (H : Hash) (s t : State) (ks : List Nat) (rs : List (Reg × BitVec 64))
    (X : (Nat → Byte) → (Nat → BitVec 64) → Prop) : Prop where
  L : Lay t (fb s) (stackArg s 3)
  wr : t.wr = frR s :: s.wr
  W : ∃ V W, Rep t.mem (fb s) (stackArg s 3) V W ∧ (∀ k ∈ ks, W k = vw H s k) ∧ X V W
  regs : ∀ p ∈ rs, t.gpr p.1 = p.2

variable {H : Hash}

theorem vs_pub {a s t : State} (S : VSib G a s) {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VS H s t ks rs X) :
    Pub (fb a) (stackArg a 3) a.wr (pw H a ks) rs X t := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  refine ⟨?_, ?_, ⟨V, W, ?_, fun p hp => ?_, hx⟩, h.regs⟩
  · rw [← S.fb, ← S.arg3]; exact h.L
  · rw [h.wr, S.frR, S.wr]
  · rw [← S.fb, ← S.arg3]; exact R
  · simp only [pw, List.mem_map] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rw [hw k hk, S.vw]

/-- A piece the analysis checks from `pT 1 ks rgs`. -/
theorem vtwo {Φ : State → State → Prop} {c : Prog isa} (ks : List Nat) (rgs : List Reg)
    (rs : State → List (Reg × BitVec 64))
    (hΦ : ∀ a t, Φ a t → ∃ s X, VSib G a s ∧ VS H s t ks (rs a) X) (hr : ∀ a, (rs a).map Prod.fst = rgs)
    (hks : ∀ k ∈ ks, k < nW) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (pT 1 ks rgs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_pub 1 ks rgs fb (fun a => stackArg a 3) State.wr (fun a => pw H a ks) rs
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
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VS H s t ks rs X) (L' : Lay t' (fb s) (stackArg s 3))
    (hwr : t'.wr = t.wr) {V' : Nat → Byte} {W' : Nat → BitVec 64} (R' : Rep t'.mem (fb s) (stackArg s 3) V' W')
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
  two_pub 1 (ks ++ eks) rgs (fun a => fb (π a)) (fun a => stackArg (π a) 3) (fun a => (π a).wr)
    (fun a => pw H (π a) ks ++ ex a) rs
    (fun a t h => by
      obtain ⟨s, S, v⟩ := hΦ a t h
      obtain ⟨L, w, ⟨V, W, R, hw, hx⟩, rg⟩ := vs_pub S v
      exact ⟨fun _ _ => True, L, w, ⟨V, W, R, fun p hp => (List.mem_append.mp hp).elim (hw p) (hx p), trivial⟩, rg⟩)
    (fun a t h => let ⟨_, S, _⟩ := hΦ a t h; S.rest)
    (fun a => by simp [pw, Function.comp_def, he a]) hr hks h

theorem maskV_byte {x : Nat} (hx : x < 256) : maskV x = BitVec.setWidth 64 ((maskV x).setWidth 8) := by
  have hv : (maskV x).toNat < 2 ^ 8 := by
    unfold maskV
    split
    · decide
    · have hl : Nat.log2 x < 8 := by
        by_cases h0 : x = 0
        · subst h0; decide
        · exact (Nat.log2_lt h0).mpr hx
      have : 2 ^ Nat.log2 x ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
      rw [BitVec.toNat_ofNat]
      have : 2 ^ Nat.log2 x - 1 < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt this]
      omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (by omega)]

theorem fnz_lt {f : Nat → Byte} : ∀ {j i : Nat}, fnz f j = some i → i < j
  | 0, _, h => by simp [fnz] at h
  | j + 1, i, h => by
    simp only [fnz] at h
    split at h
    · rename_i k hk
      cases h; exact Nat.lt_succ_of_lt (fnz_lt hk)
    · split at h
      · cases h
      · cases h; exact Nat.lt_succ_self _

theorem fnz_getD_lt {f : Nat → Byte} {j : Nat} (hj : 1 ≤ j) : (fnz f j).getD 0 < j := by
  cases h : fnz f j with
  | none => simp only [Option.getD_none]; omega
  | some i => exact fnz_lt h

end VG.Proof.RsaPss.X86_64
