module

public import VerifiedGarbage.Proof.RsaPss.X86_64.Params
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignPro
public import VerifiedGarbage.Proof.RsaPss.X86_64.CtBase
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCVerified
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCParams
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCorrect
import VerifiedGarbage.Proof.RsaPss.X86_64.SignFail
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCall
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCFixed
import VerifiedGarbage.Proof.RsaPss.X86_64.SignFixed
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect
import VerifiedGarbage.Proof.RsaPss.SignEncode
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.RsaPss.X86_64.ByIdx

/-! ### `RsaPss.X86_64.SignCtBase`, which only this module used -/

section

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

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable (tsH tsG : List FnTable) (Xs : State → State → Prop)

/-- Word 5 of the table `hash`: the index of its hash function. -/
def idxWord (s : State) : BitVec 64 := s.mem.readW (off (stackArg s 16) 40) 64

/-- The entry state `s` of a run, and the first's, `a`, with the same index
of the hash function of the table `hash` (word 5 of the table, which the
tables of `MdHash` the precondition allows give, and the public data fix). -/
def SSib (a s : State) : Prop := SPre tsH tsG a ∧ (signK tsH tsG).pub a s ∧ SPre tsH tsG s ∧
  idxWord s = idxWord a ∧ Xs a s

/-- A predicate of the state of a run, given its entry state, for every run
whose entry state agrees with `a`. -/
def SAt (J : State → State → Prop) (a t : State) : Prop := ∃ s, SSib tsH tsG Xs a s ∧ J s t

theorem spub_refl (s : State) : (signK tsH tsG).pub s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

variable {tsH tsG Xs}

namespace SSib

variable {a s : State} (h : SSib tsH tsG Xs a s)
include h

theorem gpr {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) : s.gpr r = a.gpr r :=
  (h.2.1.1 r hr).symm

theorem arg {i : Nat} (hi : i < 18) : stackArg s i = stackArg a i := by
  have := congrArg (fun l => l.getD i 0) h.2.1.2.1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some] at this
  exact this.symm

theorem nB : Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
    Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := h.2.1.2.2.1.symm

theorem eB : Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat =
    Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := h.2.1.2.2.2.1.symm

theorem pa : SPre tsH tsG a := h.1
theorem ps : SPre tsH tsG s := h.2.2.1

theorem idxw : idxWord s = idxWord a := h.2.2.2.1

theorem x : Xs a s := h.2.2.2.2

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
  simpa [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_range (show 0 < (s.gpr .rcx).toNat by omega_using [hk]),
    List.getElem?_range (show 0 < (a.gpr .rcx).toNat by omega_using [hk'])] using this

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
def ssl (s : State) : Nat := (stackArg s 13).toNat

/-- The blocks of the hash of `M'`. -/
def snb (H : Hash) (s : State) : Nat := (8 + H.D + ssl s + H.P.L) / H.P.B + 1

/-- The public words of the frame, by index. -/
def sw (H : Hash) (s : State) (k : Nat) : BitVec 64 :=
  match k with
  | 2 => stackArg s 16
  | 3 => stackArg s 17
  | 47 => idxWord s
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
  | 27 => BitVec.ofNat 64 (8 + H.D + ssl s)
  | 28 => BitVec.ofNat 64 (snb H s)
  | 37 => stackArg s 10
  | 39 => stackArg s 12
  | 40 => stackArg s 13
  | _ => 0

/-- The public words `ks`. -/
def spw (H : Hash) (s : State) (ks : List Nat) : List (Nat × BitVec 64) := ks.map fun k => (k, sw H s k)

namespace SSib

variable {a s : State} (h : SSib tsH tsG Xs a s)
include h

theorem sn0v : sn0v s = sn0v a := by simp only [VG.Proof.RsaPss.X86_64.sn0v, h.n0]
theorem slo : slo s = slo a := by simp only [VG.Proof.RsaPss.X86_64.slo, h.sn0v]
theorem seml : seml s = seml a := by
  simp only [VG.Proof.RsaPss.X86_64.seml, h.slo, h.gpr (r := .rcx) (by decide)]
theorem sdb {D : Nat} : sdb D s = sdb D a := by simp only [VG.Proof.RsaPss.X86_64.sdb, h.seml]
theorem ssl : ssl s = ssl a := by simp only [VG.Proof.RsaPss.X86_64.ssl, h.arg (i := 13) (by decide)]
theorem snb {H : Hash} : snb H s = snb H a := by simp only [VG.Proof.RsaPss.X86_64.snb, h.ssl]

theorem sw {H : Hash} (k : Nat) : sw H s k = sw H a k := by
  unfold VG.Proof.RsaPss.X86_64.sw
  split <;> simp only [h.gpr (r := .rdi) (by decide),
    h.gpr (r := .rdx) (by decide), h.gpr (r := .rcx) (by decide), h.gpr (r := .r8) (by decide),
    h.gpr (r := .r9) (by decide), h.arg (i := 10) (by decide), h.arg (i := 12) (by decide),
    h.arg (i := 13) (by decide), h.arg (i := 14) (by decide), h.arg (i := 15) (by decide), h.slo, h.sdb, h.sn0v,
    h.snb, h.ssl, h.arg (i := 16) (by decide), h.arg (i := 17) (by decide), h.idxw]

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
    rcases hr with rfl | rfl <;> dsimp only <;> omega_arith

end SSib

/-! ## A run's state between pieces -/

/-- A run, with entry state `s`, between two pieces. -/
structure SS (H : Hash) (s t : State) (ks : List Nat) (rs : List (Reg × BitVec 64))
    (X : (Nat → Byte) → (Nat → BitVec 64) → Prop) : Prop where
  L : Lay t (fb s) (stackArg s 14)
  wr : t.wr = frR s :: s.wr
  W : ∃ V W, Rep t.mem (fb s) (stackArg s 14) V W ∧ (∀ k ∈ ks, W k = sw H s k) ∧ X V W
  regs : ∀ p ∈ rs, t.gpr p.1 = p.2
  sy : t.syms = s.syms

variable {H : Hash}

theorem ss_pub {a s t : State} (S : SSib tsH tsG Xs a s) {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) :
    Pub (fb a) (stackArg a 14) a.wr (spw H a ks) rs X t := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  refine ⟨?_, ?_, ⟨V, W, ?_, fun p hp => ?_, hx⟩, h.regs⟩
  · rw [← S.fb, ← S.arg (i := 14) (by decide)]; exact h.L
  · rw [h.wr, S.frR, S.wr]
  · rw [← S.fb, ← S.arg (i := 14) (by decide)]; exact R
  · simp only [spw, List.mem_map] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rw [hw k hk, S.sw]

/-- A piece the analysis checks from `pT 2 ks rgs`. -/
theorem stwo {Φ : State → State → Prop} {c : Prog isa} (ks : List Nat) (rgs : List Reg)
    (rs : State → List (Reg × BitVec 64))
    (hΦ : ∀ a t, Φ a t → ∃ s X, SSib tsH tsG Xs a s ∧ SS H s t ks (rs a) X) (hr : ∀ a, (rs a).map Prod.fst = rgs)
    (hks : ∀ k ∈ ks, k < nW) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (pT 2 ks rgs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_pub 2 ks rgs fb (fun a => stackArg a 14) State.wr (fun a => spw H a ks) rs
    (fun a t h => let ⟨_, X, S, v⟩ := hΦ a t h; ⟨X, ss_pub S v⟩) (fun a t h => let ⟨_, _, S, _⟩ := hΦ a t h; S.rest)
    (fun a => by simp [spw, Function.comp_def]) hr hks h

theorem SS.keep {s t t' : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) {rs' : List Reg} (k : Keep rs' t t')
    (hm : t'.mem = t.mem) (hsp : Reg.rsp ∉ rs') (hrs : ∀ p ∈ rs, p.1 ∉ rs') (hs : t'.syms = t.syms) :
    SS H s t' ks rs X :=
  ⟨h.L.congr (k.gpr hsp) k.2.2 (by rw [hm]), k.2.2.trans h.wr, by rw [hm]; exact h.W,
    fun p hp => (k.gpr (hrs p hp)).trans (h.regs p hp), hs.trans h.sy⟩

theorem SS.next {s t t' : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) (L' : Lay t' (fb s) (stackArg s 14))
    (hwr : t'.wr = t.wr) {V' : Nat → Byte} {W' : Nat → BitVec 64} (R' : Rep t'.mem (fb s) (stackArg s 14) V' W')
    (hw : ∀ k ∈ ks', W' k = sw H s k) (hx : X' V' W') (hs : t'.syms = t.syms) : SS H s t' ks' [] X' :=
  ⟨L', hwr.trans h.wr, ⟨V', W', R', hw, hx⟩, (fun _ hp => by cases hp), hs.trans h.sy⟩

theorem SS.sub {s t : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : SS H s t ks rs X) (hks : ∀ k ∈ ks', k ∈ ks)
    (rs' : List (Reg × BitVec 64)) (hrs : ∀ p ∈ rs', t.gpr p.1 = p.2) (hX : ∀ V W, X V W → X' V W) :
    SS H s t ks' rs' X' := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  exact ⟨h.L, h.wr, ⟨V, W, R, fun k hk => hw k (hks k hk), hX V W hx⟩, hrs, h.sy⟩

end VG.Proof.RsaPss.X86_64

end

end


/-!
# RSASSA-PSS signing on x86-64, around the encoding: constant time, and
`Verified`

The prologue and the check of the modulus' first byte (`spro_ct`), the
index of the table `hash`'s hash function (public: the tables are), `emBits`
and `encode`'s arguments (public: the modulus' length and first byte, and
places), the choice of `encode` by that index and its call (constant time by
its contract: its public data, the places and lengths and the tables' words,
agree), whose result is public (whether the salt fits, `encode_isSome₂`), the
private-key operation's arguments and call (`scall_ct`), and the epilogue,
in two runs whose entry states agree on the public data (`signC_ct`). With
`signC_correct`, `signC` meets the contract (`signC_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (chkContract)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable {tsH tsG : List FnTable} {Xs : State → State → Prop} {H : Hash}

/-! ## The public values -/

/-- `emBits`. -/
def seb (s : State) : Nat := ebV (s.gpr .rcx).toNat (sn0v s)

/-- `emLen`. -/
def sel (s : State) : Nat := Spec.RsaPss.emLength (seb s)

/-- `lo`. -/
def sclo (s : State) : Nat := (s.gpr .rcx).toNat - sel s

/-- Whether the encoding fits, for a digest of `digest_len` bytes. -/
def sfits (s : State) : Prop := (stackArg s 11).toNat + ssl s + 2 ≤ sel s

instance (s : State) : Decidable (sfits s) := inferInstanceAs (Decidable (_ ≤ _))

/-- The index of the table `hash`'s hash function. -/
def sidx (a : State) : Nat := (idxWord a).toNat

theorem SSib.seb {a s : State} (S : SSib tsH tsG Xs a s) : seb s = seb a := by
  simp only [VG.Proof.RsaPss.X86_64.seb, S.sn0v, S.gpr (r := .rcx) (by decide)]

theorem SSib.sel {a s : State} (S : SSib tsH tsG Xs a s) : sel s = sel a := by
  simp only [VG.Proof.RsaPss.X86_64.sel, S.seb]

theorem SSib.sclo {a s : State} (S : SSib tsH tsG Xs a s) : sclo s = sclo a := by
  simp only [VG.Proof.RsaPss.X86_64.sclo, S.sel, S.gpr (r := .rcx) (by decide)]

theorem SSib.sfits {a s : State} (S : SSib tsH tsG Xs a s) : sfits s ↔ sfits a := by
  simp only [VG.Proof.RsaPss.X86_64.sfits, S.sel, S.ssl, S.arg (i := 11) (by decide)]

theorem seb_ok {s : State} (hp : SPre tsH tsG s) :
    sclo s ≤ 1 ∧ 1 ≤ seb s ∧ seb s ≤ Proof.RsaPss.maxEmBits ∧ sel s ≤ 1024 := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hl8 : Nat.log2 (sn0v s) < 8 := RsaPss.log2_lt8 (s.mem (s.gpr .rdx))
  refine ⟨lo_le hl8 (by omega_arith), ?_, ?_, ?_⟩
  · unfold seb ebV; omega_arith
  · unfold seb ebV Proof.RsaPss.maxEmBits; omega_arith
  · unfold sel seb ebV Spec.RsaPss.emLength; omega_arith

/-- `encode`'s result, from whether it fits. -/
theorem rax_of {e : Option (List Byte)} {x : BitVec 64} {c : Bool} {P : List Byte → Prop}
    (h : match e with | some e' => x.setWidth 32 = 1 ∧ P e' | none => x.setWidth 32 = 0) (hc : e.isSome = c) :
    x.setWidth 32 = if c then 1 else 0 := by
  cases e with
  | none => subst hc; exact h
  | some e' => subst hc; exact h.1

variable (f : MdFns) (g : Impl.Mgf1.X86_64.Table.Fns) in
/-- What the tables give the runs whose entry states agree with `a`: the
functions `T` and hash functions `Hs`, `Gs`, the same for every run, that
`encode` for the index of `a`'s table computes with, in constant time. -/
structure SGood (a : State) (T : Tabs) (Hs Gs : Spec.Mgf1.Hash) : Prop where
  sel : ∀ s, (signK tsH tsG).pub a s → SPre tsH tsG s → ESel f g s (sidx a) T Hs Gs
  words : ∀ s, (signK tsH tsG).pub a s → SPre tsH tsG s →
    tabWords s.mem (stackArg s 16) (stackArg s 17) = tabWords a.mem (stackArg a 16) (stackArg a 17)
  ct : ConstantTime isa (encK T Hs Gs).pre (encK T Hs Gs).pub (encode f (ofIdx (sidx a)) g)

/-! ## The pieces -/

/-- After the frame's push. -/
def J0 (s t : State) : Prop := t = allocState frameBytes s

/-- The words the prologue stores. -/
def KS1 : List Nat := [16, 17, 18, 19, 20, 21, 22, 37, 39, 40]

/-- After the prologue: the modulus' first byte, ZF set if it is zero, and
the table `hash` in `r11`. -/
def SJ1 (H : Hash) (s t : State) : Prop :=
  SS H s t KS1 [(.r11, stackArg s 16)] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (sn0v s) ∧ t.zf = some (decide (sn0v s = 0))

/-- And the index in its slot. -/
def SJ2 (H : Hash) (s t : State) : Prop :=
  SS H s t (KS1 ++ [47]) [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (sn0v s) ∧ t.zf = some (decide (sn0v s = 0))

/-- At the end. -/
def SJR (H : Hash) (s t : State) : Prop := SS H s t [] [] fun _ _ => True

theorem spro_ct : RelCT isa (Two (SAt tsH tsG Xs J0)) (.block (signPrologue ++ n0 ++ ([.mov .r11 (.mem (arg 16))] : List Instr)))
    (Two (SAt tsH tsG Xs (SJ1 H))) := by
  obtain ⟨_, hc⟩ := scFixed.pro
  have ar : ∀ (s : State) {r : Reg}, r ≠ .rsp → (allocState frameBytes s).gpr r = s.gpr r := fun s r hr => by
    rw [allocState_gpr']; exact ifn hr _ _
  refine two_post (two_pub0 2 [.rdi, .rsi, .rdx, .rcx, .r8, .r9] fb State.wr
    (fun a => [(.rdi, a.gpr .rdi), (.rsi, a.gpr .rsi), (.rdx, a.gpr .rdx), (.rcx, a.gpr .rcx), (.r8, a.gpr .r8),
      (.r9, a.gpr .r9)])
    (fun a t ⟨s, S, ht⟩ => ⟨by rw [ht, allocState_gpr', ifp rfl, ← S.fb], by rw [ht, ← S.wr, ← S.fb]; rfl,
      fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> rw [ht, ar s (by decide)] <;>
          exact S.gpr (by decide)⟩)
    (fun a t ⟨s, S, _⟩ => S.rest) (fun _ => rfl) hc) fun a t ⟨s, S, ht⟩ => ?_
  subst ht
  have hp := S.ps
  rw [WP.block_append_iff, WP.block_append_iff]
  refine X86_64.WP.mono_syms (signPro_ok hp) fun t1 ⟨k1, L1, R1, f1⟩ sy1 => ?_
  refine X86_64.WP.mono_syms (n0_ok hp L1 R1 (by simp [proW, upd]) k1.2.1 (frame_wrR f1))
    fun t2 ⟨k2, hm2, hax2, hz2⟩ sy2 => ?_
  have hM2 : Frame (wrR s) s.mem t2.mem := hm2 ▸ frame_wrR f1
  have L2 : Lay t2 (fb s) (stackArg s 14) := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  refine X86_64.WP.mono_syms (r11Arg_ok hp L2.rsp (k2.2.1.trans k1.2.1) (argsKept_of hp hM2))
    fun t3 ⟨k3, hm3, h11, hz3⟩ sy3 =>
    ⟨s, S, ⟨⟨L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3]), k3.2.2.trans (k2.2.2.trans k1.2.2),
      ⟨_, _, hm3 ▸ hm2 ▸ R1, fun k hk => ?_, trivial⟩, fun p hp => by rw [List.mem_singleton.mp hp]; exact h11,
      sy3.trans (sy2.trans sy1)⟩, k3.2.1.trans (k2.2.1.trans k1.2.1), hm3 ▸ hM2,
      (k3.gpr (by decide)).trans hax2, hz3.trans hz2⟩⟩
  simp only [KS1, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [proW, upd, sw]

theorem sidx_ct : RelCT isa (Two (SAt tsH tsG Xs (SJ1 H))) (.block idxSlot) (Two (SAt tsH tsG Xs (SJ2 H))) := by
  obtain ⟨_, hc⟩ := scFixed.idx
  refine two_post (stwo (H := H) [] [.r11] (fun a => [(.r11, stackArg a 16)])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (fun _ hk => by cases hk) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.arg (i := 16) (by decide)]; exact h.1.regs _ (List.mem_singleton_self _))
      fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hax, hz⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  refine X86_64.WP.mono_syms (idxSlot_ok S.ps v.L R hrd hM (v.regs _ (List.mem_singleton_self _)))
    fun u ⟨L', k', R', hz', hM'⟩ sy => ⟨s, S, ⟨v.next L' k'.2.2 R' (fun k hk => ?_) trivial sy, k'.2.1.trans hrd, hM',
      (k'.gpr (by decide)).trans hax, hz'.trans hz⟩⟩
  rcases List.mem_append.mp hk with hk | hk
  · have : k ≠ 47 := by simp only [KS1, List.mem_cons, List.not_mem_nil, or_false] at hk; omega_arith
    simp only [upd]; rw [ifn this]; exact hw k hk
  · rw [List.mem_singleton.mp hk]; simp [upd, sw, idxWord]

/-- A refusal: zeros to `out`. -/
theorem sfail_ct {Φ : State → State → Prop}
    (hΦ : ∀ a t, Φ a t → ∃ s X, SSib tsH tsG Xs a s ∧ SS H s t [16, 17] [] X) :
    RelCT isa (Two Φ) signFail (Two (SAt tsH tsG Xs (SJR H))) := by
  obtain ⟨_, hc⟩ := sFixed.fail
  refine two_post (stwo (H := H) [16, 17] [] (fun _ => []) hΦ (fun _ => rfl) (by decide) hc)
    fun a t h => ?_
  obtain ⟨s, X, S, v⟩ := hΦ a t h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have hout : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) ∈ t.wr := by
    rw [v.wr, hp.hwr, ← hp.hsi]; simp
  have hO : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint (stkR s) := by rw [← hp.hsi]; exact hp.dKo.symm
  exact X86_64.WP.mono_syms (signFail_ok v.L R (out := s.gpr .rdi) (k := (s.gpr .rcx).toNat) (hw 16 (by decide))
    (by rw [hw 17 (by decide)]; show s.gpr .rcx = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_arith) hk2
    hout (by rw [← hp.hsi]; exact hp.wO)
    ((by rw [← hp.hsi]; exact hp.dOs : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint
      ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩).sub_right (Region.sub_prefix (by have := hp.hsl; unfold oRsa; omega_arith)))
    (hO.sub_right (frame_sub s))) fun u ⟨L', k', R', _⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' (fun _ h => by cases h) trivial sy⟩

/-- Before the call. -/
def SJP (H : Hash) (s t : State) : Prop :=
  SS H s t [] [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    (∀ i < 14, word t.mem (fb s) (8 * i) = pArg s i) ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rcx ∧
    t.gpr .rdx = s.gpr .rdx ∧ t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9

/-- The words the private-key operation's arguments read. -/
def KSP : List Nat := [16, 17, 18, 19, 20, 22]

/-- Before `encode`. -/
def CJE (H : Hash) (s t : State) : Prop :=
  SS H s t KSP [] (fun _ W => W 0 = off (stackArg s 14) oEnc ∧ W 1 = stackArg s 15 - BitVec.ofNat 64 (oEnc / 8) ∧
      W 2 = stackArg s 16 ∧ W 3 = stackArg s 17) ∧
    t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧ sn0v s ≠ 0 ∧
    t.gpr .rdi = off (stackArg s 14) (oEm + sclo s) ∧ t.gpr .rsi = BitVec.ofNat 64 (sel s) ∧
    t.gpr .rdx = stackArg s 10 ∧ t.gpr .rcx = stackArg s 12 ∧ t.gpr .r8 = stackArg s 13 ∧
    t.gpr .r9 = BitVec.ofNat 64 (seb s) ∧ t.gpr .r11 = idxWord s

/-- After `encode`. -/
def CJC (H : Hash) (s t : State) : Prop :=
  SS H s t KSP [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    (t.gpr .rax).setWidth 32 = if decide (sfits s) then 1 else 0

/-- After the test. -/
def CJT (H : Hash) (s t : State) : Prop :=
  SS H s t KSP [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    t.zf = some (!decide (sfits s))

theorem cprep_ct :
    RelCT isa (Two fun a t => SAt tsH tsG Xs (SJ2 H) a t ∧ isa.eval .e t = some false)
      (.block (emBitsB ++ encArgs ++ idxLoad)) (Two (SAt tsH tsG Xs (CJE H))) := by
  obtain ⟨_, hc⟩ := scFixed.prep
  refine two_post (stwo (H := H) [17, 21, 22, 37, 39, 40, 47] [.rax] (fun a => [(.rax, BitVec.ofNat 64 (sn0v a))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.sn0v]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, he⟩ => ?_
  obtain ⟨v, hrd, hM, hax, hz⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have h0 : sn0v s ≠ 0 := fun h0 => by
    have : isa.eval .e t = some true := by rw [show isa.eval .e t = t.zf from rfl, hz, h0]; rfl
    rw [this] at he; cases he
  have eA : emBitsB ++ encArgs ++ idxLoad = emBitsB ++ (encA1 ++ encA2 ++ encA3) ++ (encA4 ++ idxLoad) := by
    simp only [encArgs_eq, List.append_assoc]
  rw [eA, WP.block_append_iff]
  refine X86_64.WP.mono_syms (WP.keepIn (by decide) (by exact Nat.zero_le 16)
    (encPrep_ok v.L R (hw 17 (by decide)) (hw 22 (by decide)) (hw 37 (by decide)) (hw 39 (by decide))
      (hw 40 (by decide)) (by omega_arith) hk2 (x := sn0v s) (BitVec.isLt _) h0 hax))
    fun u ⟨⟨L', k', R', di, si, dx, cx, r8, r9⟩, f⟩ sy => ?_
  have hM' := frame_keep hp v.wr v.L.rsp hM f
  rw [WP.block_append_iff]
  refine X86_64.WP.mono_syms (WP.keepIn (by decide) (by exact Nat.zero_le 16)
    (encA4_ok hp L' R' (k'.2.1.trans hrd) (argsKept_of hp hM'))) fun u2 ⟨⟨L2, k2, R2⟩, f2⟩ sy2 => ?_
  have hM2 := frame_keep hp (k'.2.2.trans v.wr) L'.rsp hM' f2
  refine X86_64.WP.mono_syms (idxLoad_ok L2 R2) fun u3 ⟨k3, hm3, h113⟩ sy3 => ?_
  have L3 : Lay u3 (fb s) (stackArg s 14) := L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
  have g : ∀ r, r ∉ [Reg.rax, .r11] → u3.gpr r = u.gpr r := fun r hr => by
    rw [k3.gpr (fun h => hr (by simp at h ⊢; exact .inr h)), k2.gpr (fun h => hr (by simp at h ⊢; exact .inl h))]
  refine ⟨s, S, ⟨v.next L3 (k3.2.2.trans (k2.2.2.trans k'.2.2)) (hm3 ▸ R2) (fun k hk => ?_)
      ⟨by simp [upd], by simp [upd], by simp [upd], by simp [upd]⟩ (sy3.trans (sy2.trans sy)),
    k3.2.1.trans (k2.2.1.trans (k'.2.1.trans hrd)), hm3 ▸ hM2, h0, (g _ (by decide)).trans di,
    (g _ (by decide)).trans si, (g _ (by decide)).trans dx, (g _ (by decide)).trans cx, (g _ (by decide)).trans r8,
    (g _ (by decide)).trans r9, ?_⟩⟩
  · simp only [KSP, List.mem_cons, List.not_mem_nil, or_false] at hk
    have hk' : k ∈ KS1 ++ [47] := by simp only [KS1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; omega_arith
    simp only [upd]
    rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith),
      ifn (by omega_arith), ifn (by omega_arith)]
    exact hw k hk'
  · rw [h113]; simp only [upd]
    rw [ifn (by decide), ifn (by decide), ifn (by decide), ifn (by decide), ifn (by decide), ifn (by decide),
      ifn (by decide)]
    exact hw 47 (by decide)

/-- `encode`'s arguments, from the state before the call. -/
theorem encAt_of {f : MdFns} {g : Impl.Mgf1.X86_64.Table.Fns} {s t : State} (hp : SPre tsH tsG s) (h : CJE H s t)
    {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash} (E : ESel f g s i T Hs Gs) : EncAt T s t (sclo s) (seb s) (sel s) := by
  obtain ⟨v, hrd, hM, -, di, si, dx, cx, r8, r9, -⟩ := h
  obtain ⟨V, W, R, -, x0, x1, x2, x3⟩ := v.W
  obtain ⟨lo, e1, e2, -⟩ := seb_ok hp
  exact ⟨v.L.rsp, hrd, v.wr, hM, v.sy, (R.fr 0 (by decide)).trans x0, (R.fr 1 (by decide)).trans x1,
    (R.fr 2 (by decide)).trans x2, (R.fr 3 (by decide)).trans x3, di, si, dx, cx, r8, r9, lo, e1, e2, rfl, E.hD, E.tabs⟩

/-- The tables' words, at the call, as on entry. -/
theorem tabWords_call {s t : State} (hp : SPre tsH tsG s) (hM : Frame (wrR s) s.mem t.mem) (hsp : t.gpr .rsp = fb s) :
    tabWords t.callEntry.mem (stackArg s 16) (stackArg s 17) = tabWords s.mem (stackArg s 16) (stackArg s 17) := by
  have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have fSE : Frame (wrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret8_sub s⟩)
  simp only [tabWords, tab_read hp fSE (.inl rfl) (by decide : 0 + 8 ≤ 56), tab_read hp fSE (.inl rfl) (by decide : 24 + 8 ≤ 56),
    tab_read hp fSE (.inl rfl) (by decide : 32 + 8 ≤ 56), tab_read hp fSE (.inr rfl) (by decide : 0 + 8 ≤ 56),
    tab_read hp fSE (.inr rfl) (by decide : 8 + 8 ≤ 56), tab_read hp fSE (.inr rfl) (by decide : 16 + 8 ≤ 56),
    tab_read hp fSE (.inr rfl) (by decide : 48 + 8 ≤ 56)]

variable {f : MdFns} {g : Impl.Mgf1.X86_64.Table.Fns}
  (hsel : ∀ a, SPre tsH tsG a → ∃ T Hs Gs, SGood (tsH := tsH) (tsG := tsG) f g a T Hs Gs)
  (hspE : ∀ i ∈ idxs, SpSafe (encode f (ofIdx i) g))
  (hdE : ∀ i ∈ idxs, (encode f (ofIdx i) g).x86_64Depth ≤ encStack)

include hsel hspE hdE in
/-- The call of `encode` for the index `j`. -/
theorem ecall_ct {j : Nat} (hj : j ∈ idxs) :
    RelCT isa (Two fun a t => SAt tsH tsG Xs (CJE H) a t ∧ sidx a = j) (.call (encName j) (encode f (ofIdx j) g))
      (Two (SAt tsH tsG Xs (CJC H))) := by
  have g' : ∀ (t : State) (rd wr : List Region) {r : Reg}, r ≠ .rsp →
      (t.callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun t rd wr r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine two_post ?_ fun a t ⟨⟨s, S, h⟩, hja⟩ => ?_
  · refine (RelCT.exists_ (P := fun (x : Tabs × Spec.Mgf1.Hash × Spec.Mgf1.Hash) t₁ t₂ => ∃ a,
        (SAt tsH tsG Xs (CJE H) a t₁ ∧ sidx a = j) ∧ (SAt tsH tsG Xs (CJE H) a t₂ ∧ sidx a = j) ∧
        SGood (tsH := tsH) (tsG := tsG) f g a x.1 x.2.1 x.2.2 ∧ SPre tsH tsG a) fun x => ?_).mono
      (fun t₁ t₂ ⟨a, h₁, h₂⟩ => by
        have hpa : SPre tsH tsG a := h₁.1.choose_spec.1.1
        obtain ⟨T, Hs, Gs, G⟩ := hsel a hpa
        exact ⟨(T, Hs, Gs), a, h₁, h₂, G, hpa⟩) fun _ _ h => h
    by_cases hx : ∃ a, sidx a = j ∧ SGood (tsH := tsH) (tsG := tsG) f g a x.1 x.2.1 x.2.2 ∧ SPre tsH tsG a
    · obtain ⟨a₀, hj₀, G₀, hpa₀⟩ := hx
      have E₀ := G₀.sel a₀ (spub_refl tsH tsG a₀) hpa₀
      rw [hj₀] at E₀
      have hct := G₀.ct
      rw [hj₀] at hct
      refine RelCT.callEx (k := encK x.1 x.2.1 x.2.2) E₀.ok hct
        fun t₁ t₂ ⟨a, ⟨⟨s₁, S₁, h₁⟩, hj₁⟩, ⟨⟨s₂, S₂, h₂⟩, _⟩, G, hpa⟩ => ?_
      have p₁ := S₁.ps; have p₂ := S₂.ps
      have E₁ := G.sel s₁ S₁.2.1 S₁.2.2.1
      have E₂ := G.sel s₂ S₂.2.1 S₂.2.2.1
      have A₁ := encAt_of p₁ h₁ E₁
      have A₂ := encAt_of p₂ h₂ E₂
      obtain ⟨lo₁, -, -, l₁⟩ := seb_ok p₁
      obtain ⟨lo₂, -, -, l₂⟩ := seb_ok p₂
      obtain ⟨c₁, w₁⟩ := enc_covers (T := x.1) p₁ A₁.rd A₁.wr lo₁ l₁ A₁.hD
      obtain ⟨c₂, w₂⟩ := enc_covers (T := x.1) p₂ A₂.rd A₂.wr lo₂ l₂ A₂.hD
      refine ⟨_, _, _, _, enc_pre (Hs := x.2.1) (Gs := x.2.2) p₁ A₁, enc_pre (Hs := x.2.1) (Gs := x.2.2) p₂ A₂,
        ⟨fun r hr => ?_, ?_, ?_⟩, c₁, w₁, c₂, w₂, by rw [A₁.sp, A₂.sp, S₁.fb, S₂.fb]⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [g' _ _ _ (by decide), g' _ _ _ (by decide), A₁.di, A₂.di, S₁.arg (i := 14) (by decide),
            S₂.arg (i := 14) (by decide), S₁.sclo, S₂.sclo]
        · rw [g' _ _ _ (by decide), g' _ _ _ (by decide), A₁.si, A₂.si, S₁.sel, S₂.sel]
        · rw [g' _ _ _ (by decide), g' _ _ _ (by decide), A₁.dx, A₂.dx, S₁.arg (i := 10) (by decide),
            S₂.arg (i := 10) (by decide)]
        · rw [g' _ _ _ (by decide), g' _ _ _ (by decide), A₁.cx, A₂.cx, S₁.arg (i := 12) (by decide),
            S₂.arg (i := 12) (by decide)]
        · rw [g' _ _ _ (by decide), g' _ _ _ (by decide), A₁.r8, A₂.r8, S₁.arg (i := 13) (by decide),
            S₂.arg (i := 13) (by decide)]
        · rw [g' _ _ _ (by decide), g' _ _ _ (by decide), A₁.r9, A₂.r9, S₁.seb, S₂.seb]
        · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, A₁.sp,
            A₂.sp, S₁.fb, S₂.fb]
      · rw [stackArgs_four, stackArgs_four, stackArg_call p₁ A₁.sp _ _ (i := 0) (by decide),
          stackArg_call p₂ A₂.sp _ _ (i := 0) (by decide), stackArg_call p₁ A₁.sp _ _ (i := 1) (by decide),
          stackArg_call p₂ A₂.sp _ _ (i := 1) (by decide), stackArg_call p₁ A₁.sp _ _ (i := 2) (by decide),
          stackArg_call p₂ A₂.sp _ _ (i := 2) (by decide), stackArg_call p₁ A₁.sp _ _ (i := 3) (by decide),
          stackArg_call p₂ A₂.sp _ _ (i := 3) (by decide), A₁.w0, A₂.w0, A₁.w1, A₂.w1, A₁.w2, A₂.w2, A₁.w3, A₂.w3,
          S₁.arg (i := 14) (by decide), S₂.arg (i := 14) (by decide), S₁.arg (i := 15) (by decide),
          S₂.arg (i := 15) (by decide), S₁.arg (i := 16) (by decide), S₂.arg (i := 16) (by decide),
          S₁.arg (i := 17) (by decide), S₂.arg (i := 17) (by decide)]
      · rw [stackArg_call p₁ A₁.sp _ _ (i := 2) (by decide), stackArg_call p₂ A₂.sp _ _ (i := 2) (by decide),
          stackArg_call p₁ A₁.sp _ _ (i := 3) (by decide), stackArg_call p₂ A₂.sp _ _ (i := 3) (by decide),
          A₁.w2, A₂.w2, A₁.w3, A₂.w3, State.withRegions_mem, State.withRegions_mem, tabWords_call p₁ A₁.M A₁.sp,
          tabWords_call p₂ A₂.M A₂.sp, G.words s₁ S₁.2.1 S₁.2.2.1, G.words s₂ S₂.2.1 S₂.2.2.1]
    · exact RelCT.of_false fun _ _ ⟨a, ⟨_, hj₁⟩, _, G, hpa⟩ => hx ⟨a, hj₁, G, hpa⟩
  · obtain ⟨T, Hs, Gs, G⟩ := hsel a S.1
    have hp := S.ps
    have E := G.sel s S.2.1 S.2.2.1
    rw [hja] at E
    have A := encAt_of hp h E
    obtain ⟨v, hrd, hM, -⟩ := h
    obtain ⟨V, W, R, hw, -⟩ := v.W
    refine WP.mono (enc_call E.ok (hspE j hj) (hdE j hj) hp A R)
      fun u ⟨rd', wr', cs', _, hM', sy', R', hE⟩ => ⟨s, S, v.next (v.L.of_rep' R R' rfl (cs' .rsp (by decide)) wr') wr'
        R' hw trivial (sy'.trans v.sy.symm), rd'.trans hrd, hM', rax_of hE ?_⟩
    rw [RsaPss.encode_isSome₂ Hs Gs (by rw [Bignum.bytesAt_length]; exact E.hD.trans (hp.hdl Hs E.hH)),
      Bignum.bytesAt_length, ← hp.hdl Hs E.hH]
    rfl

include hsel hspE hdE in
/-- The choice of `encode` by the table's index, and its call. -/
theorem echoose_ct : RelCT isa (Two (SAt tsH tsG Xs (CJE H)))
    (byIdx (fun i => .call (encName i) (encode f (ofIdx i) g)) idxs) (Two (SAt tsH tsG Xs (CJC H))) := by
  refine byIdx_ct sidx (fun a t t' ⟨s, S, h⟩ k hm sy => ?_) (fun a t ⟨s, S, h⟩ => ?_) cmpOk_idxs
    (fun j hj => ?_) (fun j hj => ecall_ct hsel hspE hdE hj)
  · obtain ⟨v, hrd, hM, h0, di, si, dx, cx, r8, r9, r11⟩ := h
    have gk : ∀ r, t'.gpr r = t.gpr r := fun r => k.gpr (List.not_mem_nil)
    exact ⟨s, S, v.keep k hm (by simp) (fun _ hp => by cases hp) sy, k.2.1.trans hrd, hm ▸ hM, h0,
      (gk _).trans di, (gk _).trans si, (gk _).trans dx, (gk _).trans cx, (gk _).trans r8, (gk _).trans r9,
      (gk _).trans r11⟩
  · obtain ⟨T, Hs, Gs, G⟩ := hsel a S.1
    refine ⟨(G.sel a (spub_refl tsH tsG a) S.1).mem, ?_⟩
    rw [h.2.2.2.2.2.2.2.2.2.2, S.idxw, sidx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · obtain ⟨_, hc⟩ := scFixed.cmp j hj
    exact stwo (H := H) [] [.r11] (fun a => [(.r11, idxWord a)])
      (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (fun _ hk => by cases hk) _ (fun p hp => by
        rw [List.mem_singleton.mp hp, ← S.idxw]; exact h.2.2.2.2.2.2.2.2.2.2) fun _ _ x => x⟩)
      (fun _ => rfl) (by decide) hc

theorem ctest_ct : RelCT isa (Two (SAt tsH tsG Xs (CJC H))) (.block [.alu32 .test .rax (.reg .rax)])
    (Two (SAt tsH tsG Xs (CJT H))) := by
  obtain ⟨_, hc⟩ := scFixed.test
  refine two_post (stwo (H := H) [] [] (fun _ => [])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hax⟩ := h
  refine X86_64.WP.mono_syms (test32_ok t) fun u ⟨k, hm, hz⟩ sy =>
    ⟨s, S, v.keep k hm (by decide) (fun _ hp => by cases hp) sy, k.2.1.trans hrd, hm ▸ hM, ?_⟩
  rw [hz, hax]
  by_cases hf : sfits s <;> simp [hf]

/-- An input, at the call, as on entry. -/
theorem sentry_bytes {s t : State} (hst : t.gpr .rsp = fb s) (hM : Frame (wrR s) s.mem t.mem)
    {R : Region} (hK : (stkR s).Disjoint R) (hO : (outR s).Disjoint R) (hS : R.Disjoint (scrR s))
    (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.callEntry.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hst]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have fSE : Frame (wrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret8_sub s⟩)
  exact bytesAt_frame fSE (in_apart hK hO hS) hl

theorem pArg_sib {a s : State} (S : SSib tsH tsG Xs a s) {i : Nat} (hi : i < 14) : pArg s i = pArg a i := by
  unfold pArg
  split
  · rw [S.arg (i := 14) (by decide)]
  · rw [S.gpr (r := .rcx) (by decide)]
  · rw [S.arg (i := 14) (by decide)]
  · rw [S.arg (i := 15) (by decide)]
  · exact S.arg (by omega_arith)

/-- The call's public data agree. -/
theorem scall_pub {a s₁ s₂ t₁ t₂ : State} (S₁ : SSib tsH tsG Xs a s₁) (h₁ : SJP H s₁ t₁) (S₂ : SSib tsH tsG Xs a s₂)
    (h₂ : SJP H s₂ t₂) :
    chkContract.pub (t₁.callEntry.withRegions (pRd s₁) (pWr s₁)) (t₂.callEntry.withRegions (pRd s₂) (pWr s₂)) := by
  obtain ⟨v₁, -, hM₁, ha₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ := h₁
  obtain ⟨v₂, -, hM₂, ha₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ := h₂
  have p₁ := S₁.ps
  have p₂ := S₂.ps
  have hE₁ : ∀ i < 14, stackArg (t₁.callEntry.withRegions (pRd s₁) (pWr s₁)) i = pArg a i :=
    fun i hi => ((stackArg_call p₁ v₁.L.rsp _ _ (by omega_using [hi])).trans (ha₁ i hi)).trans (pArg_sib S₁ hi)
  have hE₂ : ∀ i < 14, stackArg (t₂.callEntry.withRegions (pRd s₂) (pWr s₂)) i = pArg a i :=
    fun i hi => ((stackArg_call p₂ v₂.L.rsp _ _ (by omega_using [hi])).trans (ha₂ i hi)).trans (pArg_sib S₂ hi)
  have bn : ∀ {s t : State}, SSib tsH tsG Xs a s → t.gpr .rsp = fb s → Frame (wrR s) s.mem t.mem →
      Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
        Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := fun {s t} S hst hM => by
    have hp := S.ps
    rw [← S.nB]
    exact sentry_bytes (R := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) hst hM hp.dKn hp.dOn hp.dns
      (by have := hp.wN; dsimp only; omega_arith)
  have be : ∀ {s t : State}, SSib tsH tsG Xs a s → t.gpr .rsp = fb s → Frame (wrR s) s.mem t.mem →
      Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .r8) (s.gpr .r9).toNat =
        Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := fun {s t} S hst hM => by
    have hp := S.ps
    rw [← S.eB]
    exact sentry_bytes (R := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩) hst hM hp.dKe hp.dOe hp.des
      (by have := hp.wE; dsimp only; omega_arith)
  have g : ∀ (t : State) (rd wr : List Region) {r : Reg}, r ≠ .rsp → (t.callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun t rd wr r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine ⟨fun r hr => ?_, List.map_congr_left fun i hi => ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), di₁, di₂, S₁.gpr (r := .rdi) (by decide),
        S₂.gpr (r := .rdi) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), si₁, si₂, S₁.gpr (r := .rcx) (by decide),
        S₂.gpr (r := .rcx) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, S₁.gpr (r := .rdx) (by decide),
        S₂.gpr (r := .rdx) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), cx₁, cx₂, S₁.gpr (r := .rcx) (by decide),
        S₂.gpr (r := .rcx) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), r8₁, r8₂, S₁.gpr (r := .r8) (by decide),
        S₂.gpr (r := .r8) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), r9₁, r9₂, S₁.gpr (r := .r9) (by decide),
        S₂.gpr (r := .r9) (by decide)]
    · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, v₁.L.rsp,
        v₂.L.rsp, S₁.fb, S₂.fb]
  · have hi := List.mem_range.mp hi
    rw [hE₁ i hi, hE₂ i hi]
  · rw [State.withRegions_mem, State.withRegions_mem, g _ _ _ (by decide), g _ _ _ (by decide),
      g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, cx₁, cx₂, bn S₁ v₁.L.rsp hM₁, bn S₂ v₂.L.rsp hM₂]
  · rw [State.withRegions_mem, State.withRegions_mem, g _ _ _ (by decide), g _ _ _ (by decide),
      g _ _ _ (by decide), g _ _ _ (by decide), r8₁, r8₂, r9₁, r9₂, be S₁ v₁.L.rsp hM₁, be S₂ v₂.L.rsp hM₂]

variable {privN : String} {privC : Prog isa}
  (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
  (hct : ConstantTime isa chkContract.pre chkContract.pub privC) (hspC : SpSafe privC)
  (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes)

theorem srestore_ct : RelCT isa (Two (SAt tsH tsG Xs (SJR H))) (.block restoreRegs) fun _ _ => True := by
  obtain ⟨_, hc⟩ := sFixed.restore
  exact stwo (H := H) [] [] (fun _ => []) (fun a t ⟨s, S, v⟩ => ⟨s, _, S, v⟩) (fun _ => rfl) (by decide) hc

include hsel hspE hdE in
/-- The body of `signC`'s frame, with the private-key operation's arguments
`args` and call constant time from the test of `encode`'s result on. -/
theorem scbodyWith_ct (H : Hash) {args : List Instr}
    (hpriv : RelCT isa (Two fun a t => SAt tsH tsG Xs (CJT H) a t ∧ isa.eval .e t = some false)
      (.seq (.block args) (.call privN privC)) (Two (SAt tsH tsG Xs (SJR H)))) :
    RelCT isa (Two (SAt tsH tsG Xs J0)) (signCBodyWith f g privN privC args) fun _ _ => True := by
  unfold signCBodyWith
  simp only [seqs]
  refine (spro_ct (H := H)).seq (sidx_ct.seq ((two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
      rw [show isa.eval .e t₁ = t₁.zf from rfl, show isa.eval .e t₂ = t₂.zf from rfl, h₁.2.2.2.2, h₂.2.2.2.2,
        S₁.sn0v, S₂.sn0v])
    (sfail_ct (Φ := fun a t => SAt tsH tsG Xs (SJ2 H) a t ∧ isa.eval .e t = some true)
      fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
    (cprep_ct.seq ((echoose_ct hsel hspE hdE).seq (ctest_ct.seq
      (two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
          rw [show isa.eval .e t₁ = t₁.zf from rfl, show isa.eval .e t₂ = t₂.zf from rfl, h₁.2.2.2,
            h₂.2.2.2, decide_eq_decide.mpr ((S₁.sfits).trans S₂.sfits.symm)])
        (sfail_ct (Φ := fun a t => SAt tsH tsG Xs (CJT H) a t ∧ isa.eval .e t = some true)
          fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
        hpriv))))).seq srestore_ct))

end VG.Proof.RsaPss.X86_64
