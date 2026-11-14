module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.CTBase
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.CTBlocks
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTCalls
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE.Decrypt
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCT
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPCT
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPubCall
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPre
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivArgs
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Correct
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTMgfT
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Unmask
public import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Buf
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Label
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Out
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Scan
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Shift
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Written
import VerifiedGarbage.Proof.RsaPss.PPC64LE.ShiftV
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivCall
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfT
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.ByLen

/-! ### `RsaOaep.PPC64LE.Dc.CTLabel`, which only this module used -/

section

/-!
# RSAES-OAEP decryption on PPC64LE: the shared code's base state

Untrusted: everything here is checked by Lean. The shared code's base state
has the entry's public data (`pubX_bx`); the label's hash is through its table,
in two runs `hashLabelT_ct` (`Proof/RsaOaep/PPC64LE/CTMgfT.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two two_post wp_li wp_addi wp_mov wp_nil)

section
variable {pc : Bool} {s : State} (P : PreD pc s) {m : Mem} (hm : Frame [kD s, scR s] s.mem m) {rc : Nat} (hrc : rc ≤ 2)
include P hm hrc

omit hrc in
theorem pubX_bx {a : State} (p : PubD a s) : PubX a (bx s m rc) :=
  ⟨p.sp, (stackArg_bx P hm rc (by decide)).trans (p.args 13 (by decide))⟩

end

theorem off13 {a s : State} (p : PubD a s) (o : Nat) : off (stackArg a 13) o = off (Sd s) o := by
  show off (stackArg a 13) o = off (stackArg s 13) o
  rw [p.args 13 (by decide)]

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end

/-! ### `RsaOaep.PPC64LE.Dc.CTPriv`, which only this module used -/

section

/-!
# RSAES-OAEP decryption on PPC64LE: the private operation, twice

Untrusted: everything here is checked by Lean. `priv_ct`: two runs of the
private operation from entry states with the same public data leak alike:
its frame's arguments by the taint analysis, and the call of
`vg_rsa_private_checked` by its constant time (`RelCT.callEx`), whose public
data at the call (`priv_pub`) are the entry's: the pointers and lengths, the
modulus and the public exponent. Its result then differs between the runs,
in `r20` (`DX`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two Pins two_post two_alloc)

theorem psa_pub {a s : State} (p : PubD a s) {i : Nat} (hi : i < 12) : psa s i = psa a i := by
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [psa, Sd, p.g .r10 (by decide), p.args _ (by decide : (0 : Nat) < 17),
      p.args _ (by decide : (1 : Nat) < 17), p.args _ (by decide : (2 : Nat) < 17),
      p.args _ (by decide : (3 : Nat) < 17), p.args _ (by decide : (4 : Nat) < 17),
      p.args _ (by decide : (5 : Nat) < 17), p.args _ (by decide : (6 : Nat) < 17),
      p.args _ (by decide : (7 : Nat) < 17), p.args _ (by decide : (8 : Nat) < 17),
      p.args _ (by decide : (13 : Nat) < 17), p.args _ (by decide : (14 : Nat) < 17)]

/-- At the call, from an entry state with `a`'s public data. -/
def APriv (pc : Bool) (a u : State) : Prop := ∃ s, PreD pc s ∧ PubD a s ∧ AtPriv pc s u ∧ XP pc a s

/-- The public data at the call, but `pre`'s leak. -/
theorem priv_facts {pc : Bool} {a s₁ s₂ u₁ u₂ : State} (P₁ : PreD pc s₁) (p₁ : PubD a s₁) (A₁ : AtPriv pc s₁ u₁)
    (P₂ : PreD pc s₂) (p₂ : PubD a s₂) (A₂ : AtPriv pc s₂ u₂) :
    (callE pc s₁ u₁).sp = (callE pc s₂ u₂).sp ∧
      (∀ r ∈ argRegs, (callE pc s₁ u₁).gpr r = (callE pc s₂ u₂).gpr r) ∧
      (∀ i < 12, stackArg (callE pc s₁ u₁) i = stackArg (callE pc s₂ u₂) i) ∧
      Spec.Rsa.bytesAt (callE pc s₁ u₁).mem ((callE pc s₁ u₁).gpr .r5) ((callE pc s₁ u₁).gpr .r6).toNat =
        Spec.Rsa.bytesAt (callE pc s₂ u₂).mem ((callE pc s₂ u₂).gpr .r5) ((callE pc s₂ u₂).gpr .r6).toNat ∧
      Spec.Rsa.bytesAt (callE pc s₁ u₁).mem ((callE pc s₁ u₁).gpr .r7) ((callE pc s₁ u₁).gpr .r8).toNat =
        Spec.Rsa.bytesAt (callE pc s₂ u₂).mem ((callE pc s₂ u₂).gpr .r7) ((callE pc s₂ u₂).gpr .r8).toNat := by
  have m : ∀ {s u : State}, (callE pc s u).mem = u.mem := fun {_ _} => rfl
  have hb := fun {s u : State} (A : AtPriv pc s u) {p : Addr} {len : Nat}
    (hd : (kD s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd hl
  refine ⟨by rw [callE_sp, callE_sp, A₁.sp, A₂.sp, pb, pb, fb, fb, p₁.sp, p₂.sp], fun r hr => ?_,
    fun i hi => by rw [callE_stackArg A₁ (lt_nCall hi), callE_stackArg A₂ (lt_nCall hi), psa_pub p₁ hi,
      psa_pub p₂ hi], ?_, ?_⟩
  · rw [callE_gpr _ _ (fun h => by revert r; decide), callE_gpr _ _ (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.r3, A₂.r3, Sd, Sd, p₁.args 13 (by decide), p₂.args 13 (by decide)]
    · rw [A₁.r4, A₂.r4, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r5, A₂.r5, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r6, A₂.r6, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r7, A₂.r7, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r8, A₂.r8, p₁.g _ (by decide), p₂.g _ (by decide)]
    · rw [A₁.r9, A₂.r9, p₁.args 11 (by decide), p₂.args 11 (by decide)]
    · rw [A₁.r10, A₂.r10, p₁.g _ (by decide), p₂.g _ (by decide)]
  · rw [m, m, callE_gpr _ _ (r := .r5), callE_gpr _ _ (r := .r6), callE_gpr _ _ (r := .r5),
      callE_gpr _ _ (r := .r6), A₁.r5, A₁.r6, A₂.r5, A₂.r6, hb A₁ P₁.kn (by have := P₁.wn; omega_using []),
      hb A₂ P₂.kn (by have := P₂.wn; omega_using []), p₁.n, p₂.n]
  · rw [m, m, callE_gpr _ _ (r := .r7), callE_gpr _ _ (r := .r8), callE_gpr _ _ (r := .r7),
      callE_gpr _ _ (r := .r8), A₁.r7, A₁.r8, A₂.r7, A₂.r8, hb A₁ P₁.ke (by have := P₁.we; omega_using []),
      hb A₂ P₂.ke (by have := P₂.we; omega_using []), p₁.e, p₂.e]

/-- With `pc`, the call's two more stack arguments, `pre` and `pre_len`, are
the anchor's. -/
theorem psa_pubP {a s : State} (x : PubP a s) {i : Nat} (hi : 12 ≤ i) (hi' : i < 14) : psa s i = psa a i := by
  rcases (by omega_using [hi, hi'] : i = 12 ∨ i = 13) with rfl | rfl
  · exact x.1
  · exact x.2.1

/-- With `pc`, what the call may leak of `pre`, as on entry. -/
theorem pre_leak {s u : State} (X : PreXD s) (A : AtPriv true s u) :
    Spec.Rsa.privatePrecomputedLeak (callE true s u).mem (stackArg (callE true s u) 12)
        ((callE true s u).gpr .r6).toNat =
      Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 17) (s.gpr .r7).toNat := by
  have pwl : Spec.Rsa.precomputedWords (s.gpr .r7).toNat ≤ (stackArg s 18).toNat := by
    rw [X.pl]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
  simp only [Spec.Rsa.privatePrecomputedLeak, callE_stackArg A (i := 12) (by decide), psa,
    callE_gpr (pc := true) s u (r := .r6), A.r6]
  congr 1
  have subPre : Region.Sub ⟨stackArg s 17, 8 * Spec.Rsa.precomputedWords (s.gpr .r7).toNat⟩ (preR s) :=
    fun _ hx => by simp only [Region.Contains] at hx ⊢; omega_using [pwl, hx]
  exact VG.Proof.Rsa.PPC64LE.Priv.words_of_frame A.mem (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact X.kP.symm.sub_left subPre) (by have := X.wP; omega_using [pwl, this])

theorem call_ct (pc : Bool) : RelCT isa (Two (APriv pc)) (privCall pc) fun _ _ => True := by
  cases pc with
  | false =>
    refine VG.PPC64LE.RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContract) Rsa.PPC64LE.Priv.code_correct
      Rsa.PPC64LE.Priv.code_ct fun u₁ u₂ ⟨a, h₁, h₂⟩ => ?_
    obtain ⟨s₁, P₁, p₁, A₁, -⟩ := h₁
    obtain ⟨s₂, P₂, p₂, A₂, -⟩ := h₂
    obtain ⟨hsp, hr, ha, hn, he⟩ := priv_facts P₁ p₁ A₁ P₂ p₂ A₂
    exact ⟨callRd false s₁, callWr s₁, callRd false s₂, callWr s₂, Rsa.PPC64LE.Priv.pre_of_preP (preP_at P₁ A₁),
      Rsa.PPC64LE.Priv.pre_of_preP (preP_at P₂ A₂), Rsa.PPC64LE.Priv.pub_of hsp hr ha hn he,
      (call_covers P₁ A₁).1, (call_covers P₁ A₁).2, (call_covers P₂ A₂).1, (call_covers P₂ A₂).2⟩
  | true =>
    refine VG.PPC64LE.RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContractP) Rsa.PPC64LE.Priv.codeP_correct
      Rsa.PPC64LE.Priv.codeP_ct fun u₁ u₂ ⟨a, h₁, h₂⟩ => ?_
    obtain ⟨s₁, P₁, p₁, A₁, x₁⟩ := h₁
    obtain ⟨s₂, P₂, p₂, A₂, x₂⟩ := h₂
    obtain ⟨X₁, q₁⟩ := x₁ rfl
    obtain ⟨X₂, q₂⟩ := x₂ rfl
    obtain ⟨hsp, hr, ha, hn, he⟩ := priv_facts P₁ p₁ A₁ P₂ p₂ A₂
    refine ⟨callRd true s₁, callWr s₁, callRd true s₂, callWr s₂,
      Rsa.PPC64LE.Priv.pre_of_prePX (preP_at P₁ A₁) (preX_at P₁ X₁ A₁),
      Rsa.PPC64LE.Priv.pre_of_prePX (preP_at P₂ A₂) (preX_at P₂ X₂ A₂),
      Rsa.PPC64LE.Priv.pub_ofP hsp hr (fun i hi => ?_) hn he
        (by rw [pre_leak X₁ A₁, pre_leak X₂ A₂, q₁.2.2, q₂.2.2]),
      (call_covers P₁ A₁).1, (call_covers P₁ A₁).2, (call_covers P₂ A₂).1, (call_covers P₂ A₂).2⟩
    by_cases h12 : i < 12
    · exact ha i h12
    · rw [callE_stackArg A₁ hi, callE_stackArg A₂ hi, psa_pubP q₁ (by omega_using [h12]) hi, psa_pubP q₂ (by omega_using [h12]) hi]

/-- After the entry, from an entry state with `a`'s public data. -/
def AEnt (pc : Bool) (a t : State) : Prop := ∃ s, PreD pc s ∧ PubD a s ∧ Entered s t ∧ XP pc a s

theorem aEnt_sp {pc : Bool} {a t : State} (h : AEnt pc a t) : t.sp = fb a :=
  let ⟨_, _, p, E, _⟩ := h; by rw [E.sv.sp, fb, fb, p.sp]

/-- The private operation, from the entry to `DX`. -/
theorem priv_ct (pc : Bool) : RelCT isa (Two (AEnt pc)) (priv pc) fun _ _ => True := by
  unfold priv
  refine RelCT.seq (two_post (Ψ := fun a w => ∃ s, PreD pc s ∧ PubD a s ∧ w.sp = fb s ∧
      WP isa (.block [.lsr .w .r20 .r3 0]) w (AfterPriv s))
    (two_alloc (R := fun _ _ => True) (fun a t₁ t₂ h₁ h₂ => ⟨(aEnt_sp h₁).trans (aEnt_sp h₂).symm, fun _ h => nomatch h⟩) ?_)
    fun a t ⟨s, P, p, E, x⟩ => WP.mono (privF_ok P (fun h => (x h).1) E) fun w h => ⟨s, P, p, h⟩)
    (lsr_taint fun a w₁ w₂ ⟨s₁, _, p₁, e₁, _⟩ ⟨s₂, _, p₂, e₂, _⟩ =>
      ⟨by rw [e₁, e₂, fb, fb, p₁.sp, p₂.sp], fun _ h => nomatch h⟩)
  refine two_seq (Ψ := APriv pc) (privArgs_taint pc fun a u₁ u₂ ⟨t₁, h₁, e₁⟩ ⟨t₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, aEnt_sp h₁, aEnt_sp h₂], fun _ h => nomatch h⟩)
    (fun a u ⟨t, ⟨s, P, p, E, x⟩, e⟩ => by
      subst e; exact WP.mono (privArgsG_ok P E) fun u' A => ⟨s, P, p, A, x⟩)
    (call_ct pc)

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end


/-!
# RSAES-OAEP decryption on PPC64LE: constant time

Untrusted: everything here is checked by Lean. Two runs from entry states
with the anchor's public data leak alike: the code between the calls by the
taint analysis (`Dc/CTBlocks`), the private operation by its constant time
(`priv_ct`), the hash functions' calls through the tables by their
contracts (`hashLabelT_ct`, MGF1's `mgfXorT_ctS`, with each table at the
same address and its functions at the same addresses: `DXT`), the branch on
the label's digest length (`byLen_ct`) and that on the public `k`
(`two_ite`); what each run satisfies between them follows from correctness. The scan's index,
the shift's count and the private operation's result differ between the
runs, but only as data.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Two Pins two_post two_ite two_alloc wp_li wp_addi wp_subi wp_nil
  eval_nonzero)
open VG.Proof.RsaOaep (scan_idx)

/-- `k` passed the check, in terms of the anchor. -/
abbrev HK (D : Nat) (a : State) : Prop := 2 * D + 2 ≤ (a.gpr .r7).toNat

theorem hk_s {D : Nat} {a s : State} (p : PubD a s) (h : HK D a) : 2 * D + 2 ≤ kk s := by
  show 2 * D + 2 ≤ (s.gpr .r7).toNat; rw [p.g .r7 (by decide)]; exact h

/-- `G`'s functions at the anchor's addresses. -/
def SymG (G : Hash) (a s : State) : Prop :=
  s.syms G.initN = a.syms G.initN ∧ s.syms G.updN = a.syms G.updN ∧ s.syms G.finN = a.syms G.finN

/-- Both tables on entry: MGF1's, `G`'s, and the label's hash function's,
`H`'s. -/
def TT (G H : Hash) (f : Fns) (s : State) : Prop :=
  TabS G f 16 (SD s) s (stackArg s 16) ∧ TabS H f 15 (SD s) s (stackArg s 15)

/-- Both tables' functions at the anchor's addresses. -/
def SymGH (G H : Hash) (a s : State) : Prop := SymG G a s ∧ SymG H a s

/-- `DX`, with both tables on entry, their functions at the anchor's
addresses, and the entry's addresses of statics. -/
def DXT (G H : Hash) (f : Fns) (a t : State) : Prop :=
  ∃ pc s m, PreD pc s ∧ TT G H f s ∧ PubD a s ∧ SymGH G H a s ∧ Frame [kD s, scR s] s.mem m ∧
    Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t ∧ t.syms = s.syms

theorem DXT.dx {G H : Hash} {f : Fns} {a t : State} (h : DXT G H f a t) : DX a t :=
  let ⟨_, s, m, P, _, p, _, hm, b, _⟩ := h; ⟨_, s, m, P, p, hm, b⟩

theorem DXT.only {G H : Hash} {f : Fns} {a t t' : State} {rs : List Reg} (h : DXT G H f a t) (o : Only rs t t')
    (hy : t'.syms = t.syms) (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : DXT G H f a t' :=
  let ⟨_, s, m, P, T, p, y, hm, b, sy⟩ := h; ⟨_, s, m, P, T, p, y, hm, b.only (fitsM P) o hrs, hy.trans sy⟩

/-- The base state's precondition, with MGF1's table. -/
def PreXT (G : Hash) (f : Fns) (x : State) : Prop := PreX x ∧ TabS G f 16 SX x (stackArg x 16)

/-- The base state's public data, with MGF1's table's address and `G`'s
functions' addresses. -/
def PubXT (G : Hash) (a x : State) : Prop := PubX a x ∧ stackArg x 16 = stackArg a 16 ∧ SymG G a x

theorem okXT (G : Hash) (f : Fns) : OkS SX (PreXT G f) (PubXT G) := ⟨fun h => h.1, fun p => p.1.1, fun p => p.1.2⟩

theorem tabXT (G : Hash) (f : Fns) : TabA G f 16 SX (PreXT G f) (PubXT G) :=
  ⟨fun h => h.2, fun p => p.2.1, fun p => p.2.2.1, fun p => p.2.2.2.1, fun p => p.2.2.2.2⟩

/-- What the label's hash needs of the base state: the label readable, apart
from what the hash function writes in `scratch` and from the stack. -/
def LabX (H : Hash) (x : State) : Prop :=
  (⟨stackArg x 9, (stackArg x 10).toNat⟩ : Region) ∈ x.rd ∧
    Region.Disjoint ⟨stackArg x 9, (stackArg x 10).toNat⟩ ⟨off (SX x) oSt, H.S⟩ ∧
    Region.Disjoint ⟨stackArg x 9, (stackArg x 10).toNat⟩ ⟨off (SX x) oW, H.W⟩ ∧
    (cR x).Disjoint ⟨stackArg x 9, (stackArg x 10).toNat⟩ ∧ (stackArg x 10).toNat < 2 ^ 64

/-- The base state's precondition, with both tables and the label. -/
def PreXL (G H : Hash) (f : Fns) (x : State) : Prop :=
  PreXT G f x ∧ TabS H f 15 SX x (stackArg x 15) ∧ LabX H x

/-- The base state's public data, with both tables' addresses, their
functions' addresses, and the label. -/
def PubXL (G H : Hash) (a x : State) : Prop :=
  PubXT G a x ∧ stackArg x 15 = stackArg a 15 ∧ SymG H a x ∧ stackArg x 9 = stackArg a 9 ∧
    stackArg x 10 = stackArg a 10

theorem okXL (G H : Hash) (f : Fns) : OkS SX (PreXL G H f) (PubXL G H) :=
  ⟨fun h => h.1.1, fun p => p.1.1.1, fun p => p.1.1.2⟩

theorem tabXL (G H : Hash) (f : Fns) : TabA H f 15 SX (PreXL G H f) (PubXL G H) :=
  ⟨fun h => h.2.1, fun p => p.2.1, fun p => p.2.2.1.1, fun p => p.2.2.1.2.1, fun p => p.2.2.1.2.2⟩

/-- The base state of a run for the label's hash, from the decoding's. -/
theorem DXT.toL {G H : Hash} (hH : HashOK H) {f : Fns} {a t : State} (h : DXT G H f a t) :
    BT SX VX (PreXL G H f) (PubXL G H) a t := by
  obtain ⟨_, s, m, P, T, p, y, hm, b, sy⟩ := h
  have F := hfits hH
  obtain ⟨_, _, _, _, _, _⟩ := offs
  obtain ⟨pX, bX⟩ := toX P hm _ (rcOf_le _) b
  have a16 : stackArg (bx s m (rcOf (privO s))) 16 = stackArg s 16 := stackArg_bx P hm _ (by decide)
  have a15 : stackArg (bx s m (rcOf (privO s))) 15 = stackArg s 15 := stackArg_bx P hm _ (by decide)
  have a9 : stackArg (bx s m (rcOf (privO s))) 9 = stackArg s 9 := stackArg_bx P hm _ (by decide)
  have a10 : stackArg (bx s m (rcOf (privO s))) 10 = stackArg s 10 := stackArg_bx P hm _ (by decide)
  have h13 : SX (bx s m (rcOf (privO s))) = Sd s := stackArg_bx P hm _ (i := 13) (by decide)
  refine ⟨_, ⟨⟨pX, by rw [a16]; exact tabS_to P T.1 hm rfl rfl rfl (by simp only [SC, h13])⟩,
    by rw [a15]; exact tabS_toL P T.2 hm rfl rfl rfl (by simp only [SC, h13]), ?_⟩,
    ⟨⟨pubX_bx P hm p, a16.trans (p.args 16 (by decide)), y.1⟩, a15.trans (p.args 15 (by decide)), y.2,
      a9.trans (p.args 9 (by decide)), a10.trans (p.args 10 (by decide))⟩, bX, sy⟩
  show LabX H (bx s m (rcOf (privO s)))
  unfold LabX
  rw [a9, a10, h13]
  exact ⟨by show lR s ∈ s.rd; rw [P.hrd]; simp, (P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega_arith)),
    (P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega_arith)),
    P.kl.sub_left fun a ha => kR_sub a (cR_sub (withMem s m) a ha), BitVec.isLt _⟩

/-- `DXT` with the check passed. -/
def DK (G H : Hash) (f : Fns) (D : Nat) (a t : State) : Prop := DXT G H f a t ∧ HK D a

/-- MGF1's arguments, from the anchor. -/
def MgfD (G H : Hash) (f : Fns) (src srcLen dst dstLen : Nat) (a t : State) : Prop :=
  DXT G H f a t ∧ t.gpr .r24 = off (stackArg a 13) src ∧ t.gpr .r25 = BitVec.ofNat 64 srcLen ∧
    t.gpr .r26 = off (stackArg a 13) dst ∧ t.gpr .r27 = BitVec.ofNat 64 dstLen

theorem MgfD.toA {G H : Hash} {f : Fns} {src srcLen dst dstLen : Nat} {a t : State}
    (h : MgfD G H f src srcLen dst dstLen a t) : MgfAT SX VX (PreXT G f) (PubXT G) src srcLen dst dstLen a t := by
  obtain ⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, h24, h25, h26, h27⟩ := h
  obtain ⟨pX, bX⟩ := toX P hm _ (rcOf_le _) b
  have a16 : stackArg (bx s m (rcOf (privO s))) 16 = stackArg s 16 := stackArg_bx P hm _ (by decide)
  have h13 : SX (bx s m (rcOf (privO s))) = Sd s := stackArg_bx P hm _ (i := 13) (by decide)
  refine ⟨_, ⟨pX, ?_⟩, ⟨pubX_bx P hm p, a16.trans (p.args 16 (by decide)), y.1⟩, bX, sy, h24, h25, h26, h27⟩
  rw [a16]
  exact tabS_to P T.1 hm rfl rfl rfl (by simp only [SC, h13])

section
variable {G H : Hash} (hG : HashOK G) (cG : HashCT hG) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {f : Fns}

include cG hGh hGl hGv in
/-- `mgfXorT`, with its lengths and offsets the anchor's. -/
theorem mgf_anyD (q : State → Nat × Nat × Nat × Nat) :
    RelCT isa (Two fun a t => MgfD G H f (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2 a t ∧
      MFit (q a).1 (q a).2.1 (q a).2.2.1 (q a).2.2.2) (mgfXorT f 16) fun _ _ => True :=
  (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfAT SX VX (PreXT G f) (PubXT G) x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXorT_ctS (okXT G f) hG cG x.2 hGh hGl hGv (tabXT G f)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨q a, h₁.2⟩, a, h₁.1.toA, h₂.1.toA⟩) fun _ _ h => h

include hGh hGl hGv in
theorem mgf_dx {src srcLen dst dstLen : Nat} (hf : MFit src srcLen dst dstLen) {a t : State}
    (h : MgfD G H f src srcLen dst dstLen a t) : WP isa (mgfXorT f 16) t (DXT G H f a) := by
  obtain ⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, h24, h25, h26, h27⟩ := h
  exact WP.mono (mgfXorT_ok (fitsM P) hG (tabS_wm P T.1 hm) hGh hGl hGv hf b sy (h24.trans (off13 p _)) h25
    (h26.trans (off13 p _)) h27) fun _ h' => ⟨_, s, m, P, T, p, y, hm, h'.1.1, h'.2⟩

end

/-- `k` from the anchor. -/
abbrev kA (a : State) : Nat := (a.gpr .r7).toNat

theorem kA_le {a t : State} (h : DX a t) : kA a ≤ 1024 := by
  obtain ⟨_, s, m, P, p, -, -⟩ := h
  have := P.k2; rw [p.g .r7 (by decide)] at this; exact this

/-- The arguments of MGF1 of `maskedDB` into the seed. -/
theorem seed_wp {G H : Hash} {f : Fns} (hD0 : 0 < H.D) (hD64 : H.D ≤ 64) {a t : State} (h : DK G H f H.D a t) :
    WP isa (.block (seedArgs H)) t fun t' => (MgfD G H f (1 + H.D) (kA a - (H.D + 1)) 1 H.D a t' ∧
      MFit (1 + H.D) (kA a - (H.D + 1)) 1 H.D) ∧ HK H.D a := by
  obtain ⟨hE, -, -, -, -, -⟩ := offs
  have hk := h.2
  have hk2 := kA_le h.1.dx
  have ek : kA a = (a.gpr .r7).toNat := rfl
  obtain ⟨-, r14, r15, -, -, -, -⟩ := h.1.dx.pins
  refine WP.of_syms (wp_addi (h := by omega_using [hD64, hE]) fun t₁ o₁ e₁ => wp_subi (h := by omega_using [hD64]) fun t₂ o₂ e₂ =>
    wp_addi (h := by omega_using [hE]) fun t₃ o₃ e₃ => wp_li (by omega_using [hD64]) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
  have k₄ : Only [.r24, .r25, .r26, .r27] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine ⟨⟨⟨h.1.only k₄ y, ?_, ?_, ?_, ?_⟩, ⟨by omega_using [hD64, hk2], by omega_using [hD64], .inr (by omega_using []), by omega_using [hD0]⟩⟩, hk⟩
  · rw [o₄.get .r24, o₃.get .r24, o₂.get .r24, e₁, r14, hE, Nat.zero_add]
  · rw [o₄.get .r25, o₃.get .r25, e₂, o₁.get .r15, r15, sub_r15 (by omega)]
  · rw [o₄.get .r26, e₃, o₂.get .r14, o₁.get .r14, r14, hE]
  · rw [e₄]

/-- The arguments of MGF1 of the seed into `maskedDB`. -/
theorem db_wp {G H : Hash} {f : Fns} (hD64 : H.D ≤ 64) {a t : State} (h : DK G H f H.D a t) :
    WP isa (.block (dbArgs H)) t fun t' => (MgfD G H f 1 H.D (1 + H.D) (kA a - (H.D + 1)) a t' ∧
      MFit 1 H.D (1 + H.D) (kA a - (H.D + 1))) ∧ HK H.D a := by
  obtain ⟨hE, -, -, -, -, -⟩ := offs
  have hk := h.2
  have hk2 := kA_le h.1.dx
  have ek : kA a = (a.gpr .r7).toNat := rfl
  obtain ⟨-, r14, r15, -, -, -, -⟩ := h.1.dx.pins
  refine WP.of_syms (wp_addi (h := by omega_using [hE]) fun t₁ o₁ e₁ => wp_li (by omega_using [hD64]) fun t₂ o₂ e₂ =>
    wp_addi (h := by omega_using [hD64, hE]) fun t₃ o₃ e₃ => wp_subi (h := by omega_using [hD64]) fun t₄ o₄ e₄ => wp_nil fun y => ?_)
  have k₄ : Only [.r24, .r25, .r26, .r27] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine ⟨⟨⟨h.1.only k₄ y, ?_, ?_, ?_, ?_⟩, ⟨by omega_using [hD64], by omega_using [hD64, hk2], .inl (by omega_using []), by omega⟩⟩, hk⟩
  · rw [o₄.get .r24, o₃.get .r24, o₂.get .r24, e₁, r14, hE]
  · rw [o₄.get .r25, o₃.get .r25, e₂]
  · rw [o₄.get .r26, e₃, o₂.get .r14, o₁.get .r14, r14, hE, Nat.zero_add]
  · rw [e₄, o₃.get .r15, o₂.get .r15, o₁.get .r15, r15, sub_r15 (by omega)]

/-- `DX` from an entry state with `a`'s public data, by the correctness
lemmas' `Base`. -/
theorem dk_wp {G H : Hash} {f : Fns} {D : Nat} {c : Prog isa} {a t : State} (h : DK G H f D a t)
    (hw : ∀ pc s m, PreD pc s → PubD a s → 2 * D + 2 ≤ kk s → Frame [kD s, scR s] s.mem m →
      Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t →
      WP isa c t fun t' => Base (SD s) (VD s (rcOf (privO s))) (withMem s m) t') :
    WP isa c t (DK G H f D a) :=
  let ⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, hk⟩ := h
  WP.mono_syms (hw _ s m P p (hk_s p hk) hm b) fun _ b' y' => ⟨⟨_, s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩

/-- After the scan: the index, below the buffer's size. -/
def DI (G H : Hash) (f : Fns) (D : Nat) (a t : State) : Prop := DK G H f D a t ∧ ∃ idx < 1023, t.gpr .r25 = BitVec.ofNat 64 idx

theorem dk_pins {G H : Hash} {f : Fns} {D : Nat} {α : Type} {Φ : α → State → Prop} {an : α → State}
    (h : ∀ x t, Φ x t → DK G H f D (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ [Reg.r14, .r15, .r16, .r17, .r18, .r19] := by decide) : Pins Φ rs :=
  dx_pins (fun x t hx => (h x t hx).1.dx) rs hrs

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (hG : HashOK G) (cG : HashCT hG) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {f : Fns}

include hH cH cG hGh hGl hGv in
theorem decMain_ct : RelCT isa (Two (DK G H f H.D)) (decMain H f) fun _ _ => True := by
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  unfold decMain
  -- The seed with MGF1 of `maskedDB`.
  let q₁ : State → Nat × Nat × Nat × Nat := fun a => (1 + H.D, kA a - (H.D + 1), 1, H.D)
  refine two_seq (Ψ := fun a t => (MgfD G H f (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2 a t ∧
      MFit (q₁ a).1 (q₁ a).2.1 (q₁ a).2.2.1 (q₁ a).2.2.2) ∧ HK H.D a)
    (seedArgs_taint H (dk_pins (an := id) (fun _ _ h => h) [])) (fun a t h => seed_wp hD0 hD64 h) ?_
  refine two_seq (Ψ := DK G H f H.D) ((mgf_anyD hG cG hGh hGl hGv q₁).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨h, hf⟩, hk⟩ => WP.mono (mgf_dx hG hGh hGl hGv hf h) fun _ h' => ⟨h', hk⟩) ?_
  -- `maskedDB` with MGF1 of the seed.
  let q₂ : State → Nat × Nat × Nat × Nat := fun a => (1, H.D, 1 + H.D, kA a - (H.D + 1))
  refine two_seq (Ψ := fun a t => (MgfD G H f (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2 a t ∧
      MFit (q₂ a).1 (q₂ a).2.1 (q₂ a).2.2.1 (q₂ a).2.2.2) ∧ HK H.D a)
    (dbArgs_taint H (dk_pins (an := id) (fun _ _ h => h) [])) (fun a t h => db_wp hD64 h) ?_
  refine two_seq (Ψ := DK G H f H.D) ((mgf_anyD hG cG hGh hGl hGv q₂).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩)
    fun _ _ h => h) (fun a t ⟨⟨h, hf⟩, hk⟩ => WP.mono (mgf_dx hG hGh hGl hGv hf h) fun _ h' => ⟨h', hk⟩) ?_
  -- `lHash`, and `lHash'` against it.
  refine two_seq (Ψ := DK G H f H.D) ((hashLabelT_ct (vf := VX) (okXL G H f) hH cH (tabXL G H f) (rl := .r18)
      (rn := .r19)
      (L := fun x => stackArg x 9) (N := fun x => (stackArg x 10).toNat) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (fun {x t} _ b => ⟨b.vs .r18 (by decide), by
        rw [b.vs .r19 (by decide)]; show stackArg x 10 = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩)
      (fun _ p => ⟨p.2.2.2.1, by rw [p.2.2.2.2]⟩) (fun P => P.2.2) (fun h => lab2_taint h)
      (fun h => lab3_taint h)).mono
      (fun _ _ ⟨a, h₁, h₂⟩ => ⟨(a, 0), h₁.1.toL hH, h₂.1.toL hH⟩) fun _ _ h => h)
    (fun a t ⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, hk⟩ => WP.mono (hashLabelT_ok P hH (tabS_wmL P T.2 hm) b sy)
      fun t' ⟨⟨b', _⟩, y'⟩ => ⟨⟨_, s, m, P, T, p, y, hm, b', y'⟩, hk⟩) ?_
  refine two_seq (Ψ := DK G H f H.D) (accLh_taint H (dk_pins (an := id) (fun _ _ h => h) [.r14]))
    (fun a t h => dk_wp h fun _ s m P _ hk _ b => WP.mono (accLh_ok P rfl hD0 hD64 hk b) fun _ h' => h'.1) ?_
  -- The scan.
  refine two_seq (Ψ := DI G H f H.D) (scan_taint H (dk_pins (an := id) (fun _ _ h => h) [.r14, .r15]))
    (fun a t ⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, hk⟩ => ?_) ?_
  · have hk' := hk_s p hk
    have hk2 := P.k2
    refine WP.mono_syms (scan_ok P rfl hD64 hk' b) fun t' ⟨b', _, _, _, i'⟩ y' =>
      ⟨⟨⟨_, s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩, ?_⟩
    obtain ⟨idx, he, hi⟩ := scan_idx (fun i => view t.mem (Sd s) (1 + 2 * H.D + i)) (t.gpr .r24)
      (kk s - (2 * H.D + 1))
    exact ⟨idx, by unfold kk at *; omega_using [hk2, hi], i'.trans he⟩
  -- The buffer.
  refine two_seq (Ψ := DI G H f H.D) (clearBuf_taint (dk_pins (an := id) (fun _ _ h => h.1) [.r14]))
    (fun a t ⟨⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, hk⟩, idx, hi, h25⟩ => WP.mono_syms (clearBuf_ok P b)
      fun t' ⟨b', g', _⟩ y' => ⟨⟨⟨_, s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩, idx, hi, (g' .r25 (by simp)).trans h25⟩) ?_
  refine two_seq (Ψ := DI G H f H.D) (copyT_taint H (dk_pins (an := id) (fun _ _ h => h.1) [.r14, .r15]))
    (fun a t ⟨⟨⟨_, s, m, P, T, p, y, hm, b, sy⟩, hk⟩, idx, hi, h25⟩ => WP.mono_syms (copyT_ok P rfl hD64 (hk_s p hk) b)
      fun t' ⟨b', g', _⟩ y' => ⟨⟨⟨_, s, m, P, T, p, y, hm, b', y'.trans sy⟩, hk⟩, idx, hi, (g' .r25 (by simp)).trans h25⟩) ?_
  -- The shift, `ok`, `out`, the length and the result.
  refine two_seq (Ψ := DK G H f H.D) (shift_taint (dk_pins (an := id) (fun _ _ h => h.1) [.r14, .r15]))
    (fun a t ⟨h, idx, hi, h25⟩ => dk_wp h fun _ s m P _ _ _ b => WP.mono (shift_ok P b h25 hi) fun _ h' => h'.1) ?_
  refine two_seq (Ψ := DK G H f H.D) (okMask_taint (dk_pins (an := id) (fun _ _ h => h) []))
    (fun a t h => dk_wp h fun _ s m P _ _ _ b => WP.mono (okMask_ok P b (rcOf_le _)) fun _ h' => h'.1) ?_
  refine two_seq (Ψ := fun a t => t.sp = fb a ∧ t.gpr .r17 = a.gpr .r5)
    (outLoop_taint (dk_pins (an := id) (fun _ _ h => h) [.r14, .r15, .r16])) (fun a t h => ?_) ?_
  · obtain ⟨-, -, -, -, r17, -, -⟩ := h.1.dx.pins
    obtain ⟨⟨_, s, m, P, -, p, -, hm, b, -⟩, -⟩ := h
    exact WP.mono (outLoop_ok P b) fun t' ⟨sv, _, g', _⟩ =>
      ⟨by rw [sv.sp, fb, fb, p.sp], (g' .r17 (by simp)).trans r17⟩
  exact decRet_taint H fun a t₁ t₂ h₁ h₂ => ⟨h₁.1.trans h₂.1.symm, fun r hr => by
    rw [List.mem_singleton.mp hr, h₁.2, h₂.2]⟩

end

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (hG : HashOK G) (cG : HashCT hG) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)

/-- After the entry, from an entry state with MGF1's table, `G`'s, and `a`'s
public data. -/
def AEntT (pc : Bool) (G H : Hash) (f : Fns) (a t : State) : Prop :=
  ∃ s, PreD pc s ∧ TT G H f s ∧ PubD a s ∧ SymGH G H a s ∧ Entered s t ∧ t.syms = s.syms ∧ XP pc a s

/-- After the private operation, from such an entry state. -/
def AP (G H : Hash) (f : Fns) (a v : State) : Prop :=
  ∃ pc s, PreD pc s ∧ TT G H f s ∧ PubD a s ∧ SymGH G H a s ∧ AfterPriv s v ∧ v.syms = s.syms

/-- After the check of `k`. -/
def AC (G H : Hash) (f : Fns) (D : Nat) (a v : State) : Prop :=
  ∃ pc s, PreD pc s ∧ TT G H f s ∧ PubD a s ∧ SymGH G H a s ∧ AfterPriv s v ∧ v.syms = s.syms ∧
    (v.gpr .r3 != 0) = decide (kk s < 2 * D + 2)

theorem AC.dxt {G H : Hash} {f : Fns} {D : Nat} {a v : State} (h : AC G H f D a v) : DXT G H f a v :=
  let ⟨_, s, P, T, p, y, A, sy, _⟩ := h; ⟨_, s, v.mem, P, T, p, y, A.mem, A.base, sy⟩

theorem AC.dx {G H : Hash} {f : Fns} {D : Nat} {a v : State} (h : AC G H f D a v) : DX a v := h.dxt.dx

theorem AC.r3 {G H : Hash} {f : Fns} {D : Nat} {a v : State} (h : AC G H f D a v) :
    (v.gpr .r3 != 0) = decide (kA a < 2 * D + 2) := by
  obtain ⟨_, s, _, _, p, _, _, _, r⟩ := h
  rw [r]; show decide ((s.gpr .r7).toNat < _) = _; rw [p.g .r7 (by decide)]

theorem AP.dxt {G H : Hash} {f : Fns} {a v : State} (h : AP G H f a v) : DXT G H f a v :=
  let ⟨_, s, P, T, p, y, A, sy⟩ := h; ⟨_, s, v.mem, P, T, p, y, A.mem, A.base, sy⟩

theorem AP.only {G H : Hash} {f : Fns} {a v v' : State} {rs : List Reg} (h : AP G H f a v) (o : Only rs v v')
    (y : v'.syms = v.syms) (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : AP G H f a v' :=
  let ⟨_, s, P, T, p, g, A, sy⟩ := h; ⟨_, s, P, T, p, g, A.only P o hrs, y.trans sy⟩

include hH cH hG cG hHh hHl hHv hGh hGl hGv in
theorem code_ct (pc : Bool) {f : Fns} (hl : H.D ∈ lens) :
    RelCT isa (Two fun a s => (PreD pc s ∧ TT G H f s) ∧ (PubD a s ∧ SymGH G H a s) ∧ XP pc a s) (decryptG pc f)
      fun _ _ => True := by
  have hD64 := hH.hD64
  refine two_alloc (R := fun _ _ => True) (fun a s₁ s₂ h₁ h₂ =>
    ⟨h₁.2.1.1.sp.trans h₂.2.1.1.sp.symm, fun _ h => nomatch h⟩) ?_
  refine two_seq (Ψ := AEntT pc G H f)
    (entry_taint fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, h₁.2.1.1.sp,
      h₂.2.1.1.sp], fun _ h => nomatch h⟩)
    (fun a u ⟨s, ⟨⟨P, T⟩, ⟨p, g⟩, x⟩, e⟩ => by
      subst e; exact WP.mono_syms (entry_ok P) fun t E y => ⟨s, P, T, p, g, E, y, x⟩) ?_
  refine two_seq (Ψ := AP G H f) ((priv_ct pc).mono
      (fun _ _ ⟨a, ⟨s₁, P₁, _, p₁, _, E₁, _, x₁⟩, ⟨s₂, P₂, _, p₂, _, E₂, _, x₂⟩⟩ =>
        ⟨a, ⟨s₁, P₁, p₁, E₁, x₁⟩, ⟨s₂, P₂, p₂, E₂, x₂⟩⟩) fun _ _ h => h)
    (fun a t ⟨s, P, T, p, g, E, sy, x⟩ => WP.mono_syms (priv_ok P (fun h => (x h).1) E) fun v A y =>
      ⟨_, s, P, T, p, g, A, y.trans sy⟩) ?_
  -- The label's hash function's digest length to `r3`.
  let A₃ := fun (a v : State) => AP G H f a v ∧ v.gpr .r3 = BitVec.ofNat 64 H.D
  have hlen : RelCT isa (Two (AP G H f)) (.block (lenLoad 15)) (Two A₃) :=
    (tword_two (okXL G H f) (tabXL G H f) (Φ := fun (ac : State × Nat) t => AP G H f ac.1 t)
      (fun _ _ h => h.dxt.toL hH) (d := .r3) (.inr (.inr rfl)) (k := 6) (by decide)
      (v := fun _ => BitVec.ofNat 64 H.D) fun P _ => P.2.1.d).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨(a, 0), h₁, h₂⟩)
      fun _ _ ⟨ac, ⟨t₁, h₁, o₁, z₁, e₁⟩, ⟨t₂, h₂, o₂, z₂, e₂⟩⟩ => ⟨ac.1, ⟨h₁.only o₁ z₁, e₁⟩, ⟨h₂.only o₂ z₂, e₂⟩⟩
  refine RelCT.seq hlen ?_
  -- The code for that length.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ pc s, PreD pc s ∧ PubD a s ∧ Saves s u)
    (byLen_ct (D := H.D) (Φ := A₃) (by omega_using [hD64]) (fun _ _ h => h.2)
      (fun _ _ _ h₁ h₂ => h₁.1.dxt.dx.pins.1.trans h₂.1.dxt.dx.pins.1.symm)
      (fun _ _ _ ⟨h, r3⟩ o y => ⟨h.only o y, by rw [o.get .r3]; exact r3⟩) ?_ hl lens_certs)
    fun a v ⟨⟨_, s, P, T, p, g, A, sy⟩, h3⟩ => ?_)
    (restore_taint fun a u₁ u₂ ⟨_, s₁, _, p₁, v₁⟩ ⟨_, s₂, _, p₂, v₂⟩ =>
      ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.sp, p₂.sp], fun _ h => nomatch h⟩)
  · rw [decTail_D (G := ofLen H.D) (G' := H) rfl]
    refine two_seq (Ψ := AC G H f H.D) (chkK_taint H (dx_pins (an := id) (fun _ _ h => h.1.dxt.dx) []))
      (fun a v ⟨⟨_, s, P, T, p, g, A, sy⟩, _⟩ => WP.mono_syms (chk_ok P hH.hD64 A) fun _ ⟨A', r⟩ y =>
        ⟨_, s, P, T, p, g, A', y.trans sy, r⟩) ?_
    refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.r3, h₂.r3])
      (decFail_taint (dx_pins (an := id) (fun _ _ h => h.1.dx) [.r15, .r16, .r17])) ?_
    refine (decMain_ct hH cH hG cG hGh hGl hGv).mono (fun _ _ ⟨a, ⟨h₁, c₁⟩, ⟨h₂, _⟩⟩ => ?_) fun _ _ h => h
    rw [eval_nonzero, h₁.r3] at c₁
    have hk : HK H.D a := by simp at c₁; omega
    exact ⟨a, ⟨h₁.dxt, hk⟩, ⟨h₂.dxt, hk⟩⟩
  · refine byLen_ok (D := H.D) (by omega_using [hD64])
      (F := fun u => AfterPriv s u ∧ u.syms = s.syms ∧ u.gpr .r3 = BitVec.ofNat 64 H.D)
      (fun _ h => h.2.2) (fun u u' ⟨A', y', r3'⟩ o y => ⟨A'.only P o, y.trans y', by rw [o.get .r3]; exact r3'⟩)
      ?_ hl (fun x hx => (lens_certs x hx).1) v ⟨A, sy, h3⟩
    intro u ⟨A', y', _⟩
    rw [decTail_D (G := ofLen H.D) (G' := H) rfl]
    exact WP.seq (WP.mono (checks_done hH hG hHh hHl hHv hGh hGl hGv P T.1 T.2 A' y') fun v' h => WP.mono h
      fun _ d => ⟨_, s, P, p, d.1⟩)

end

end VG.Proof.RsaOaep.PPC64LE.Dec
