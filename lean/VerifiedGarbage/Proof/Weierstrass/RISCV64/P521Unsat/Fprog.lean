module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Unsat.Mul
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Unsat.Add
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Unsat.Unpack
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Unsat.Pack
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Fprog
public import VerifiedGarbage.Spec.P521
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Unsat.Lit
import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Sqr
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Field programs on slots in 58-bit limbs, for P-521, on RISC-V

`fprog P521Unsat.field ops` runs the field operations `ops` on slots of the
working space by calls of the functions of
`Impl/Weierstrass/RISCV64/P521Unsat.lean` (`ufprog_ok`), as `fprog_ok`
(`Proof/Weierstrass/RISCV64/Fprog.lean`) does for a field in Montgomery's
form: what the slots stand for, their limbs' number modulo `p` (`uf`),
follows `runOps ops`, the program on environments (`LInv`), for slots that
hold tight limbs, apart from each other and below the functions' own working
space (`ULay`). A slot is read only once it holds tight limbs: either it did
at the start or an earlier operation wrote it (`readsOk`).

The contracts by register of the functions (`umulRV`, …), and their calls:
`ucall_ok`, of any of the functions by its contract, and those of the product,
sum and difference (`umulCall_ok`, `uaddCall_ok`, `usubCall_ok`); the
complete addition `rcb` (`urcb_ok`) and the formulas on numbered slots
(`uofN_ok`).
-/

-- separate module: the field programs in limbs, which the windows' proofs and, later, ECDSA's share

-- `p` is a numeral.
set_option exponentiation.threshold 600

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P521Unsat

open VG VG.RISCV64 VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Weierstrass.RISCV64.P521Unsat (field mulFn mulFnA addFn subFn unpackFn packFn core)
open VG.Impl.Weierstrass.Mont (p521p)
open VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Weierstrass.RISCV64 (rvPre arg res offArg WsReg CallKeep KeepR Kp own callOp_ok numAt_ofNat
  outs_of_keeps Meets alignedC outs_wordsVal progs_wp)
open VG.Proof.Weierstrass.RISCV64.GenWide (fnA_rv)
open VG.Spec.Weierstrass (Fe)

/-- P-521. -/
abbrev W : Spec.Weierstrass.Curve := Spec.P521.curve

theorem W_p : W.p = p := rfl

/-! ## The contracts by register

The five functions of `Impl/Weierstrass/RISCV64/P521Unsat.lean`, with
GenWide's entry and copies (`GenWide.fnWith_rv`, `GenWide.fn_rv`), meet contracts by register
as GenWide's do (`ws` in `a0`, the offsets in `a1`–`a3`, nine words each,
their own working space the top 576 bytes of `ws`):

* `umulRV`: tight operands to a tight result, the product modulo `p`;
* `uaddRV`, `usubRV`: the sum, and `[a] + 4p - [b]`, likewise;
* `unpackRV`: a number below `2⁵²²` to tight limbs of the same number;
* `packRV`: tight limbs to the nine words of their residue modulo `p`.
-/

section RVs

open VG.Impl.Weierstrass.RISCV64.P521Unsat
open VG.Impl.Weierstrass.Mont (Keeps)
open VG.Proof.Weierstrass.RISCV64 (rvPub rvOwn rvOwnEnd)
open VG.Proof.Weierstrass.RISCV64.GenWide (fnWith_rv fn_rv)

/-- What the five contracts keep. -/
abbrev ukeeps (s s' : State) : Prop :=
  Keeps 9 (s.gpr .a0) (offArg s .a1) s.mem s'.mem (rvOwn 9) (rvOwnEnd 9)

/-- The product. -/
def umulRV : Contract isa where
  pre s := rvPre p521p s ∧ Tight (arg p521p s .a2) ∧ Tight (arg p521p s .a3)
  post s s' := Tight (res p521p s s') ∧ uv (res p521p s s') % p = uv (arg p521p s .a2) * uv (arg p521p s .a3) % p ∧
    ukeeps s s'
  pub := rvPub

/-- The sum. -/
def uaddRV : Contract isa where
  pre s := rvPre p521p s ∧ Tight (arg p521p s .a2) ∧ Tight (arg p521p s .a3)
  post s s' := Tight (res p521p s s') ∧ uv (res p521p s s') % p = (uv (arg p521p s .a2) + uv (arg p521p s .a3)) % p ∧
    ukeeps s s'
  pub := rvPub

/-- The difference, with `4p` added. -/
def usubRV : Contract isa where
  pre s := rvPre p521p s ∧ Tight (arg p521p s .a2) ∧ Tight (arg p521p s .a3)
  post s s' := Tight (res p521p s s') ∧
    uv (res p521p s s') % p = (uv (arg p521p s .a2) + 4 * p - uv (arg p521p s .a3)) % p ∧ ukeeps s s'
  pub := rvPub

/-- Words to limbs. -/
def unpackRV : Contract isa where
  pre s := rvPre p521p s ∧ arg p521p s .a2 < 2 ^ 522
  post s s' := Tight (res p521p s s') ∧ uv (res p521p s s') = arg p521p s .a2 ∧ ukeeps s s'
  pub := rvPub

/-- Limbs to the words of their residue. -/
def packRV : Contract isa where
  pre s := rvPre p521p s ∧ Tight (arg p521p s .a2)
  post s s' := res p521p s s' = uv (arg p521p s .a2) % p ∧ ukeeps s s'
  pub := rvPub

theorem umul_rv (s : State) (hs : umulRV.pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ umulRV.post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fnWith_rv (S := p521p) (by decide) (by decide) @core_spec @mulC_spec hs.1
    hs.2
  exact ⟨t, s', he, a, v1, v2, k⟩

theorem uadd_rv (s : State) (hs : uaddRV.pre s) :
    ∃ t s', Exec isa addFn s t s' ∧ abiPreserved s s' ∧ uaddRV.post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fn_rv (S := p521p) (by decide) (by decide) @add_spec hs.1 hs.2
  exact ⟨t, s', he, a, v1, v2, k⟩

theorem usub_rv (s : State) (hs : usubRV.pre s) :
    ∃ t s', Exec isa subFn s t s' ∧ abiPreserved s s' ∧ usubRV.post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fn_rv (S := p521p) (by decide) (by decide) @sub_spec hs.1 hs.2
  exact ⟨t, s', he, a, v1, v2, k⟩

theorem unpack_rv (s : State) (hs : unpackRV.pre s) :
    ∃ t s', Exec isa unpackFn s t s' ∧ abiPreserved s s' ∧ unpackRV.post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fn_rv (S := p521p) (by decide) (by decide) @unpack_spec hs.1 hs.2
  exact ⟨t, s', he, a, v1, v2, k⟩

theorem pack_rv (s : State) (hs : packRV.pre s) :
    ∃ t s', Exec isa packFn s t s' ∧ abiPreserved s s' ∧ packRV.post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv (S := p521p) (by decide) (by decide) @pack_spec hs.1 hs.2
  exact ⟨t, s', he, a, v, k⟩

end RVs

/-! ## The product for aligned offsets -/

theorem umulA_rv (s : State) (hs : (alignedC umulRV).pre s) :
    ∃ t s', Exec isa mulFnA s t s' ∧ abiPreserved s s' ∧ umulRV.post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ :=
    fnA_rv (S := p521p) (by decide) (by decide) @core_spec hs.1.1 hs.2 (by exact hs.1.2)
  exact ⟨t, s', he, a, v1, v2, k⟩

/-! ## The calls -/

/-- The number at offset `x` of the working space. -/
abbrev wv (base : Addr) (s : State) (x : Nat) : Nat := wordsVal s.mem base x 9

theorem own9 : own 9 = 7616 := rfl

/-- A call by `callOp` of a function meeting `K` (`P` of its operands to
`R` of them and its result), or of one meeting it for aligned offsets. -/
theorem ucall_ok {f : String} {body bodyA : Prog isa} (hn : body.noFrames = true) (hnA : bodyA.noFrames = true)
    {K : Contract isa} (hK : Meets body K) (hKA : Meets bodyA (alignedC K))
    {P : Nat → Nat → Prop} {R : Nat → Nat → Nat → Prop}
    (hpre : ∀ t, rvPre p521p t → P (arg p521p t .a2) (arg p521p t .a3) → K.pre t)
    (hpost : ∀ t t', K.post t t' → R (arg p521p t .a2) (arg p521p t .a3) (res p521p t t') ∧ ukeeps t t')
    {s : State} {base : Addr} (hw : WsReg s base) {o a b : Nat}
    (ho : o + 72 ≤ 7616) (ha : a + 72 ≤ 7616) (hb : b + 72 ≤ 7616)
    (ho' : o < 4095) (ha' : a < 4095) (hb' : b < 4095) (hp : P (wv base s a) (wv base s b)) :
    WP isa (callOp f body bodyA o a b) s fun s' =>
      CallKeep 9 base o s s' ∧ R (wv base s a) (wv base s b) (wv base s' o) := by
  have h32 : ∀ x, x + 72 ≤ 7616 → x < 2 ^ 32 := fun x hx => by omega
  refine callOp_ok (S := p521p) hn hnA hK hKA hw (by rw [show p521p.k = 9 from rfl, own9]; exact ho)
    (by rw [show p521p.k = 9 from rfl, own9]; exact ha) (by rw [show p521p.k = 9 from rfl, own9]; exact hb)
    ho' ha' hb' (fun t ht h0 h1 h2 h3 hm => hpre t ht (by
      simp only [arg]
      rw [h2, h3, h0, hm, numAt_ofNat _ _ (h32 a ha), numAt_ofNat _ _ (h32 b hb)]
      exact hp)) fun s' K' Fr t h0 h1 h2 h3 hm hp' => ?_
  obtain ⟨v, k⟩ := hpost _ _ hp'
  simp only [res, arg, ukeeps, State.withRegions_mem, h0, h1, h2, h3, hm, numAt_ofNat _ _ (h32 _ ho),
    numAt_ofNat _ _ (h32 _ ha), numAt_ofNat _ _ (h32 _ hb), show p521p.k = 9 from rfl] at v k
  exact ⟨⟨K', outs_of_keeps (h32 o ho) k Fr (by decide)⟩, v⟩

/-- `[o] ≡ [a] [b]` by a call. -/
theorem umulCall_ok {s : State} {base : Addr} (hw : WsReg s base) {o a b : Nat}
    (ho : o + 72 ≤ 7616) (ha : a + 72 ≤ 7616) (hb : b + 72 ≤ 7616)
    (ho' : o < 4095) (ha' : a < 4095) (hb' : b < 4095)
    (hA : Tight (wv base s a)) (hB : Tight (wv base s b)) :
    WP isa (mulCall field o a b) s fun s' => CallKeep 9 base o s s' ∧
      Tight (wv base s' o) ∧ uv (wv base s' o) % p = uv (wv base s a) * uv (wv base s b) % p :=
  ucall_ok (K := umulRV) (P := fun A B => Tight A ∧ Tight B)
    (R := fun A B r => Tight r ∧ uv r % p = uv A * uv B % p)
    Impl.Weierstrass.RISCV64.P521Unsat.mulFn_noFrames Impl.Weierstrass.RISCV64.P521Unsat.mulFnA_noFrames
    umul_rv umulA_rv (fun _ ht hp => ⟨ht, hp⟩) (fun _ _ ⟨v1, v2, k⟩ => ⟨⟨v1, v2⟩, k⟩) hw ho ha hb ho' ha' hb' ⟨hA, hB⟩

/-- Code meeting `K` meets it for aligned offsets. -/
theorem meets_aligned {c : Prog isa} {K : Contract isa} (h : Meets c K) : Meets c (alignedC K) :=
  fun s hs => h s hs.1

/-- `[o] ≡ [a] + [b]` by a call. -/
theorem uaddCall_ok {s : State} {base : Addr} (hw : WsReg s base) {o a b : Nat}
    (ho : o + 72 ≤ 7616) (ha : a + 72 ≤ 7616) (hb : b + 72 ≤ 7616)
    (ho' : o < 4095) (ha' : a < 4095) (hb' : b < 4095)
    (hA : Tight (wv base s a)) (hB : Tight (wv base s b)) :
    WP isa (addCall field o a b) s fun s' => CallKeep 9 base o s s' ∧
      Tight (wv base s' o) ∧ uv (wv base s' o) % p = (uv (wv base s a) + uv (wv base s b)) % p :=
  ucall_ok (K := uaddRV) (P := fun A B => Tight A ∧ Tight B)
    (R := fun A B r => Tight r ∧ uv r % p = (uv A + uv B) % p)
    Impl.Weierstrass.RISCV64.P521Unsat.addFn_noFrames Impl.Weierstrass.RISCV64.P521Unsat.addFn_noFrames
    uadd_rv (meets_aligned uadd_rv) (fun _ ht hp => ⟨ht, hp⟩) (fun _ _ ⟨v1, v2, k⟩ => ⟨⟨v1, v2⟩, k⟩) hw ho ha hb
    ho' ha' hb' ⟨hA, hB⟩

/-- `[o] ≡ [a] + 4p - [b]` by a call. -/
theorem usubCall_ok {s : State} {base : Addr} (hw : WsReg s base) {o a b : Nat}
    (ho : o + 72 ≤ 7616) (ha : a + 72 ≤ 7616) (hb : b + 72 ≤ 7616)
    (ho' : o < 4095) (ha' : a < 4095) (hb' : b < 4095)
    (hA : Tight (wv base s a)) (hB : Tight (wv base s b)) :
    WP isa (subCall field o a b) s fun s' => CallKeep 9 base o s s' ∧
      Tight (wv base s' o) ∧ uv (wv base s' o) % p = (uv (wv base s a) + 4 * p - uv (wv base s b)) % p :=
  ucall_ok (K := usubRV) (P := fun A B => Tight A ∧ Tight B)
    (R := fun A B r => Tight r ∧ uv r % p = (uv A + 4 * p - uv B) % p)
    Impl.Weierstrass.RISCV64.P521Unsat.subFn_noFrames Impl.Weierstrass.RISCV64.P521Unsat.subFn_noFrames
    usub_rv (meets_aligned usub_rv) (fun _ ht hp => ⟨ht, hp⟩) (fun _ _ ⟨v1, v2, k⟩ => ⟨⟨v1, v2⟩, k⟩) hw ho ha hb
    ho' ha' hb' ⟨hA, hB⟩

/-- `[o]` = the limbs of `[a]`, below `2⁵²²`, by a call. -/
theorem unpackCall_ok {f : String} {s : State} {base : Addr} (hw : WsReg s base) {o a b : Nat}
    (ho : o + 72 ≤ 7616) (ha : a + 72 ≤ 7616) (hb : b + 72 ≤ 7616)
    (ho' : o < 4095) (ha' : a < 4095) (hb' : b < 4095) (hA : wv base s a < 2 ^ 522) :
    WP isa (callOp f unpackFn unpackFn o a b) s fun s' => CallKeep 9 base o s s' ∧
      Tight (wv base s' o) ∧ uv (wv base s' o) = wv base s a :=
  ucall_ok (K := unpackRV) (P := fun A _ => A < 2 ^ 522) (R := fun A _ r => Tight r ∧ uv r = A)
    Impl.Weierstrass.RISCV64.P521Unsat.unpackFn_noFrames Impl.Weierstrass.RISCV64.P521Unsat.unpackFn_noFrames
    unpack_rv (meets_aligned unpack_rv) (fun _ ht hp => ⟨ht, hp⟩) (fun _ _ ⟨v1, v2, k⟩ => ⟨⟨v1, v2⟩, k⟩) hw ho ha hb
    ho' ha' hb' hA

/-- `[o]` = the residue of the tight limbs `[a]`, by a call. -/
theorem packCall_ok {f : String} {s : State} {base : Addr} (hw : WsReg s base) {o a b : Nat}
    (ho : o + 72 ≤ 7616) (ha : a + 72 ≤ 7616) (hb : b + 72 ≤ 7616)
    (ho' : o < 4095) (ha' : a < 4095) (hb' : b < 4095) (hA : Tight (wv base s a)) :
    WP isa (callOp f packFn packFn o a b) s fun s' => CallKeep 9 base o s s' ∧
      wv base s' o = uv (wv base s a) % p :=
  ucall_ok (K := packRV) (P := fun A _ => Tight A) (R := fun A _ r => r = uv A % p)
    Impl.Weierstrass.RISCV64.P521Unsat.packFn_noFrames Impl.Weierstrass.RISCV64.P521Unsat.packFn_noFrames
    pack_rv (meets_aligned pack_rv) (fun _ ht hp => ⟨ht, hp⟩) (fun _ _ ⟨v, k⟩ => ⟨v, k⟩) hw ho ha hb
    ho' ha' hb' hA

/-! ## What limbs stand for -/

/-- The element tight limbs stand for. -/
def uf (X : Nat) : Fe W := Fin.ofNat W.p (uv X)

theorem lv9' (l : Nat → Nat) : lv l 9 = l 0 + 2 ^ 58 * l 1 + 2 ^ 116 * l 2 + 2 ^ 174 * l 3 + 2 ^ 232 * l 4 +
    2 ^ 290 * l 5 + 2 ^ 348 * l 6 + 2 ^ 406 * l 7 + 2 ^ 464 * l 8 := by
  simp only [lv]; omega

/-- Tight limbs stand for a number below `4p`. -/
theorem uv_le {X : Nat} (h : Tight X) : uv X ≤ 4 * p := by
  obtain ⟨h1, h2⟩ := h
  have := h1 0 (by decide); have := h1 1 (by decide); have := h1 2 (by decide); have := h1 3 (by decide)
  have := h1 4 (by decide); have := h1 5 (by decide); have := h1 6 (by decide); have := h1 7 (by decide)
  rw [uv, lv9', show 4 * p = 2 ^ 523 - 4 from rfl]
  omega

theorem uf_eq {X : Nat} {v : Nat} (h : uv X % p = v % p) : uf X = Fin.ofNat W.p v :=
  Fin.ext (by simp only [uf, W_p]; exact h)

theorem uf_mul {r A B : Nat} (h : uv r % p = uv A * uv B % p) : uf r = uf A * uf B := by
  rw [uf_eq h]
  apply Fin.ext
  simp [uf, Fin.val_mul, Nat.mul_mod]

theorem uf_add {r A B : Nat} (h : uv r % p = (uv A + uv B) % p) : uf r = uf A + uf B := by
  rw [uf_eq h]
  apply Fin.ext
  simp [uf, Fin.val_add, Nat.add_mod]

theorem uf_sub {r A B : Nat} (hB : uv B ≤ 4 * p) (h : uv r % p = (uv A + 4 * p - uv B) % p) :
    uf r = uf A - uf B := by
  rw [uf_eq h]
  have e : Fin.ofNat W.p (uv A + 4 * p - uv B) + uf B = uf A := by
    apply Fin.ext
    simp only [uf, Fin.val_add, Fin.val_ofNat]
    rw [← Nat.add_mod, Nat.sub_add_cancel (by omega), W_p, show 4 * p = p * 4 from Nat.mul_comm _ _,
      Nat.add_mul_mod_self_left]
  rw [← e]; grind

/-! ## The invariant -/

/-- Slots apart from each other, below the functions' own working space, at
offsets `liAt` reaches. -/
structure ULay (Sl : Nat → Prop) : Prop where
  le : ∀ x, Sl x → x + 72 ≤ 7616
  apart : ∀ x y, Sl x → Sl y → x ≠ y → x + 72 ≤ y ∨ y + 72 ≤ x
  short : ∀ x, Sl x → x < 4095

/-- The state holds the environment `E` in tight limbs in the slots `V` (of
`Sl`), and the working space is at `s0`. -/
structure LInv (base : Addr) (Sl : Nat → Prop) (V : List Nat) (E : Nat → Fe W) (s : State) : Prop where
  ws : WsReg s base
  sl : ∀ x ∈ V, Sl x
  tight : ∀ x ∈ V, Tight (wv base s x)
  val : ∀ x ∈ V, uf (wv base s x) = E x

theorem LInv.sub {base : Addr} {Sl : Nat → Prop} {V V' : List Nat} {E : Nat → Fe W} {s : State}
    (h : LInv base Sl V E s) (hV : ∀ x ∈ V', x ∈ V) : LInv base Sl V' E s :=
  ⟨h.ws, fun x hx => h.sl x (hV x hx), fun x hx => h.tight x (hV x hx), fun x hx => h.val x (hV x hx)⟩

/-- An operation writing `o`, which then holds `v`, keeps the invariant. -/
theorem LInv.update {base : Addr} {Sl : Nat → Prop} (hL : ULay Sl) {V : List Nat} {E : Nat → Fe W} {s s' : State}
    (hI : LInv base Sl V E s) {o : Nat} (ho : Sl o) (hk : KeepR 9 base [o] s s')
    (hr : Tight (wv base s' o)) {v : Fe W} (hv : uf (wv base s' o) = v) :
    LInv base Sl (o :: V) (Function.update E o v) s' := by
  have heq : ∀ x ∈ V, x ≠ o → wv base s' x = wv base s x := by
    intro x hx hxo
    have hxS := hI.sl x hx
    have h1 := hL.le x hxS
    have h2 := hL.apart x o hxS ho hxo
    refine outs_wordsVal hk.mem (fun r hr => ?_) (by omega)
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h2
    · exact .inl (by rw [own9]; exact h1)
  refine ⟨hI.ws.of_kp hk.kp, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ho
    · exact hI.sl x hx
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; exact hr
    · have hx' := List.mem_of_ne_of_mem hxo hx
      rw [heq x hx' hxo]; exact hI.tight x hx'
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; rw [Function.update_self]; exact hv
    · have hx' := List.mem_of_ne_of_mem hxo hx
      rw [heq x hx' hxo, Function.update_of_ne hxo]
      exact hI.val x hx'

/-- One operation. -/
theorem ufop_ok {base : Addr} {Sl : Nat → Prop} (hL : ULay Sl) {V : List Nat} {E : Nat → Fe W} {s : State}
    (hI : LInv base Sl V E s) {op : FOp} (hS : ∀ x ∈ op.out :: op.ins, Sl x) (hR : ∀ x ∈ op.ins, x ∈ V) :
    WP isa (opCode field op) s fun s' =>
      KeepR 9 base [op.out] s s' ∧ LInv base Sl (op.out :: V) (op.run E) s' := by
  cases op with
  | mul o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    refine WP.mono (umulCall_ok hI.ws (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
        (hL.short o hS.1) (hL.short a hS.2.1) (hL.short b hS.2.2) (hI.tight a hR.1) (hI.tight b hR.2))
      fun s' ⟨K, ht, heq⟩ => ?_
    refine ⟨.of_call K, hI.update hL hS.1 (.of_call K) ht ?_⟩
    rw [uf_mul heq, hI.val a hR.1, hI.val b hR.2]
  | add o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    refine WP.mono (uaddCall_ok hI.ws (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
        (hL.short o hS.1) (hL.short a hS.2.1) (hL.short b hS.2.2) (hI.tight a hR.1) (hI.tight b hR.2))
      fun s' ⟨K, ht, heq⟩ => ?_
    refine ⟨.of_call K, hI.update hL hS.1 (.of_call K) ht ?_⟩
    rw [uf_add heq, hI.val a hR.1, hI.val b hR.2]
  | sub o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    refine WP.mono (usubCall_ok hI.ws (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
        (hL.short o hS.1) (hL.short a hS.2.1) (hL.short b hS.2.2) (hI.tight a hR.1) (hI.tight b hR.2))
      fun s' ⟨K, ht, heq⟩ => ?_
    refine ⟨.of_call K, hI.update hL hS.1 (.of_call K) ht ?_⟩
    rw [uf_sub (uv_le (hI.tight b hR.2)) heq, hI.val a hR.1, hI.val b hR.2]

/-- A field program. -/
theorem ufprog_ok {base : Addr} {Sl : Nat → Prop} (hL : ULay Sl) :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fe W} {s : State},
      LInv base Sl V E s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) →
      readsOk ops V = true →
      WP isa (fprog field ops) s fun s' => KeepR 9 base (ops.map FOp.out) s s' ∧
        LInv base Sl (validAfter ops V) (runOps ops E) s'
  | [], _, _, s, hI, _, _ => WP.block_nil ⟨KeepR.refl _ _ _ s, hI⟩
  | op :: ops, V, E, s, hI, hS, hR => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    refine progs_wp _ _ (WP.mono (ufop_ok hL hI (hS op (List.mem_cons_self ..)) hR.1)
      fun s₁ ⟨k₁, I₁⟩ => ?_)
    refine WP.mono (ufprog_ok hL ops I₁ (fun op' h => hS op' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨(k₁.mono fun w hw => ?_).trans (k₂.mono fun w hw => ?_), I₂⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      simp [hw]
    · simp [hw]

/-! ## The complete addition and the formulas on numbered slots -/

/-- `o = p + q` by `rcb`, as `rcb_ok`. -/
theorem urcb_ok {base : Addr} {Sl : Nat → Prop} (hL : ULay Sl) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat}
    {E : Nat → Fe W} {s : State} (hI : LInv base Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprog field (rcb S p q o)) s fun s' => KeepR 9 base (rcbW S o) s s' ∧
      LInv base Sl (rcbW S o ++ V) (runOps (rcb S p q o) E) s' ∧
      (runOps (rcb S p q o) E o.x, runOps (rcb S p q o) E o.y, runOps (rcb S p q o) E o.z) =
        VG.Proof.Weierstrass.rcbAdd (E S.a) (E S.b3) (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) (E q.z) ∧
      ∀ x, x ∉ rcbW S o → runOps (rcb S p q o) E x = E x := by
  have hR : readsOk (rcb S p q o) V = true := by
    rw [rcb_eq_rename]
    exact readsOk_mono (readsOk_rename _ rcbN_reads) hV
  refine WP.mono (ufprog_ok hL _ hI (fun op hop x hx => hSl x (rcb_slots op hop x hx)) hR)
    fun s' ⟨hk', hI'⟩ => ⟨hk'.mono fun w hw => ?_, hI'.sub fun x hx => ?_, rcb_run hA E,
      fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ rcb_out op hop)⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact rcb_out op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (rcb_out_mem hx)
    · exact Or.inl hx

/-- A formula on numbered slots (`NumOk`), renamed to the slots of a sum, as
`ofN_ok`. -/
theorem uofN_ok {base : Addr} {Sl : Nat → Prop} (hL : ULay Sl) {N : List FOp} (hN : NumOk N) {S : RcbSlots}
    {p q o : Pt} (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat}
    {E : Nat → Fe W} {s : State} (hI : LInv base Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprog field (ofN N S p q o)) s fun s' => KeepR 9 base (rcbW S o) s s' ∧
      LInv base Sl ([o.x, o.y, o.z] ++ V) (runOps (ofN N S p q o) E) s' ∧
      (runOps (ofN N S p q o) E o.x, runOps (ofN N S p q o) E o.y, runOps (ofN N S p q o) E o.z) =
        (runOps N (fun y => E (rcbσ S p q o y)) 6, runOps N (fun y => E (rcbσ S p q o y)) 7,
          runOps N (fun y => E (rcbσ S p q o y)) 8) ∧
      ∀ x, x ∉ rcbW S o → runOps (ofN N S p q o) E x = E x := by
  have hR : readsOk (ofN N S p q o) V = true := readsOk_mono (ofN_readsOk hN S p q o) hV
  refine WP.mono (ufprog_ok hL _ hI (fun op hop x hx => hSl x (ofN_slots op hop x hx)) hR)
    fun s' ⟨hk', hI'⟩ => ⟨hk'.mono fun w hw => ?_, hI'.sub fun x hx => ?_, ?_,
      fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ ofN_out hN op hop)⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact ofN_out hN op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ofN_out_mem hN hx)
    · exact Or.inl hx
  · exact congrArg₂ Prod.mk (ofN_run hN hA E 6) (congrArg₂ Prod.mk (ofN_run hN hA E 7) (ofN_run hN hA E 8))

end VG.Proof.Weierstrass.RISCV64.P521Unsat
