# `vg_rsa_keygen_key` on AArch64: plan of the remaining proofs

The code is `Impl/RsaKeyGen/AArch64/Key.lean`; its x86-64 twin is proven in
`Proof/RsaKeyGen/X86_64/Key/`, which every piece below mirrors (same names,
`_k` suffix). This directory already has (do not edit these files; add new
ones):

| File | What it gives |
| --- | --- |
| `Contract.lean` | `keyPre`, `keyRes`, `keyOuts`, `keyPost`, `keyLeak`, `keyPub`, `keyA` |
| `Implies.lean` | `key_implies : keyA.Implies (Spec.RsaKeyGen.keyContract abi)` |
| `State.lean` | `Rc`, `KF` and its lemmas, `KIn`, `KIn.W/P₀/Q₀/E/P/Q/L`, `KLens`, `KArgs`, `kRegs`, `KS`, `KS.step`, `KS.regs`, `KS.hdrW`, `av`, `atop`, `av_of_full`, `csL`, `csD`, `DRes`, `KPrimes`, `KFront` |
| `Pieces.lean` | `wv_zero2`, `wv_put`, `wv_put0`, `zeroA_k`, `copyA_k`, `zc_k`, `constA_k`, `cmpA_k`, `ltA_k`, `geA_k`, `zeroMask_ok`, `nonzeroMask_ok`, `eqMask_k`, `neMask_k`, `wsMov_ok`, `wsBase16_ok`, `selC_k`, `oddMaskOf_k`, `evenMaskOf_k`, `mask_even`, `word_mod2`, `setOne_k`, `divmod_k`, `divmod_rem`, `inverse_k` |
| `Shared.lean` | `mulTo_k` (for `phi` and `nPart`), `invFrom_k`, `gcdIsOne_k`, `dv`, `or_and1_mask`, `av_or1`, `divisorOf_k` |
| `Ctx.lean` | `keyIn`, `outsL`, `KOuts`, `KCtx`, `keyCtx_of : keyPre s → KCtx s` |
| `Entry.lean` | `keyEntry_ok`, `keyStart_k : KCtx s → WP isa (.block (entry ++ Keys.head)) s fun t => KS (keyIn s) s t` |
| `Front.lean` | `loads_k`, `order_k`, `subC_k`, `decTo_k`, `front_k` (to `KPrimes`), `KLens.P_lt`, `Q_lt`, `E_lt`, `L_lt` |

Every new file starts with

```lean
namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)
```

(the `open`s matter: Lean's `autoImplicit` would make an unknown `loadE` a
variable) and imports `Key.Shared` (or `Key.Front`), plus what it needs; never an
`X86_64` module.

## The state predicate, and how to keep it

`KS I s₀ s` (`State.lean`) holds between all pieces: `Ws s I.B I.Z I.W`
(the working space, `x0 = I.B`), `KArgs s.mem I` (the header slots of
`entry`), `Src` of `p`, `q`, `e`, `InScr I.B I.Z s₀.mem s.mem`,
`s.wr = I.Wr`, and `Keep kRegs s₀ s` (`kRegs = .x0 :: mmRegs`, so every
callee-saved register, `sp` and the low halves of `v8`–`v15` are those on
entry: `abiPreserved_of_keep` at the end). The pieces may change any array
(`Rc.arr j`, `j < 16`) and the header slots 29–31 (`Rc.hdr kEv`,
`Rc.hdr kOk`); `Rc.mut` says which.

* After code that changes memory only in parts `cs` (`KF I.B I.W cs s.mem t.mem`)
  and registers `regs ⊆ mmRegs` (`Keep regs s t`):
  `h.step hf (by decide : cs.all Rc.mut = true) k` (the last argument
  `regs ⊆ mmRegs` is `by decide` by default).
* Code that does not change memory: `h.regs hm k`.
* A store to `kOk` or `kEv`: `h.hdrW (i := kOk) (by unfold kOk sFn; omega) hm k`
  gives `KS`, the `KF [.hdr kOk]` and the word.
* Values: `av I m j` (array `j`'s low `W` words), `atop I m j` (its word
  `W`). Across a piece, `f.av hok hj hn hZ` / `f.at …` / `f.word hok hi hn`
  for parts outside `cs` (`hok : cs.all Rc.ok = true := by decide`,
  `hZ := h.hZ`). A result over `W + 2` words becomes an `av` with
  `av_of_full` (bound `< 2^(64 W)`), a `divmod` remainder (`W + 1` words)
  with `divmod_rem`.
* Each piece is stated `KS I s₀ s → … → WP isa piece s fun t => KS I s₀ t ∧
  KF I.B I.W cs s.mem t.mem ∧ facts`, where `cs` lists the parts it changes,
  so that callers read every other array and slot through `KF`.
* Masks are in `x15` as `mask b` (`Proof/Bignum/Words.lean`). `x15` survives
  `zeroA`, `copyA`, `constA`, the bases, `selC`, `halfIf`'s loops: take it
  from a piece's `Keep`.
* Sequences: `wp_seqs_append (by simp [...]) (by simp [...])` to split
  `seqs (a ++ b)`; write the piece as a right-nested `++` first
  (`theorem foo_eq : foo = a ++ (b ++ c) := by simp only [foo, List.append_assoc]`),
  ascribing instruction lists next to `++` (`([...] : List Instr)`).
* Symbolic execution: `brun [...]` inside `WP.keep regs (Q := …) (by brun …)
  (by decide) (by decide) (by decide +kernel)` (see `Pieces.lean`); give it
  the loads and stores as `h.ws.scr.ld (d := …) (by omega)` /
  `.st`, the header slots with `hdr_enc (show kOk < 32 by decide)`, and the
  register values as equations. Split long blocks with
  `WP.block_append_iff` (memory).

## Agent A: `lcm(p − 1, q − 1)` (`Halve.lean`, `Lcm.lean`)

x86: `Halve.lean`, `Lcm.lean`. Imports: `Key.Shared`,
`VerifiedGarbage.Proof.RsaKeyGen.KeyMath` (`halveStep`, `halveIter`,
`halve_end`, … are target-independent).

```lean
/-- `phi`: `[aL] := [aPm] [aQm]` (`mulTo_k`). -/
theorem phi_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {w : Nat} (hW : I.W = 2 * w)
    {a b : Nat} (ha : av I s.mem aPm = a) (hb : av I s.mem aQm = b) (ha' : a < 2 ^ (64 * w))
    (hb' : b < 2 ^ (64 * w)) :
    WP isa (seqs phi) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aL] s.mem t.mem ∧
      wv t.mem I.B (slot I.W aL) (I.W + 2) = a * b

/-- `halfIf j`: `[j] := x15 ? [j] / 2 : [j]` (`shr_ok` into `aT`, then
`selLoop_ok`); word `W` of `[j]` must be 0 (`shrBody` reads it). -/
theorem halfIf_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {j : Nat} (hj : j < 16) (hjT : j ≠ aT)
    {c : Bool} (h15 : s.gpr .x15 = mask c) (htop : atop I s.mem j = 0) :
    WP isa (seqs (halfIf j)) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr j, .arr aT] s.mem t.mem ∧
      av I t.mem j = (if c then av I s.mem j / 2 else av I s.mem j) ∧ atop I t.mem j = 0 ∧
      Keep [.x3, .x4, .x11, .x12, .x14, .x16, .x17] s t

/-- What a step of the halving keeps and changes (x86's, without `sMo`). -/
def TwoP (I : KIn) (s₀ s t : State) : Prop :=
  KS I s₀ t ∧ KF I.B I.W [.arr aU, .arr aV, .arr aL, .arr aT] s.mem t.mem ∧
    atop I t.mem aU = 0 ∧ atop I t.mem aV = 0 ∧ atop I t.mem aL = 0

theorem TwoP.trans {I : KIn} {s₀ s t u : State} (h₁ : TwoP I s₀ s t) (h₂ : TwoP I s₀ t u) : TwoP I s₀ s u

/-- One step: the mask of `u` and `v` both even into `x15`
(`((u | v) & 1) − 1`), the three halvings, and `x6` counted down. -/
theorem twoStep_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) (hU0 : atop I s.mem aU = 0)
    (hV0 : atop I s.mem aV = 0) (hL0 : atop I s.mem aL = 0) :
    WP isa twoStep s fun t => TwoP I s₀ s t ∧ t.gpr .x6 = s.gpr .x6 - BitVec.ofNat 64 1 ∧
      (av I t.mem aU, av I t.mem aV, av I t.mem aL) = halveStep (av I s.mem aU, av I s.mem aV, av I s.mem aL)

/-- `64 W` steps (`x6 := W << 6`, then `wp_countdown` on `x6`). -/
theorem twos_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) (hU0 : atop I s.mem aU = 0)
    (hV0 : atop I s.mem aV = 0) (hL0 : atop I s.mem aL = 0) :
    WP isa (seqs twos) s fun t => TwoP I s₀ s t ∧
      (av I t.mem aU, av I t.mem aV, av I t.mem aL) =
        halveIter (64 * I.W) (av I s.mem aU, av I s.mem aV, av I s.mem aL)

/-- `gcdUV`: `v` made odd by a swap (`evenMaskOf_k`), the mask of `v < 2`
into `kOk`, `inverse` modulo `v` (3 if `v < 2`, by `selC_k`), and 1 for
`v < 2`. -/
theorem gcdUV_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) (hU0 : atop I s.mem aU = 0)
    (hodd : let v := if av I s.mem aV % 2 = 0 then av I s.mem aU else av I s.mem aV; 2 ≤ v → v % 2 = 1) :
    WP isa (seqs gcdUV) s fun t => KS I s₀ t ∧
      KF I.B I.W [.arr aU, .arr aV, .arr aC, .arr aM, .arr aX₁, .arr aX₂, .arr aT, .hdr kOk] s.mem t.mem ∧
      av I t.mem aV =
        (let u := if av I s.mem aV % 2 = 0 then av I s.mem aV else av I s.mem aU
         let v := if av I s.mem aV % 2 = 0 then av I s.mem aU else av I s.mem aV
         if v ≤ 1 then 1 else Nat.gcd u v)

/-- `lcmPart`: `[aL] := lcm(a, b)`. -/
theorem lcm_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {w : Nat} (hW : I.W = 2 * w)
    {a b : Nat} (ha : av I s.mem aPm = a) (hb : av I s.mem aQm = b) (ha' : a < 2 ^ (64 * w))
    (hb' : b < 2 ^ (64 * w)) :
    WP isa (seqs lcmPart) s fun t => KS I s₀ t ∧ KF I.B I.W csL s.mem t.mem ∧ av I t.mem aL = Nat.lcm a b
```

AArch64 differences: the halving's mask is `x15` (not `sMo`), `halfIf`
selects with `Crt.selLoop` (`selLoop_ok`, `[x17] := x15 ? [x16] : [x17]`),
the shift is `shr_ok` (`Proof/Rsa/AArch64/KeyLoops.lean`), the counter is
`x6` counted down by `wp_countdown`, and `selC` selects `[aC]` under the
mask of the *bad* case (`v < 2`).

## Agent B: `d = e⁻¹ mod L` and `smallMask` (`DBase.lean`, `DOdd.lean`, `DEven.lean`, `DPart.lean`, `Small.lean`)

x86: `DBase.lean`, `Minv.lean`, `DOdd.lean`, `DEven.lean`, `DPart.lean`,
`Small.lean`. `minv` on AArch64 is `minv_ok` (`Proof/Bignum/AArch64/Setup.lean`,
leaving `e⁻¹ mod 2⁶⁴` in `x4`); `mulAddRow_ok` is in
`Proof/Bignum/AArch64/Row.lean`.

```lean
theorem loadEv_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {e : Nat} (he : e < 2 ^ 64)
    (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) :
    WP isa (seqs loadEv) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aE] s.mem t.mem ∧
      wv t.mem I.B (slot I.W aE) (I.W + 2) = e

/-- `lGe2`: `kOk := ` the mask of `L ≥ 2` (`geA_k`). -/
theorem lGe2_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (seqs lGe2) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aC, .hdr kOk] s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (decide (2 ≤ av I s.mem aL))

theorem dOne_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {L : Nat} (hL : av I s.mem aL = L) :
    WP isa (seqs dOne) s fun t => KS I s₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I 1 L t.mem

theorem dOdd_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {e L : Nat} (he3 : 3 ≤ e) (he64 : e < 2 ^ 64)
    (heo : e % 2 = 1) (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hL : av I s.mem aL = L)
    (hLW : L < 2 ^ (64 * I.W)) :
    WP isa (seqs dOdd) s fun t => KS I s₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem

theorem dEven_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {e L : Nat} (he64 : e < 2 ^ 64)
    (hee : e % 2 = 0) (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hL : av I s.mem aL = L)
    (hLW : L < 2 ^ (64 * I.W)) :
    WP isa (seqs dEven) s fun t => KS I s₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem

/-- `dPart`: by `e` (`cbz`/`cbnz` on `x3`: `eval_zero`, `eval_nonzero`). -/
theorem dPart_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {e L : Nat} (he64 : e < 2 ^ 64)
    (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hL : av I s.mem aL = L) (hLW : L < 2 ^ (64 * I.W)) :
    WP isa dPart s fun t => KS I s₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem

/-- `smallMask`: `x15 := kOk & ` the mask of `d ≤ 2^(64 w)` (`ltA_k` against
`2^(64 w) + 1`). -/
theorem smallMask_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {w : Nat} (hW : I.W = 2 * w) {ok : Bool}
    (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa (seqs smallMask) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aC] s.mem t.mem ∧
      t.gpr .x15 = mask (decide (av I s.mem aDd ≤ 2 ^ (64 * w)) && ok)
```

AArch64 differences: `dOdd` keeps `t = e − x` in `x1` and the low word
`(1 + R t) e⁻¹` in `x10` (no `sMo`); `dEven`'s divisor is `divisorOf_k`
(`Shared.lean`); `dEven` computes the mask of `L` even or below 3 in `x15`
(`ltA_k`, `evenMaskOf_k`, `orr`) and stores its complement (`notMask`) in
`kOk`; `selC_k` takes the mask of the bad case. `dZero` is two
instructions (`KS.hdrW`). Use `invFrom_k`, `gcdIsOne_k`, `inverse_k`,
`divmod_k`, `divmod_rem` from this directory.

## Agent C: the key and the outputs (`Qinv.lean`, `Crt.lean`, `NFin.lean`, `Out.lean`, `Res.lean`, `Tail.lean`)

x86: the files of the same names. `Res.lean` is target-independent but for
the return register (`x0` for `rax`); `keyFromPrimes_code` and `qModP` are
in `Proof/RsaKeyGen/KeyOp.lean`; `outsL` and `KOuts` in `Key/Ctx.lean`
(import it, or `Key.Entry`). The stores: `storeA_ok` (`KeyWs.lean`),
`zeroOut_ok` (`Proof/Rsa/AArch64/CvFail.lean`).

```lean
/-- The modulus of `qInv`: `p` if it is odd and at least 3, else 3. -/
abbrev qMod (P : Nat) : Nat := if (decide (P % 2 = 1) && !decide (P < 3)) = true then P else 3

abbrev csQ : List Rc := [.arr aU, .arr aC, .arr aM, .arr aV, .arr aX₁, .arr aX₂, .arr aT, .hdr kOk]

theorem qinvPart_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {P Q : Nat} {ok : Bool}
    (hP : av I s.mem aPa = P) (hQ : av I s.mem aQa = Q) (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa (seqs qinvPart) s fun t => KS I s₀ t ∧ KF I.B I.W csQ s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (decide (Nat.gcd Q (qMod P) = 1) && ok) ∧
      ((qMod P : Nat) : Int) ∣ (av I t.mem aX₂ : Int) * Q - Nat.gcd Q (qMod P) ∧ av I t.mem aX₂ < qMod P

abbrev csC : List Rc := [.arr aM, .arr aC, .arr aU, .arr aV, .arr aT, .arr aX₁]

theorem crtPart_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {d a b : Nat} (hd : av I s.mem aDd = d)
    (ha : av I s.mem aPm = a) (hb : av I s.mem aQm = b) :
    WP isa (seqs crtPart) s fun t => KS I s₀ t ∧ KF I.B I.W csC s.mem t.mem ∧
      av I t.mem aX₁ = d % dv a ∧ av I t.mem aV = d % dv b

/-- `nPart` (`mulTo_k`). -/
theorem nPart_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {w : Nat} (hW : I.W = 2 * w)
    {a b : Nat} (ha : av I s.mem aPa = a) (hb : av I s.mem aQa = b) (ha' : a < 2 ^ (64 * w))
    (hb' : b < 2 ^ (64 * w)) :
    WP isa (seqs nPart) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aQt] s.mem t.mem ∧
      wv t.mem I.B (slot I.W aQt) (I.W + 2) = a * b

abbrev finalOk (W n P Q e : Nat) (ok : Bool) : Bool :=
  decide (2 ^ (64 * W - 1) ≤ n) && ok && decide (P % 2 = 1) && decide (Q % 2 = 1) && Spec.Rsa.exponentValid e

/-- `finalMask` (the masks and'ed in `x10`, then to `kOk`). -/
theorem finalMask_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {n P Q e : Nat} {ok : Bool}
    (hn : av I s.mem aQt = n) (hP : av I s.mem aPa = P) (hQ : av I s.mem aQa = Q) (he64 : e < 2 ^ 64)
    (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa (.block finalMask) s fun t => KS I s₀ t ∧ KF I.B I.W [.hdr kOk] s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (finalOk I.W n P Q e ok)

/-- What `keyPart` leaves, from `KFront` and `kOk` the mask of `ok`. -/
def TailPost (I : KIn) (s t : State) (ok : Bool) : Prop :=
  ∃ x : Nat, ((qMod I.P : Nat) : Int) ∣ (x : Int) * I.Q - Nat.gcd I.Q (qMod I.P) ∧ x < qMod I.P ∧
    (let c := finalOk I.W (I.P * I.Q) I.P I.Q I.E (decide (Nat.gcd I.Q (qMod I.P) = 1) && ok)
     t.gpr .x0 = BitVec.ofNat 64 c.toNat ∧
     Spec.Rsa.bytesAt t.mem I.pN (2 * I.pl) = Spec.Rsa.i2osp (if c then I.P * I.Q else 0) (2 * I.pl) ∧
     Spec.Rsa.bytesAt t.mem I.pD (2 * I.pl) = Spec.Rsa.i2osp (if c then av I s.mem aDd else 0) (2 * I.pl) ∧
     Spec.Rsa.bytesAt t.mem I.pP I.pl = Spec.Rsa.i2osp (if c then I.P else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pQ I.pl = Spec.Rsa.i2osp (if c then I.Q else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pDp I.pl = Spec.Rsa.i2osp (if c then av I s.mem aDd % dv (I.P - 1) else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pDq I.pl = Spec.Rsa.i2osp (if c then av I s.mem aDd % dv (I.Q - 1) else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pQi I.pl = Spec.Rsa.i2osp (if c then x else 0) I.pl) ∧
    (∀ y, I.Z ≤ ofs I.B y → (∀ o ∈ outsL I, ∀ i < o.2, y ≠ o.1 + BitVec.ofNat 64 i) → t.mem y = s.mem y) ∧
    Keep kRegs s t

theorem keyPart_k {I : KIn} {s₀ s : State} (h : KFront I s₀ s) (L : KLens I) (O : KOuts I) {ok : Bool}
    (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa keyPart s (fun t => TailPost I s t ok)

/-- What `zeros 2` leaves. -/
def ZerosPost (I : KIn) (s t : State) : Prop :=
  t.gpr .x0 = BitVec.ofNat 64 2 ∧ (∀ o ∈ outsL I, Spec.Rsa.bytesAt t.mem o.1 o.2 = List.replicate o.2 0) ∧
    (∀ y, I.Z ≤ ofs I.B y → (∀ o ∈ outsL I, ∀ i < o.2, y ≠ o.1 + BitVec.ofNat 64 i) → t.mem y = s.mem y) ∧
    Keep kRegs s t

theorem zerosPart_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) (L : KLens I) (O : KOuts I) :
    WP isa (zeros 2) s (ZerosPost I s)

/-- `Res.lean`: the status and the outputs `keyOp` gives. -/
def OutsRes (I : KIn) (m : Mem) (x0 : BitVec 64) : Prop :=
  (x0.setWidth 32).toNat = Spec.RsaKeyGen.keyStatus (Spec.RsaKeyGen.keyOp I.pl I.eb I.pb I.qb) ∧
    match Spec.RsaKeyGen.keyOp I.pl I.eb I.pb I.qb with
    | .inl (.ok ys) => (outsL I).map (fun o => Spec.Rsa.bytesAt m o.1 o.2) = ys
    | _ => ∀ o ∈ outsL I, Spec.Rsa.bytesAt m o.1 o.2 = List.replicate o.2 0

theorem outsRes_zeros {I : KIn} {s t : State} {d : Nat}
    (hd : Spec.Rsa.inverse I.E I.L = some d) (hsm : d ≤ 2 ^ (8 * I.pl)) (Z : ZerosPost I s t) :
    OutsRes I t.mem (t.gpr .x0)

theorem outsRes_tail {I : KIn} {s t : State} (L : KLens I) {ok : Bool}
    (hok : (∃ d, Spec.Rsa.inverse I.E I.L = some d) ↔ ok = true)
    (hdd : ∀ d, Spec.Rsa.inverse I.E I.L = some d → av I s.mem aDd = d)
    (hb : (decide (av I s.mem aDd ≤ 2 ^ (8 * I.pl)) && ok) = false) (T : TailPost I s t ok) :
    OutsRes I t.mem (t.gpr .x0)
```

AArch64 differences: `qinvPart` takes the mask of `p < 3` or `p` even
(`ltA_k`, `evenMaskOf_k`, `orr`) for `selC_k`; the outputs are stored under
the slot `kOk` (`storeA_ok`'s `sMsk := kOk`), and the status is `kOk`'s low
bit in `x0` (`ldh .x3 kOk, movi .x4 1, and x0`). The register frame is
`Keep kRegs s t` (there are no saved registers to restore).

## After A, B and C: the front to `smallMask`, and the code (`Main.lean`, `Code.lean`)

```lean
/-- `Main.lean`: from `KPrimes` to `KFront` (x86's `front_k` after
`decTo`: `lcm_k`, `dPart_k`, `smallMask_k`, with `KLens.P_lt`, `Q_lt`,
`E_lt`, `L_lt` from `Front.lean`). -/
theorem front2_k {I : KIn} {s₀ s : State} (h : KPrimes I s₀ s) (L : KLens I) :
    WP isa (seqs (lcmPart ++ ([dPart] ++ smallMask))) s (KFront I s₀)

/-- `Code.lean`. -/
theorem code_eq : code = seqs (([.block (entry ++ VG.Impl.Rsa.AArch64.Keys.head)] : List (Prog isa)) ++
    ((loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ (([.block [sth .x3 kEv]] : List (Prog isa)) ++
      (order ++ (decTo aPm aPa ++ decTo aQm aQa)))))) ++
    ((lcmPart ++ ([dPart] ++ smallMask)) ++ ([.ite (.nonzero .x .x15) (zeros 2) keyPart] : List (Prog isa)))))

theorem keyPost_of {s t : State} (c : KCtx s) (R : OutsRes (keyIn s) t.mem (t.gpr .x0)) : keyPost s t

theorem keyCode_wp (s : State) (h : keyPre s) : WP isa code s fun t => abiPreserved s t ∧ keyPost s t

theorem keyCode_correct (s : State) (h : keyA.pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ keyA.post s s'
```

`keyCode_wp`: `keyCtx_of`, `keyStart_k`, `front_k`, `front2_k`, then
`WP.ite` on `eval_nonzero` of `x15 = mask (d small && ok)` (`KFront.x15`):
`zerosPart_k` with `outsRes_zeros`, or `keyPart_k` with `outsRes_tail`;
`abiPreserved_of_keep ((KFront.ks.keep.trans post.keep).mono (by decide))`.
`keyOuts s = outsL (keyIn s)` by `c.x1` (`n_len = 2 p_len`), and
`keyRes s` is `keyOp (keyIn s).pl (keyIn s).eb (keyIn s).pb (keyIn s).qb`
by `rfl`.

Then constant time (x86's `CT*.lean`, with `KG F p s := ∃ I s₀, I.pub = p.q ∧
I.st = p.st ∧ KS I s₀ s ∧ KLens I ∧ KOuts I ∧ F I s`; the AArch64 taint
helpers are in `Proof/Rsa/AArch64/CTBase.lean` and the candidate's
`CTBase.lean`), `Verified.lean` (`Verified.of_correct keyCode_correct … key_implies`)
and the registration in `Artifacts/RsaKeyGen/AArch64.lean`.

## Checking

From `lean/`: `lake build +VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Shared`
(and `.Front`) once, then `lake env lean <file>` on a new file (with the
lakefile's `weak.*` options to match `lake build`); check the exit code
(137 is out of memory). Then `python3 ci/check_lean_speed.py` and
`python3 ci/check_lean_imports.py` from the repository's root.
