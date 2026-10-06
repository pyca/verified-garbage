# `vg_rsa_keygen_key` on AArch64: plan of the constant-time proof

The correctness proof is `PLAN.md`'s; this is the relational constant time
(two runs), mirroring x86-64's `Proof/RsaKeyGen/X86_64/Key/CT*.lean`. Done
(do not edit; add new `CT*.lean` files):

| File | What it gives |
| --- | --- |
| `CTBase.lean` | `KQ`, `KP`, `KIn.pub`, `KIn.st`, `KG`, `NF`, the tools below, `Stab` and its facts (`EvOK`, `KokM`, `X15M`, `Zero`, `TopZ`, `AvIs`, `AvEq`, `PF`) |
| `CTUnits.lean` | `zeroA_ct0/_ct`, `zeroAZ_ct`, `copyA_ct0/_ct`, `zc_ct`, `constA_ct0/_ct`, `ltA_ct`, `geA_ct`, `eqMask_ct`, `neMask_ct`, `oddMaskOf_ct`, `evenMaskOf_ct`, `selC_ct0/_ct`, `setOne_ct`, `one_ct`, `divmod_ct`, `inverse_ct0/_ct` (and the register lists `zRegs`, `cpRegs`, `cRegs`, `ltRegs`, `eqRegs`, `omRegs`, `emRegs`, `selRegs`, `soRegs`, `dvRegs`) |
| `CTFront.lean` | `KRel`, `start_ct`, `loadA_ct0`, `loadE_ct0`, `loads_ct0`, `order_ct0`, `decTo_ct0`, `frontL`, `front_ct`, `KG.primes`, `kpubOf`, `kpubOf_eq`, `keyCT_of` |
| `CTLcm.lean` | `mulTo_ct0`, `phi_ct`, `shrHalf_k`, `halfIf_ct0/_ct`, `twoStep_ct0`, `twos_ct`, `stOk_k`, `stOk_ct`, `ldOk_ct`, `invStart_ct`, `gcdUV_ct`, `LF`, `lcmPart_ct` |

Every statement and equation below was elaborated against these files (with
the proofs left out), and every taint check named below was run with
`taint_decide`: all succeed.

## The relation

```lean
structure KQ where   -- the public inputs
  B : Addr; Z : Nat; pl : Nat; pN pD pP pQ pDp pDq pQi pE : Addr; el : Nat; eb : List Byte; Wr : List Region
structure KP where q : KQ; st : Nat   -- and the status
abbrev KIn.st (I : KIn) : Nat := Spec.RsaKeyGen.keyStatus (Spec.RsaKeyGen.keyOp I.pl I.eb I.pb I.qb)
def KG (F : KIn → State → Prop) (p : KP) (s : State) : Prop :=
  ∃ I s₀, I.pub = p.q ∧ I.st = p.st ∧ KS I s₀ s ∧ KLens I ∧ KOuts I ∧ F I s
```

`Two (KG F)` relates two runs (same `p`, same `sp`). `I.E = os2ip p.q.eb`
(`KIn.pub_E`), `I.W = p.q.W` (`KIn.pub_W`).

The stages so far: `start_ct : RelCT isa (Two KRel) (.block (entry ++ Keys.head)) (Two (KG NF))`,
`front_ct : RelCT isa (Two (KG NF)) (seqs frontL) (Two (KG PF))`,
`lcmPart_ct : RelCT isa (Two (KG PF)) (seqs lcmPart) (Two (KG LF))`, where

```lean
def PF (I : KIn) (t : State) : Prop :=   -- `KPrimes` but for `KS`, and the top words of `p − 1`, `q − 1` zero
  av I t.mem aPa = I.P ∧ av I t.mem aQa = I.Q ∧ av I t.mem aPm = I.P - 1 ∧ av I t.mem aQm = I.Q - 1 ∧
    EvOK I t ∧ TopZ aPm I t ∧ TopZ aQm I t
abbrev LF : KIn → State → Prop := fun I t => PF I t ∧ av I t.mem aL = I.L
```

`PF.frame (hok) (hPa hQa hPm hQm hEv : … ∉ cs) hZ (h : PF I s) (f : KF I.B I.W cs s.mem t.mem) : PF I t`
carries `PF` across any piece that changes none of `aPa`, `aQa`, `aPm`,
`aQm`, `kEv` (all of `csL`, `csD`, `csQ`, `csC`, `[.arr aC]`, `[.arr aQt]`,
`[.hdr kOk]` qualify; every `hok`/`∉` is `by decide`).

## The tools (all in `CTBase.lean`)

The taint analysis tracks registers only; every load (including `ws`'s
`ldh .x12 sW, ldh .x11 sStride`) gives a secret. So each piece that starts
with `ws` is checked from `x0`, `x12`, `x11` pinned by correctness, and the
pins need `KS` (`Ws`) at its start: between two pieces, the relation must be
`Two (KG G)` for facts `G` that make the next piece's correctness lemma
apply (to get `KS` after it).

* `kg_ws0 ht : RelCT (Two (KG F)) (.seq (.block (ws ++ rest)) body) True`,
  `kg_wsb0 ht` (a block): taint only, `ht` on `rest`/`body` from
  `[.x0, .x12, .x11]`.
* `kg_ct hct hw : RelCT (Two (KG F)) c (Two (KG G))` from a taint-only
  `hct` and correctness `hw : ∀ I s₀ s, KS I s₀ s → KLens I → F I s → WP isa c s fun t => KS I s₀ t ∧ G I t`.
  `kg_ws`, `kg_wsb`, `kg_x0` (code checked from `x0` alone) combine both.
* `kg_then h₁ hw₁ h₂ : RelCT (Two (KG F)) (.seq c₁ c₂) True` (facts between
  from `c₁`'s correctness), `kg_app0` (the same for `seqs (a ++ b)`),
  `kg_split` (and the facts after from the whole's correctness).
  The stages use this: a taint-only chain, then `kg_ct chain whole_k`.
* `kg_blk_ws0 ht₁ hw₁ ht₂ : RelCT (Two (KG F)) (.block (l₁ ++ (ws ++ rest))) True`
  for a block that reloads `ws` in its middle (`l₁` checked from `x0`, with
  correctness `hw₁` giving `KS`), `kg_blk_ws_seq0` when code follows.
* `kg_ite hc ht he` for `.ite cond th el`, with `hc` from
  `kg_zero_eq (g := …) hg` / `kg_nonzero_eq (g := …) hg`, where
  `hg : ∀ I t, F I t → t.gpr r = g ⟨I.pub, I.st⟩`; the branches start from
  `KG fun I t => F I t ∧ isa.eval cond t = some true` (`false`).
* `rs_app ha hb h₁ h₂` splits `seqs (a ++ b)` (any relations);
  `RelCT.drop (Q := …) h` forgets a postcondition; `two_kg`, `KG.imp`,
  `KG.imp'` change the facts.
* `Stab F cs rs`, `stab_*`, `Stab.mono`, `Stab.sub` (from `allR = mmRegs`),
  `stab_and`, as x86-64's.
* `kg_regs` for a block that changes registers alone (checked from `x0`).

Write lists next to `++` with ascriptions (`([…] : List Instr)`,
`([…] : List (Prog isa))`); `seqs [c] = c` and `seqs [a, b] = .seq a b` are
definitional (`show RelCT isa _ (seqs [zeroA o, copyA o j]) _ from …`).
`warningAsError` makes unused simp arguments and unused names errors.

## Remaining files

Every new file starts with the `namespace`/`open`s of `CTLcm.lean`, plus
`open VG.Proof.MlKem.AArch64 (Keep eval_zero eval_nonzero)` where needed.

### `CTD.lean`: `dPart` (imports `CTLcm`, `Key.DPart`)

```lean
abbrev DF : KIn → State → Prop := fun I t => PF I t ∧ DRes I I.E I.L t.mem

theorem dZero_ct0 : RelCT isa (Two (KG NF)) (.block dZero) fun _ _ => True :=
  two_taint [.x0] (pins_kg NF) (by taint_decide)          -- checked
theorem dOne_ct0 : RelCT isa (Two (KG NF)) (seqs dOne) fun _ _ => True
theorem dOdd_ct0 : RelCT isa (Two (KG fun I t => EvOK I t ∧ I.E % 2 = 1)) (seqs dOdd) fun _ _ => True
theorem dEven_ct0 : RelCT isa (Two (KG EvOK)) (seqs dEven) fun _ _ => True
theorem dPart_ct0 : RelCT isa (Two (KG EvOK)) dPart fun _ _ => True

theorem dPart_ct : RelCT isa (Two (KG LF)) dPart (Two (KG DF)) :=      -- checked, given dPart_ct0
  kg_ct (dPart_ct0.mono (fun _ _ h => two_kg (fun _ _ h => h.1.2.2.2.2.1) h) fun _ _ h => h)
    fun I _ s h L ⟨hf, hL⟩ => WP.mono (dPart_k h L.E_lt hf.2.2.2.2.1 hL L.L_lt) fun _ ⟨ht, f, d⟩ =>
      ⟨ht, PF.frame (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.hZ hf f, d⟩
```

`dPart_ct0`, following `dPart_k`'s proof (`DPart.lean`):

1. `.block [ldh .x3 kEv]`: `kg_x0 (G := fun I t => EvOK I t ∧ t.gpr .x3 = BitVec.ofNat 64 I.E)`,
   correctness by `WP.keep [.x3]` and `brun [h.ws.x0, hdr_enc (show kEv < 32 by decide), hld, hev]`
   as in `dPart_k`.
2. `kg_ite (kg_zero_eq (g := fun p => BitVec.ofNat 64 (Spec.Rsa.os2ip p.q.eb)) fun _ _ h => h.2)`
   (`I.pub.eb = I.eb` is `rfl`): `e = 0` → `dZero_ct0` (`.mono` with `two_kg`).
3. Else `.seq (.block [.subImm .x .x3 .x3 1]) …`: `kg_x0` to
   `x3 = ofNat (E − 1)` (`E ≠ 0` from the branch: `eval_zero`,
   `ofNat_beq_zero L.E_lt`; `VG.Offset.ofNat_sub_ofNat`), then `kg_ite
   (kg_zero_eq (g := fun p => BitVec.ofNat 64 (Spec.Rsa.os2ip p.q.eb - 1)))`:
   `dOne_ct0`, or
4. `.seq (.block [ldh .x3 kEv, movi .x4 1, .logic .and .x .x3 .x3 .x4]) …`:
   `kg_x0` to `x3 = ofNat (E % 2)` (as `dPart_k`), then `kg_ite
   (kg_nonzero_eq (g := fun p => BitVec.ofNat 64 (Spec.Rsa.os2ip p.q.eb % 2)))`:
   `dOdd_ct0` (`E % 2 = 1` from the branch) or `dEven_ct0`.

`dOne_ct0` (`dOne_eq : dOne = constA 1 ++ (neMask aL aC ++ ([.block [sth .x15 kOk], zeroA aDd, .block (setOneA aDd)] : List (Prog isa)))`,
by `simp only [dOne, List.append_assoc]`): `constA_ct 1 (by decide) (stab_nf _ _)`,
`neMask_ct (G := X15M)`, `stOk_ct (F := NF) (stab_nf _ _)` (relation
`NF ∧ X15M`: use `.mono`/`two_kg`), `zeroAZ_ct (F := NF)`,
`setOne_ct (G := NF)`.

`dOdd_ct0` (`dOdd_eq`, `DOdd.lean`): a taint-only chain (`rs_app`, each
piece `kg_ct`'d with its correctness for the next piece's facts):

* `loadEv` (`loadEv_eq : seqs loadEv = .seq (zeroA aE) (.block (ws ++ (base aE .x16 ++ ([ldh .x3 kEv, st .x3 .x16] : List Instr))))`):
  `kg_then (zeroA_ct0 …) (zeroA_k) (kg_wsb0 (by taint_decide))`, facts after
  from `loadEv_k h L.E_lt hev` (keep `EvOK`, `I.E % 2 = 1` by `stab_ev`/frames).
* `zeroA aQt`, `copyA aQt aL`, `divmod aQt aR aE aT` (`zeroA_ct`, `copyA_ct`,
  `divmod_ct` with `Stab` of the carried facts), `zeroA aU`, `copyA aU aR`
  (`zc_ct`: `TopZ aU`).
* `invFrom aE = [zeroA aV, copyA aV aE, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂]`:
  `zeroA_ct` then `invStart_ct (o := aV) (a := aE)` → `AvEq aV aE ∧ AvIs aX₁ 1 ∧ AvIs aX₂ 0`;
  `inverse_ct` (`InvS aU aV aX₁ aX₂ aE`: `TopZ aU`, the `AvEq`, `1`, `0`).
* `lGe2` (`lGe2_eq : lGe2 = constA 2 ++ (geA aL aC ++ ([.block [sth .x15 kOk]] : List (Prog isa)))`):
  `constA_ct`, `geA_ct (G := … ∧ X15M)`, `stOk_ct` → `KokM`.
* `gcdIsOne` (`gcdIsOne_eq : gcdIsOne = constA 1 ++ (eqMask aV aC ++ ([.block [ldh .x3 kOk, .logic .and .x .x15 .x15 .x3, sth .x15 kOk]] : List (Prog isa)))`):
  as a unit `gcdIsOne_ct : RelCT (Two (KG fun I t => F I t ∧ KokM I t)) (seqs gcdIsOne) (Two (KG fun I t => F I t ∧ KokM I t))`
  for `hF : Stab F [.arr aC, .hdr kOk] allR`: `kg_ct` of the taint chain
  (`constA_ct0`, `eqMask_ct (G := NF)`, `two_taint [.x0] … (by taint_decide)`
  on the last block) with `gcdIsOne_k` (`qinvPart` and `dEven` use it too).
* The `minv` block: `dOddBlk_eq : [ldh .x3 kEv] ++ minv ++ ws ++ base aX₂ .x16 ++ base aR .x17 ++ ([…] : List Instr) = (([ldh .x3 kEv] : List Instr) ++ minv) ++ (ws ++ (base aX₂ .x16 ++ (base aR .x17 ++ ([…] : List Instr))))`
  (`simp only [List.append_assoc]`); `kg_blk_ws0` with `l₁ = [ldh .x3 kEv] ++ minv`
  (correctness: the load as in `dOddC_ok`, then `minvX4_ok` with
  `I.E % 2 = 1`; `KS` by `h.regs`). The next piece needs `KS` after the whole
  block: `dOddC_ok` needs the values; write `dOddCblk_k : KS I s₀ s → EvOK I s → I.E % 2 = 1 → WP isa (.block (…)) s (KS I s₀)`
  from `dOddC_ok`'s proof with `Q := fun t => t.mem = s.mem` (no values),
  and `kg_ct (kg_blk_ws0 …) dOddCblk_k`.
* `zeroA aDd` (`zeroA_ct`), and last `.block (ws ++ base aDd .x8 ++ ([st .x10 .x8] : List Instr) ++ base aQt .x9 ++ ([movi .x7 0] : List Instr))`
  with `mulAddRow`: `kg_ws0` on `.seq (.block (base aDd .x8 ++ (([st .x10 .x8] : List Instr) ++ (base aQt .x9 ++ ([movi .x7 0] : List Instr))))) mulAddRow`
  (after a `simp only [List.append_assoc]` rewrite of the block).

`dEven_ct0` (`dEven_eq`, `DEven.lean`): `loadEv` as above, `divisorOf aL`
(`divisorOf_ct` below), `zeroA aQt`, `copyA aQt aE`, `divmod aQt aR aM aT`,
`zc_ct` (`aU`, `aR`), `constA 3`, `ltA aL aC (G := … ∧ X15M)`, the mask
block (`dEvenBlk_eq : ([mov .x10 .x15] : List Instr) ++ evenMaskOf aL ++ ([.logic .orr .x .x15 .x15 .x10, mov .x10 .x15] : List Instr) ++ notMask ++ ([sth .x15 kOk, mov .x15 .x10] : List Instr) = ([mov .x10 .x15] : List Instr) ++ (ws ++ (base aL .x16 ++ (([ld .x3 .x16, movi .x4 1, .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1] : List Instr) ++ (([.logic .orr .x .x15 .x15 .x10, mov .x10 .x15] : List Instr) ++ (notMask ++ ([sth .x15 kOk, mov .x15 .x10] : List Instr))))))`,
by `simp only [evenMaskOf, List.append_assoc]`; `kg_ct (kg_blk_ws0 (l₁ := [mov .x10 .x15]) …) dEvenMask_k`
→ `KokM ∧ X15M`), `zeroA aM`, `copyA aM aL`, `selC_ct` (`X15M` survives
`zRegs`, `cpRegs`), `invFrom aM` (`zeroA_ct`, `invStart_ct (o := aV) (a := aM)`),
`inverse_ct`, `gcdIsOne_ct`, `zeroA aDd`, `copyA aDd aX₂` (last: `copyA_ct0`).

`divisorOf_ct {F} (hj : j < 16) (hjM : j ≠ aM) (hjC : j ≠ aC) (hF : Stab F [.arr aM, .arr aC] allR) : RelCT isa (Two (KG F)) (seqs (divisorOf j)) (Two (KG F))`
(taint checks as parameters, `j` varies): `divisorOf_eq2 j : divisorOf j = [zeroA aM, copyA aM j] ++ (constA 0 ++ (eqMask j aC ++ ([.block (ws ++ (base aM .x16 ++ ([ld .x3 .x16, movi .x4 1, .logic .and .x .x4 .x15 .x4, .logic .orr .x .x3 .x3 .x4, st .x3 .x16] : List Instr)))] : List (Prog isa))))`;
chain `zeroA_ct0`, `copyA_ct0`, `constA_ct0`, `eqMask_ct (G := NF)`,
`kg_wsb0`, all `NF` between (`zeroA_k`, `copyA_k`, `constA_k`, `eqMask_k`
give `KS`); post `divisorOf_k`.

### `CTSmall.lean`: `smallMask` (imports `CTD`, `Key.Small`)

```lean
abbrev FF : KIn → State → Prop := fun I t => PF I t ∧ DRes I I.E I.L t.mem ∧
  ∃ ok : Bool, word t.mem I.B (8 * kOk) = mask ok ∧ ((∃ d, Spec.Rsa.inverse I.E I.L = some d) ↔ ok = true) ∧
    t.gpr .x15 = mask (decide (av I t.mem aDd ≤ 2 ^ (8 * I.pl)) && ok)

theorem FF.front {I : KIn} {s₀ t : State} (h : KS I s₀ t) (hf : FF I t) : KFront I s₀ t :=   -- checked
  ⟨h, hf.1.1, hf.1.2.1, hf.1.2.2.1, hf.1.2.2.2.1, hf.1.2.2.2.2.1, hf.2.1, hf.2.2⟩

theorem smallMask_eq : smallMask = constA 1 ++ (([.block (ws ++ (base aC .x16 ++ ([.lsr .x .x3 .x12 1,
    .lsl .x .x3 .x3 3, .add .x .x16 .x16 .x3, movi .x3 1, st .x3 .x16] : List Instr)))] : List (Prog isa)) ++
    (ltA aDd aC ++ ([.block [ldh .x3 kOk, .logic .and .x .x15 .x15 .x3]] : List (Prog isa)))) := by
  simp only [smallMask, List.append_assoc]                                                   -- checked

theorem smallBlk_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (.block (ws ++ (base aC .x16 ++ ([.lsr .x .x3 .x12 1, .lsl .x .x3 .x3 3, .add .x .x16 .x16 .x3, movi .x3 1,
      st .x3 .x16] : List Instr)))) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aC] s.mem t.mem
  -- `smallMask_k`'s middle (`wsBase16_ok`, `WP.keep [.x3, .x16]`, `KF.arr1`), for any contents of `[aC]`

theorem smallMask_ct : RelCT isa (Two (KG DF)) (seqs smallMask) (Two (KG FF))

/-- The branch's mask is the status' (x86-64's `front_zf`, with `keyOp_inr_k`, `Res.lean`). -/
theorem FF.x15 {I : KIn} {t : State} (h : FF I t) : t.gpr .x15 = mask (decide (I.st = 2))
```

`smallMask_ct`: `kg_ct` of the chain `constA_ct 1 (stab_nf _ _)`,
`kg_then (kg_wsb0 …) smallBlk_k`, `ltA_ct (G := NF)`, `two_taint [.x0]` on
the last block; post from `smallMask_k h L.W hok` (`L.W : I.W = 2 * (I.pl / 8)`,
`hok` from `DRes`; `64 * (I.pl / 8) = 8 * I.pl` by `L.pl8`), `PF.frame` and a `DRes` frame
across `[.arr aC]` (its `kOk` word and `av aDd`; `KF.word`, `KF.av`).

### `CTOut.lean`: the zeros and the stores (imports `CTBase`, `Key.Tail`, `Rsa.AArch64.CvCTCode`)

From the stores on, `KS` no longer holds (memory outside the working space
changes), so the relation is x86-64's `EG`:

```lean
def EG (M : KIn → State → Prop) (p : KP) (s : State) : Prop :=
  ∃ I, I.pub = p.q ∧ Ws s I.B I.Z I.W ∧ KArgs s.mem I ∧ s.wr = I.Wr ∧ KLens I ∧ KOuts I ∧ M I s
theorem pins_EG (M) : Pins (EG M) [.x0]
theorem EG.of_kg {M : KIn → State → Prop} {p : KP} {s : State} (h : KG M p s) : EG M p s
abbrev OutHdr (sPtr sLen : Nat) (ptr : KQ → Addr) (len : KQ → Nat) : Prop :=   -- as x86-64's
abbrev HdrStab (M : KIn → State → Prop) : Prop :=                               -- as x86-64's
theorem zeroOutK_ct {M} (hM : HdrStab M) {sPtr sLen} (hP : sPtr < 32) (hL : sLen < 32) (ptr : KQ → Addr)
    (len : KQ → Nat) (hA : OutHdr sPtr sLen ptr len) {hc} (ht : (taint.check (Taint.ofRegs [.x0])
      (.block [ldh .x1 sPtr, ldh .x2 sLen, movi .x3 0]) hc).isSome = true) :
    RelCT isa (Two (EG M)) (zeroOut sPtr sLen) (Two (EG M))
theorem storeAK_ct {j sPtr sLen} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : KQ → Addr) (len : KQ → Nat)
    (hA : OutHdr sPtr sLen ptr len) {hc} (ht : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base j .x8 ++
      ([ldh .x1 sPtr, ldh .x9 sLen, .add .x .x1 .x1 .x9, ldh .x15 kOk] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (EG KokM)) (seqs (storeA j sPtr sLen kOk)) (Two (EG KokM))
theorem outN … outQi   -- `OutHdr` of the seven outputs, from `KArgs` (x86-64's)
theorem zeros2_ct : RelCT isa (Two (EG NF)) (zeros 2) fun _ _ => True
theorem outputs_ct : RelCT isa (Two (EG KokM)) (seqs outputs) fun _ _ => True
```

* `zeroOutK_ct`: `CvCTCode.lean`'s `zeroOut_ct` (`pin_ct [.x0] [.x1, .x2] (fun p => zoVal (ptr p.q) (len p.q))`,
  the loop `countLoop .x2 [.strb .x3 .x1 0, .addImm .x .x1 .x1 1]` from
  `[.x1, .x2]`), correctness `zeroOut_ok` (`CvFail.lean`) and x86-64's `EG.after`.
* `storeAK_ct`: `storeA_eq : seqs (storeA j sPtr sLen kOk) = .seq (.block (ws ++ base j .x8 ++ ([ldh .x1 sPtr, ldh .x9 sLen, .add .x .x1 .x1 .x9, ldh .x15 kOk] : List Instr))) storeBE`
  is `rfl`; `pin_ct [.x0] [.x0, .x8, .x1, .x9] (fun p => soVal p.q.B (off p.q.B (slot p.q.W j)) (ptr p.q) (len p.q))`
  (`soVal`, `CvCTMain.lean`), the pins from `storeBlkK_ok` (`CvCTMain`'s
  `storeBlk_ok` with `ldh .x15 kOk` for `ldh .x15 Public.sMask`), `storeBE`
  from `[.x0, .x8, .x1, .x9]`, correctness `storeK_ws` (`Out.lean`).
* `zeros2_ct`: `zeros 2 = seqs [zeroOut kNo kNl, …, zeroOut kQi kPl, .block [movi .x0 2]]`;
  last `two_taint [.x0] (pins_EG NF) (by taint_decide)`.
* `outputs_ct`: `outputs = storeA aQt kNo kNl kOk ++ (… ++ ([.block retOk] : List (Prog isa)))`
  (`simp only [outputs, List.append_assoc]`), last `two_taint [.x0]`.

### `CTTail.lean`: `keyPart` (imports `CTD`, `CTOut`, `Key.Tail`)

```lean
abbrev TF : KIn → State → Prop := fun I t => PF I t ∧ KokM I t

theorem qinvPart_ct : RelCT isa (Two (KG TF)) (seqs qinvPart) (Two (KG TF))
theorem crtPart_ct : RelCT isa (Two (KG TF)) (seqs crtPart) (Two (KG TF))
theorem nPart_ct : RelCT isa (Two (KG TF)) (seqs nPart) (Two (KG TF))
theorem finalMask_ct : RelCT isa (Two (KG TF)) (.block finalMask) (Two (KG TF))

theorem keyPart_ct : RelCT isa (Two (KG TF)) keyPart fun _ _ => True := by       -- checked, given the above
  rw [keyPart]
  simp only [List.append_assoc]
  refine rs_app (by simp [qinvPart]) (by simp [crtPart, divisorOf]) qinvPart_ct ?_
  refine rs_app (by simp [crtPart, divisorOf]) (by simp [nPart]) crtPart_ct ?_
  refine rs_app (by simp [nPart, mulTo]) (by simp) nPart_ct ?_
  refine rs_app (by simp) (by simp [outputs, storeA]) finalMask_ct ?_
  exact outputs_ct.mono (fun _ _ ⟨p, ⟨I₁, _, e₁, _, k₁, L₁, O₁, _, m₁⟩, ⟨I₂, _, e₂, _, k₂, L₂, O₂, _, m₂⟩, hsp⟩ =>
    ⟨p, ⟨I₁, e₁, k₁.ws, k₁.args, k₁.wr, L₁, O₁, m₁⟩, ⟨I₂, e₂, k₂.ws, k₂.args, k₂.wr, L₂, O₂, m₂⟩, hsp⟩)
    fun _ _ h => h
```

Each `…_ct` is `kg_ct` of a taint-only chain and the whole's correctness
(`qinvPart_k`, `crtPart_k`, `nPart_k`, `finalMask_k`), `PF.frame` across
`csQ`, `csC`, `[.arr aQt]`, `[.hdr kOk]`, and `KokM` from the new `kOk`
word (or kept: `crtPart`, `nPart` do not touch it).

* `qinvPart` (`qinvPart_eq`, `Qinv.lean`): `zc_ct` (`aU`, `aQa` → `TopZ aU`),
  `constA_ct 3`, `ltA_ct (G := … ∧ X15M)`, the mask block (`qinvBlk_eq : ([mov .x10 .x15] : List Instr) ++ (evenMaskOf aPa ++ ([.logic .orr .x .x15 .x15 .x10] : List Instr)) = ([mov .x10 .x15] : List Instr) ++ (ws ++ (base aPa .x16 ++ (([ld .x3 .x16, movi .x4 1, .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1] : List Instr) ++ ([.logic .orr .x .x15 .x15 .x10] : List Instr))))`;
  `kg_ct (kg_blk_ws0 …)` with a lemma from `qinvPart_k`'s proof for the
  block: `KS`, `X15M`), `zeroA aM`, `copyA aM aPa`, `selC_ct`, `invFrom aM`,
  `inverse_ct`, `gcdIsOne_ct`.
* `crtPart` (`crtPart_eq2 : crtPart = divisorOf aPm ++ (([zeroA aU, copyA aU aDd, divmod aU aV aM aT, zeroA aX₁, copyA aX₁ aV] : List (Prog isa)) ++ (divisorOf aQm ++ ([zeroA aU, copyA aU aDd, divmod aU aV aM aT] : List (Prog isa))))`):
  `divisorOf_ct`, `zeroA_ct`, `copyA_ct`, `divmod_ct`; post `crtPart_k h rfl rfl rfl`.
* `nPart = mulTo aQt aPa aQa`: `mulTo_ct0` and `nPart_k h L.W hf.1.1 hf.1.2.1 L.P_lt L.Q_lt`
  (`hf : TF I s`; `KLens.P_lt`, `Q_lt` are in `Key.Front`).
* `finalMask` (`finalMask_eq3 : finalMask = (ws ++ (base aQt .x16 ++ finTop)) ++ ((ws ++ (base aPa .x16 ++ (([movi .x7 0, ld .x3 .x16] : List Instr) ++ (oddMask ++ finAnd)))) ++ (ws ++ (base aQa .x16 ++ (([movi .x7 0, ld .x3 .x16] : List Instr) ++ (oddMask ++ (finAnd ++ (finE1 ++ (finE2 ++ ((carryMask ++ finAnd) ++ (finE3 ++ (borrowMask ++ finSt)))))))))))`,
  by `rw [finalMask_eq]; simp only [oddMaskOf, List.append_assoc, List.cons_append, List.nil_append]`):
  three blocks reloading `ws`; `RelCT.block_append` twice, each part
  `kg_wsb0`, the facts between from `KS` after each of the first two (a
  lemma for `ws ++ (base aQt .x16 ++ finTop)`: memory unchanged, registers
  `⊆ mmRegs`; `oddMaskOf_k` then `finAnd` for the second), post
  `finalMask_k h rfl hf.1.1 hf.1.2.1 L.E_lt hf.1.2.2.2.2.1 hok` (`hf : TF I s`, `hf.2 = ⟨_, hok⟩`).

### `CTCode.lean`: the code (imports `CTSmall`, `CTTail`)

```lean
theorem code_ct_eq : code = seqs (([.block (entry ++ VG.Impl.Rsa.AArch64.Keys.head)] : List (Prog isa)) ++
    (frontL ++ (lcmPart ++ (([dPart] : List (Prog isa)) ++ (smallMask ++
      ([.ite (.nonzero .x .x15) (zeros 2) keyPart] : List (Prog isa))))))) := by
  simp only [code, frontL, List.append_assoc]                                                -- checked

theorem branch_ct : RelCT isa (Two (KG FF)) (.ite (.nonzero .x .x15) (zeros 2) keyPart) fun _ _ => True :=
  kg_ite (kg_nonzero_eq (g := fun p => mask (decide (p.st = 2))) fun _ _ hf => hf.x15)        -- checked
    (zeros2_ct.mono (fun _ _ ⟨p, h₁, h₂, hsp⟩ => ⟨p, EG.of_kg …, EG.of_kg …, hsp⟩) fun _ _ h => h)
    (keyPart_ct.mono (fun _ _ h => two_kg (fun _ _ ⟨⟨hp, _, ok, hok, _⟩, _⟩ => ⟨hp, ok, hok⟩) h) fun _ _ h => h)

theorem keyCode_ct : RelCT isa (Two KRel) code fun _ _ => True := by                         -- checked
  rw [code_ct_eq]
  refine rs_app (by simp) (by simp [frontL, loadA]) start_ct ?_
  refine rs_app (by simp [frontL, loadA]) (by simp [lcmPart, phi, mulTo]) front_ct ?_
  refine rs_app (by simp [lcmPart, phi, mulTo]) (by simp) lcmPart_ct ?_
  refine rs_app (by simp) (by simp [smallMask, constA]) dPart_ct ?_
  exact rs_app (by simp [smallMask, constA]) (by simp) smallMask_ct branch_ct

theorem keyCode_constantTime : ConstantTime isa keyA.pre keyA.pub code := keyCT_of keyCode_ct  -- checked
```

(`EG.of_kg` to `EG NF` drops the facts: `⟨I, he, hk.ws, hk.args, hk.wr, L, O, trivial⟩`.)
`Verified.lean` then combines `keyCode_correct` (`Code.lean`),
`keyCode_constantTime` and `key_implies`.

## Taint checks run (all succeed with `taint_decide`)

From `[.x0]`: `[ldh .x3 kEv]`, `dZero`, `[.subImm .x .x3 .x3 1]`,
`[ldh .x3 kEv, movi .x4 1, .logic .and .x .x3 .x3 .x4]`,
`[ldh .x3 kEv] ++ minv`, `[ldh .x3 kOk, .logic .and .x .x15 .x15 .x3, sth .x15 kOk]`,
`[mov .x10 .x15]`, `[ldh .x3 kOk, .logic .and .x .x15 .x15 .x3]`,
`ws ++ base aQt .x8 ++ [ldh .x1 kNo, ldh .x9 kNl, .add .x .x1 .x1 .x9, ldh .x15 kOk]`,
`[ldh .x1 kNo, ldh .x2 kNl, movi .x3 0]`, `retOk`, `[movi .x0 2]`.
From `[.x0, .x12, .x11]`: `loadEv`'s block after `ws`, the `minv` block's
part after `ws`, `dOdd`'s last block with `mulAddRow`, `dEven`'s and
`qinvPart`'s mask blocks after `ws`, `divisorOf`'s last block after `ws`,
`smallMask`'s word-setting block after `ws`, the three parts of
`finalMask` after `ws`. From `[.x0, .x8, .x1, .x9]`: `storeBE`. From
`[.x1, .x2]`: `zeroOut`'s loop.
