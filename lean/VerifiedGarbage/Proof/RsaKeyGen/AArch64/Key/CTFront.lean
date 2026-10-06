import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTUnits
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Front
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Entry
import VerifiedGarbage.Proof.Rsa.AArch64.CvCT

/-!
# An RSA key from its primes on AArch64: constant time, the entry, the loads, the order and `p − 1`, `q − 1`

`start_ct`: `entry` and `Keys.head`, from the stack pointer and then from
the working space's base (stack argument 8), which correctness pins to the
public data. The loads take the pointer and the length from the header,
which correctness pins too (`loadA_ct0`, `loadE_ct0`); the rest are pieces
of the key routines. Each stage is checked with no postcondition, the facts
between its parts from their correctness (`kg_app0`), and the facts after
it from the correctness of the whole stage: `loads_k`, `order_k`,
`decTo_k`, and `front_k` for all of them (`front_ct`, to `KG PF`).

`keyCT_of`: runs the contract relates (`keyPub`) have the same public data
(`kpubOf_eq`), so the contract's `ConstantTime` follows from the code's
constant time in `Two KRel`.
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-! ## The entry -/

/-- A state the contract allows, with the public data `p`. -/
def KRel (p : KP) (s : State) : Prop := keyPre s ∧ (keyIn s).pub = p.q ∧ (keyIn s).st = p.st

/-- After `entry`'s first instruction: the working space's base in `x8`. -/
def KC1 (p : KP) (t : State) : Prop :=
  ∃ s, KRel p s ∧ t.gpr .x8 = p.q.B ∧ WP isa (.block (entry.drop 1 ++ VG.Impl.Rsa.AArch64.Keys.head)) t
    (KS (keyIn s) s)

theorem keyEntry_split : entry ++ VG.Impl.Rsa.AArch64.Keys.head = ([.ldrSp .x8 64] : List Instr) ++
    (entry.drop 1 ++ VG.Impl.Rsa.AArch64.Keys.head) := rfl

/-- `entry` and `Keys.head`. -/
theorem start_ct : RelCT isa (Two KRel) (.block (entry ++ VG.Impl.Rsa.AArch64.Keys.head)) (Two (KG NF)) := by
  rw [keyEntry_split]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := KC1) [] (fun _ _ _ _ _ _ hr => by simp at hr)
    (by taint_decide) ?_)
    (two_piece [.x8] (fun p s₁ s₂ ⟨_, _, a₁, _⟩ ⟨_, _, a₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [a₁, a₂]) (by taint_decide)
      fun p t ⟨s, ⟨hpre, he, hst⟩, _, hw⟩ => WP.mono hw fun u hu =>
        ⟨keyIn s, s, he, hst, hu, (keyCtx_of hpre).L, (keyCtx_of hpre).O, trivial⟩))
  intro p s ⟨hpre, he, hst⟩
  have c := keyCtx_of hpre
  have hh : WP isa (.block (([.ldrSp .x8 64] : List Instr) ++ (entry.drop 1 ++ VG.Impl.Rsa.AArch64.Keys.head))) s
      (KS (keyIn s) s) := by
    rw [← keyEntry_split]; exact keyStart_k c
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 64) 64 = stackArg s 8 := rfl
  have ha8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 64) 8 := c.ha 8 (by decide)
  have ho : 64 % 8 = 0 ∧ 64 < 32768 := ⟨rfl, by decide⟩
  refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.x8] (Q := fun t => t.gpr .x8 = stackArg s 8)
    (by brun [exec_ldrSp ho ha8, hB']) (by decide) (by decide) (by decide +kernel))) fun t ⟨hw, h8, _⟩ =>
      ⟨s, ⟨hpre, he, hst⟩, h8.trans (congrArg KQ.B he), hw⟩

/-! ## The loads -/

/-- `loadA j sPtr sLen`, for the number whose pointer and length (functions
of the public inputs) are in the header slots `sPtr` and `sLen`. -/
theorem loadA_ct0 {F : KIn → State → Prop} {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (ptr : KQ → Addr) (len : KQ → Nat)
    (hA : ∀ I s₀ s, KS I s₀ s → word s.mem I.B (8 * sPtr) = ptr I.pub ∧
      word s.mem I.B (8 * sLen) = BitVec.ofNat 64 (len I.pub))
    {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ ([movi .x7 0] : List Instr)))
      zeroAcc) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base j .x8 ++ ([ldh .x1 sPtr, ldh .x2 sLen] :
      List Instr))) hc₂).isSome = true)
    (ht₃ : (taint.check (Taint.ofRegs [.x0, .x8, .x1, .x2]) loadBE hc₃).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (loadA j sPtr sLen)) fun _ _ => True := by
  show RelCT isa _ (.seq (zeroA j) (.seq (.block (ws ++ base j .x8 ++ ([ldh .x1 sPtr, ldh .x2 sLen] :
    List Instr))) loadBE)) _
  refine RelCT.assoc (kpin_seq0 [.x0, .x8, .x1, .x2]
    (fun p : KP => ioVal p.q.B (off p.q.B (slot p.q.W j)) (ptr p.q) (len p.q))
    (RelCT.seq (kg_ct (G := NF) (zeroA_ct0 ht₁) fun I _ s h _ _ => WP.mono (zeroA_k h hj) fun _ ⟨ht, _⟩ =>
      ⟨ht, trivial⟩) (two_taint [.x0] (pins_kg NF) ht₂)) (fun p s h => ?_) ht₃)
  obtain ⟨I, s₀, he, -, hk, -⟩ := h
  rw [← he]
  refine WP.seq (WP.mono (zeroA_k hk hj) fun t ⟨ht, _⟩ => ?_)
  obtain ⟨hp, hl⟩ := hA I s₀ t ht
  exact loadBlk_ok ht.ws hP hL hp hl

/-- `loadA j sPtr sLen` changes array `j`. -/
theorem loadA_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {j sPtr sLen len : Nat} {ptr : Addr} {bs : List Byte}
    (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (hp : word s.mem I.B (8 * sPtr) = ptr)
    (hl : word s.mem I.B (8 * sLen) = BitVec.ofNat 64 len) (hsrc : Src s I.B I.Z ptr bs) (hlen : bs.length = len)
    (hl1 : 1 ≤ len) (hlw : len ≤ 8 * I.W) :
    WP isa (seqs (loadA j sPtr sLen)) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr j] s.mem t.mem :=
  WP.mono (loadA_ok h.ws hj hP hL hp hl hsrc hlen hl1 hlw) fun _ ⟨_, o, _, _, k⟩ =>
    have f := KF.arr1 (B := I.B) (W := I.W) (j := j) o (Nat.le_refl _) (Nat.le_refl _)
    ⟨h.step f (all_mut_arr hj) k, f⟩

/-- `e`'s pointer and length, and the working space's base. -/
def eVal (q : KQ) : Reg → BitVec 64
  | .x0 => q.B
  | .x1 => q.pE
  | .x2 => BitVec.ofNat 64 q.el
  | _ => 0

theorem loadE_eq : seqs (loadE ++ ([.block [sth .x3 kEv]] : List (Prog isa))) =
    .seq (.block [ldh .x1 kE, ldh .x2 kElen, movi .x3 0])
      (.seq (countLoop .x2 [.lsl .x .x3 .x3 8, .ldrb .x4 .x1 0, .add .x .x3 .x3 .x4, .addImm .x .x1 .x1 1])
        (.block [sth .x3 kEv])) := rfl

/-- `e`'s load and its store into `kEv`. -/
theorem loadE_ct0 {F : KIn → State → Prop} :
    RelCT isa (Two (KG F)) (seqs (loadE ++ ([.block [sth .x3 kEv]] : List (Prog isa)))) fun _ _ => True := by
  rw [loadE_eq]
  refine kpin_seq0 [.x0, .x1, .x2] (fun p : KP => eVal p.q) (two_taint [.x0] (pins_kg F) (by taint_decide))
    (fun p s h => ?_) (by taint_decide)
  obtain ⟨I, s₀, he, -, hk, -⟩ := h
  rw [← he]
  have hw := hk.ws
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi => hw.scr.ld (by omega)
  refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = I.pE ∧ t.gpr .x2 = BitVec.ofNat 64 I.el)
    (by brun [hw.x0, hdr_enc (show kE < 32 by decide), hdr_enc (show kElen < 32 by decide), hl kE (by decide),
      hl kElen (by decide), hk.args.e, hk.args.el]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h1, h2⟩, k⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (k.gpr .x0 (by decide)).trans hw.x0
  · exact h1
  · exact h2

/-- The three loads. -/
abbrev loadsL : List (Prog isa) :=
  loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ ([.block [sth .x3 kEv]] : List (Prog isa))))

theorem loads_ct0 : RelCT isa (Two (KG NF)) (seqs loadsL) fun _ _ => True := by
  have pl8 : ∀ {I : KIn}, KLens I → I.pl ≤ 8 * I.W ∧ 1 ≤ I.pl := fun L => by
    have := L.W; have := L.pl1; have := L.pl8; omega
  refine kg_app0 (G := NF) (by simp [loadA]) (by simp [loadA]) (loadA_ct0 (by decide) (by decide) (by decide)
    KQ.pP KQ.pl (fun _ _ _ h => ⟨h.args.pp, h.args.pl⟩) (by taint_decide) (by taint_decide) (by taint_decide))
    (fun I _ s h L _ => WP.mono (loadA_k h (j := aPa) (by decide) (by decide) (by decide) h.args.pp h.args.pl h.p
      L.pbl (pl8 L).2 (pl8 L).1) fun _ ⟨ht, _⟩ => ⟨ht, trivial⟩) ?_
  refine kg_app0 (G := NF) (by simp [loadA]) (by simp [loadE]) (loadA_ct0 (by decide) (by decide) (by decide)
    KQ.pQ KQ.pl (fun _ _ _ h => ⟨h.args.qp, h.args.pl⟩) (by taint_decide) (by taint_decide) (by taint_decide))
    (fun I _ s h L _ => WP.mono (loadA_k h (j := aQa) (by decide) (by decide) (by decide) h.args.qp h.args.pl h.q
      L.qbl (pl8 L).2 (pl8 L).1) fun _ ⟨ht, _⟩ => ⟨ht, trivial⟩) loadE_ct0

/-! ## The order -/

theorem order_eq : order = ltA aPa aQa ++ ([.block (ws ++ (([mov .x14 .x12] : List Instr) ++
    (base aPa .x16 ++ base aQa .x17))), countLoop .x14 cswapBody] : List (Prog isa)) := by
  simp only [order, List.append_assoc]

theorem order_ct0 : RelCT isa (Two (KG NF)) (seqs order) fun _ _ => True := by
  rw [order_eq]
  exact rs_app (by simp [ltA, cmpA]) (by simp) (ltA_ct (G := NF) (by decide) (by decide)
    (fun _ _ _ _ _ _ _ _ => trivial) (by taint_decide)) (kg_ws0 (by taint_decide))

/-! ## Minus one -/

theorem decTo_eq (o j : Nat) : decTo o j = [zeroA o, copyA o j] ++ (constA 0 ++ (neMask j aC ++ (constA 1 ++
    ([.block (ws ++ (([movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] : List Instr) ++ (base o .x16 ++
      (base aC .x17 ++ base o .x8)))), countLoop .x14 subMBody] : List (Prog isa))))) := by
  simp only [decTo, List.append_assoc]

/-- `decTo o j`, with no postcondition. -/
theorem decTo_ct0 {o j : Nat} (ho : o < 16) (hj : j < 16) (hoj : o ≠ j)
    {h₁ h₂ h₃ h₄ h₅ h₆ h₇ : VG.Taint.Hint VG.AArch64.Taint.T}
    (t₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base o .x8 ++ ([movi .x7 0] : List Instr)))
      zeroAcc) h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x16 ++ base o .x17)) copyWords)
      h₂).isSome = true)
    (t₃ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base aC .x8 ++ ([movi .x7 0] : List Instr)))
      zeroAcc) h₃).isSome = true)
    (t₄ : (taint.check (Taint.ofRegs [.x0, .x12, .x11])
      (.block (base aC .x16 ++ ([movi .x3 0, st .x3 .x16] : List Instr))) h₄).isSome = true)
    (t₅ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block ([movi .x9 0, mov .x14 .x12] : List Instr))
      (.seq (.block (base j .x16 ++ base aC .x17)) (.seq (countLoop .x14 xorBody) (.block nonzeroMask)))) h₅).isSome =
      true)
    (t₆ : (taint.check (Taint.ofRegs [.x0, .x12, .x11])
      (.block (base aC .x16 ++ ([movi .x3 1, st .x3 .x16] : List Instr))) h₆).isSome = true)
    (t₇ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (([movi .x7 0, mov .x14 .x12,
      .subs .x .x3 .x7 .x7] : List Instr) ++ (base o .x16 ++ (base aC .x17 ++ base o .x8)))) (countLoop .x14 subMBody))
      h₇).isSome = true) :
    RelCT isa (Two (KG NF)) (seqs (decTo o j)) fun _ _ => True := by
  rw [decTo_eq]
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [zeroA o, copyA o j]) _ from
    RelCT.seq (zeroA_ct ho (stab_nf _ _) t₁) (copyA_ct ho hj hoj (stab_nf _ _) t₂)) ?_
  refine rs_app (by simp [constA]) (by simp [neMask, eqA]) (constA_ct 0 (by decide) (stab_nf _ _) t₃ t₄) ?_
  refine rs_app (by simp [neMask, eqA]) (by simp [constA]) (neMask_ct (G := NF) hj (by decide)
    (fun _ _ _ _ _ _ _ _ => trivial) t₅) ?_
  exact rs_app (by simp [constA]) (by simp) (constA_ct 1 (by decide) (stab_nf _ _) t₃ t₆) (kg_ws0 t₇)

theorem decP_ct0 : RelCT isa (Two (KG NF)) (seqs (decTo aPm aPa)) fun _ _ => True :=
  decTo_ct0 (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)

theorem decQ_ct0 : RelCT isa (Two (KG NF)) (seqs (decTo aQm aQa)) fun _ _ => True :=
  decTo_ct0 (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)

/-! ## The front -/

/-- The front: the loads, the order, `p − 1` and `q − 1`. -/
abbrev frontL : List (Prog isa) :=
  loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++
    (([.block [sth .x3 kEv]] : List (Prog isa)) ++ (order ++ (decTo aPm aPa ++ decTo aQm aQa)))))

theorem frontL_eq : frontL = loadsL ++ (order ++ (decTo aPm aPa ++ decTo aQm aQa)) := by
  simp only [frontL, loadsL, List.append_assoc]

/-- The front leaks the same in runs with the same public data, and leaves
`PF` (`front_k`). -/
theorem front_ct : RelCT isa (Two (KG NF)) (seqs frontL) (Two (KG PF)) := by
  refine kg_ct ?_ fun I _ s h L _ => WP.mono (front_k h L) fun _ ⟨P, _, t1, t2⟩ =>
    ⟨P.ks, P.vP, P.vQ, P.vPm, P.vQm, P.ev, t1, t2⟩
  rw [frontL_eq]
  refine kg_app0 (G := NF) (by simp [loadA]) (by simp [order, ltA, cmpA]) loads_ct0
    (fun I _ s h L _ => WP.mono (loads_k h L) fun _ ⟨ht, _⟩ => ⟨ht, trivial⟩) ?_
  refine kg_app0 (G := NF) (by simp [order, ltA, cmpA]) (by simp [decTo]) order_ct0
    (fun I _ s h _ _ => WP.mono (order_k h) fun _ ⟨ht, _⟩ => ⟨ht, trivial⟩) ?_
  exact kg_app0 (G := NF) (by simp [decTo]) (by simp [decTo]) decP_ct0
    (fun I _ s h _ _ => WP.mono (decTo_k h (o := aPm) (j := aPa) (by decide) (by decide) (by decide) (by decide)
      (by decide)) fun _ ⟨ht, _⟩ => ⟨ht, trivial⟩) decQ_ct0

/-- `KG PF` is `KPrimes`, with words `W` of `p − 1` and `q − 1` zero. -/
theorem KG.primes {p : KP} {s : State} (h : KG PF p s) :
    ∃ I s₀, I.pub = p.q ∧ I.st = p.st ∧ KPrimes I s₀ s ∧ KLens I ∧ KOuts I ∧ atop I s.mem aPm = 0 ∧
      atop I s.mem aQm = 0 := by
  obtain ⟨I, s₀, he, hst, hk, L, O, hf⟩ := h
  exact ⟨I, s₀, he, hst, PF.primes hk hf, L, O, hf.2.2.2.2.2.1, hf.2.2.2.2.2.2⟩

/-! ## From the contract -/

/-- Byte lists with the same values. -/
theorem kbytes_eq_of_toNat : ∀ {a b : List Byte}, a.map (·.toNat) = b.map (·.toNat) → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, kbytes_eq_of_toNat h.2]

/-- The public data of a state. -/
def kpubOf (s : State) : KP := ⟨(keyIn s).pub, (keyIn s).st⟩

/-- Runs that the contract relates (`keyPub`) have the same public data. -/
theorem kpubOf_eq {s₁ s₂ : State} (h₁ : keyPre s₁) (h₂ : keyPre s₂) (hp : keyPub s₁ s₂) :
    KRel (kpubOf s₁) s₂ := by
  obtain ⟨hr, -, ha, hl⟩ := hp
  simp only [keyLeak] at hl
  have hlen : ((Spec.Rsa.bytesAt s₁.mem (arg s₁ 6) (arg s₁ 7).toNat).map (·.toNat)).length =
      ((Spec.Rsa.bytesAt s₂.mem (arg s₂ 6) (arg s₂ 7).toNat).map (·.toNat)).length := by
    simp only [List.length_map, bytesAt_length, ha 7 (by decide)]
  obtain ⟨he, hs⟩ := List.append_inj hl hlen
  simp only [List.cons.injEq, and_true] at hs
  refine ⟨h₂, ?_, hs.symm⟩
  have hwr : s₂.wr = s₁.wr := by
    have w₁ := h₁.2.2.1
    have w₂ := h₂.2.2.1
    rw [w₁, w₂]
    simp only [hr .x0 (by decide), hr .x1 (by decide), hr .x2 (by decide), hr .x3 (by decide), hr .x4 (by decide),
      hr .x5 (by decide), hr .x6 (by decide), hr .x7 (by decide), ha 0 (by decide), ha 1 (by decide),
      ha 2 (by decide), ha 3 (by decide), ha 4 (by decide), ha 5 (by decide), ha 8 (by decide), ha 9 (by decide)]
  simp only [kpubOf, keyIn, KIn.pub, KQ.mk.injEq]
  exact ⟨(ha 8 (by decide)).symm, by rw [ha 9 (by decide)], by rw [hr .x5 (by decide)], (hr .x0 (by decide)).symm,
    (hr .x2 (by decide)).symm, (hr .x4 (by decide)).symm, (hr .x6 (by decide)).symm, (ha 0 (by decide)).symm,
    (ha 2 (by decide)).symm, (ha 4 (by decide)).symm, (ha 6 (by decide)).symm, by rw [ha 7 (by decide)],
    (kbytes_eq_of_toNat he).symm, hwr⟩

/-- The contract's constant time, from that of the code in runs with the same
public data. -/
theorem keyCT_of {c : Prog isa} (h : RelCT isa (Two KRel) c fun _ _ => True) :
    ConstantTime isa keyA.pre keyA.pub c :=
  RelCT.constantTime (h.mono (fun _ _ ⟨h₁, h₂, hp⟩ => ⟨kpubOf _, ⟨h₁, rfl, rfl⟩, kpubOf_eq h₁ h₂ hp, hp.2.1⟩)
    fun _ _ h => h)

end VG.Proof.RsaKeyGen.AArch64.Key
