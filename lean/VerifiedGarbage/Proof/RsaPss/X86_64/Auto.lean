module

public import VerifiedGarbage.Proof.RsaPss.X86_64.Cand
import VerifiedGarbage.Proof.RsaOaep.X86_64.DecLoops
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: every candidate salt length

The loop of `autoBack` over the candidates `c < dbLen` (`cand_ok`, one
step): the state saved at `scratch + oSt2` represents the prefix and the
buffer's first `c` bytes, and the digest at `scratch + oDig` is that of the
prefix and the first `L` bytes once `c > L`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs)
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sCtr sHD oBuf oSt oDig oLh oW oRsa scr lay)
open VG.Proof.RsaOaep.X86_64 (Lay Rep upd ea_sp off_plus nW Here Fns WP.here updF_ok finF_ok sizes inR stBytes
  inR_cons inR_nil keep_cs' cs_disj cpV)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off)
open VG.Proof.HashFns (StreamingOK)

/-- Before the candidate `c`, from the state `u₀` at the loop's entry, whose
view of the working space is `V₀` and of the frame `W₀`: the state saved at
`oSt2` represents `pre` and the buffer's first `c` bytes, the bytes below
`oSt` are unchanged, and the digest is that of `pre` and the buffer's first
`l` bytes if `l < c`. -/
structure CandI (stack : Nat) (e₀ u₀ : State) (T : Spec.HashFns.Streaming) (F S : Addr) (V₀ : Nat → Byte)
    (W₀ : Nat → BitVec 64) (pre : List Byte) (D l c : Nat) (u : State) : Prop where
  L : Lay u F S
  here : Here stack e₀ u F S
  rd : u.rd = u₀.rd
  wr : u.wr = u₀.wr
  cs : ∀ r ∈ calleeSaved, u.gpr r = u₀.gpr r
  rep : ∃ V, Rep u.mem F S V (upd W₀ 19 (BitVec.ofNat 64 c)) ∧ (∀ x < oSt, V x = V₀ x) ∧
    (∀ m : Mem, (∀ i < T.S.stateBytes, m (off S (oSt + i)) = V (oSt2 + i)) →
      T.S.Repr m (off S oSt) (pre ++ (List.range c).map fun i => V₀ (oBuf + i))) ∧
    (∀ i < D, V (oDig + i) = if l < c then (T.S.H.hash (pre ++ (List.range l).map fun i => V₀ (oBuf + i))).getD i 0
      else V₀ (oDig + i))

theorem upd_ne {α : Type} (f : Nat → α) {a k : Nat} (v : α) (h : k ≠ a) : upd f a v k = f k := ifn h _ _

variable {T : Spec.HashFns.Streaming} {Hh : Spec.Mgf1.Hash} (hT : StreamingOK T Hh)
variable {stack : Nat} {e₀ : State} {fi fu ff : Addr}

include hT in
/-- One candidate `c < dbLen`. -/
theorem cand_ok (hF : Fns stack e₀ T fi fu ff) {u₀ : State} {F S : Addr} {V₀ : Nat → Byte}
    {W₀ : Nat → BitVec 64} {pre : List Byte} {D l db c : Nat} (hD : W₀ 39 = BitVec.ofNat 64 D)
    (hDl : T.S.digestBytes = D) (hfn : W₀ 45 = fi ∧ W₀ 46 = fu ∧ W₀ 47 = ff) (hl : W₀ 5 = BitVec.ofNat 64 l)
    (hl64 : l < 2 ^ 64) (hdb : W₀ 44 = BitVec.ofNat 64 db) (hdb1 : db < 1024) (hpl : pre.length = D + 8)
    {u : State} (I : CandI stack e₀ u₀ T F S V₀ W₀ pre D l c u) (hc : c < db) :
    WP isa cand u fun u' => u'.zf = some (decide (c + 1 = db)) ∧ CandI stack e₀ u₀ T F S V₀ W₀ pre D l (c + 1) u' := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hT
  have c1 : oSt = 3072 := rfl
  have c2 : oDig = 3328 := rfl
  have c3 : oBuf = 1024 := rfl
  have c4 : oW = 4096 := rfl
  have c5 : oRsa = 8192 := rfl
  have c7 : oLh = 3392 := rfl
  have c8 : oSt2 = 3712 := rfl
  obtain ⟨V, R, hlow, hsv, hdg⟩ := I.rep
  have L := I.L
  have hh := I.here
  have hw : ∀ k, k ≠ 19 → upd W₀ 19 (BitVec.ofNat 64 c) k = W₀ k := fun k hk => upd_ne _ _ hk
  have hcw : upd W₀ 19 (BitVec.ofNat 64 c) 19 = BitVec.ofNat 64 c := ifp rfl _ _
  have hfn' : upd W₀ 19 (BitVec.ofNat 64 c) 45 = fi ∧ upd W₀ 19 (BitVec.ofNat 64 c) 46 = fu ∧
      upd W₀ 19 (BitVec.ofNat 64 c) 47 = ff :=
    ⟨(hw 45 (by decide)).trans hfn.1, (hw 46 (by decide)).trans hfn.2.1, (hw 47 (by decide)).trans hfn.2.2⟩
  have hD' := (hw 39 (by decide)).trans hD
  unfold cand seqs seqs seqs seqs seqs seqs
  -- The saved state restored.
  refine WP.seq (WP.mono (WP.here rfl hh (copyQ_ok L R (a := oSt2) (b := oSt) (by decide) (by decide)
    (by decide) (by decide) (by decide))) fun u1 ⟨⟨L1, k1, R1⟩, hh1⟩ => ?_)
  have hr1 := hsv u1.mem fun i hi => by
    rw [R1.scr _ (by omega), cpV, ifp ⟨by omega, by omega⟩]; exact congrArg V (by omega)
  -- Finalized to `oLh`.
  unfold finCand
  refine WP.seq (WP.seq (WP.mono (WP.here rfl hh1 (finCandArgs_ok L1 R1 hD' hcw))
    fun u2 ⟨⟨hdi2, hsi2, hdx2, hcx2, hm2, k2⟩, hh2⟩ => ?_))
  have L2 : Lay u2 F S := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  refine WP.mono (finF_ok hT hF hh2 L2 (hm2 ▸ R1) (j := 45) rfl (by decide) hfn'.2.2 (o := oLh)
    (Or.inr (by omega)) hdi2 hdx2 hcx2) fun u3 ⟨L3, rd3, wr3, cs3, R3, hh3, hr3⟩ => ?_
  have hml : (pre ++ (List.range c).map fun i => V₀ (oBuf + i)).length = D + 8 + c := by simp [hpl]
  have hdig := hr3 _ (hm2 ▸ hr1) (by rw [hml]; omega) (by rw [hsi2, hml])
  obtain ⟨V3, R3, hV3, hV3'⟩ := VG.Proof.RsaOaep.X86_64.Rep.ex R3
  -- Selected if `c = l`.
  refine WP.seq (WP.mono (WP.here (by decide) hh3 (selCand_ok L3 R3 hcw ((hw 5 (by decide)).trans hl) (by omega) hl64)) fun u4 ⟨⟨L4, k4, R4⟩, hh4⟩ => ?_)
  -- The saved state restored again.
  refine WP.seq (WP.mono (WP.here rfl hh4 (copyQ_ok L4 R4 (a := oSt2) (b := oSt) (by decide) (by decide)
    (by decide) (by decide) (by decide))) fun u5 ⟨⟨L5, k5, R5⟩, hh5⟩ => ?_)
  have h43 : ∀ x, oSt2 ≤ x → x < oSt2 + 256 → selV V3 (decide (c = l)) 64 x = V x := fun x h1 h2 => by
    rw [selV, ifn (by omega), hV3 _ (by simp only [inR_cons, inR_nil, or_false]; omega), cpV, ifn (by omega)]
  have hr5 := hsv u5.mem fun i hi => by
    rw [R5.scr _ (by omega), cpV, ifp ⟨by omega, by omega⟩, h43 _ (by omega) (by omega)]
    exact congrArg V (by omega)
  -- Updated with the buffer's byte `c`.
  unfold updCand
  refine WP.seq (WP.seq (WP.mono (WP.here rfl hh5 (updCandArgs_ok L5 R5 hD' hcw))
    fun u6 ⟨⟨hdi6, hsi6, hdx6, hcx6, h86, hm6, k6⟩, hh6⟩ => ?_))
  have L6 : Lay u6 F S := L5.congr (k6.gpr (by decide)) k6.2.2 (by rw [hm6])
  refine WP.mono (updF_ok hT hF hh6 L6 (hm6 ▸ R5) (j := 45) rfl (by decide) hfn'.2.1 (a := oBuf + c) (len := 1)
    (by omega) (.inl (by omega)) (.inl (by omega)) hdi6 hdx6 hcx6 h86) fun u7 ⟨L7, rd7, wr7, cs7, R7, hh7, hr7⟩ => ?_
  have hR7 := hr7 _ (hm6 ▸ hr5) (by rw [hsi6, hml])
  obtain ⟨V7, R7, hV7, hV7'⟩ := VG.Proof.RsaOaep.X86_64.Rep.ex R7
  -- Saved.
  refine WP.seq (WP.mono (WP.here rfl hh7 (copyQ_ok L7 R7 (a := oSt) (b := oSt2) (by decide) (by decide)
    (by decide) (by decide) (by decide))) fun u8 ⟨⟨L8, k8, R8⟩, hh8⟩ => ?_)
  refine WP.mono (WP.here rfl hh8 (nextCand_ok L8 R8 hcw ((hw 44 (by decide)).trans hdb) (by omega) (by omega)))
    fun u9 ⟨⟨L9, k9, hz9, R9⟩, hh9⟩ => ⟨hz9, L9, hh9, ?_, ?_, ?_, ?_⟩
  · exact k9.2.1.trans (k8.2.1.trans (rd7.trans (k6.2.1.trans (k5.2.1.trans (k4.2.1.trans (rd3.trans
      (k2.2.1.trans (k1.2.1.trans I.rd))))))))
  · exact k9.2.2.trans (k8.2.2.trans (wr7.trans (k6.2.2.trans (k5.2.2.trans (k4.2.2.trans (wr3.trans
      (k2.2.2.trans (k1.2.2.trans I.wr))))))))
  · intro r hr
    rw [keep_cs' k9 (cs_disj _ (by decide)) r hr, keep_cs' k8 (cs_disj _ (by decide)) r hr, cs7 r hr,
      keep_cs' k6 (cs_disj _ (by decide)) r hr, keep_cs' k5 (cs_disj _ (by decide)) r hr,
      keep_cs' k4 (cs_disj _ (by decide)) r hr, cs3 r hr, keep_cs' k2 (cs_disj _ (by decide)) r hr,
      keep_cs' k1 (cs_disj _ (by decide)) r hr, I.cs r hr]
  · have hW9 : upd (upd W₀ 19 (BitVec.ofNat 64 c)) 19 (BitVec.ofNat 64 (c + 1)) = upd W₀ 19 (BitVec.ofNat 64 (c + 1)) :=
      funext fun x => by simp only [upd]; split <;> rfl
    rw [hW9] at R9
    -- Bytes below `oSt`, and those of the digest, through every step.
    have hb : ∀ x, x < oSt → cpV V7 (fun i => V7 (oSt + i)) oSt2 256 x = V₀ x := fun x hx => by
      rw [cpV, ifn (by omega), hV7 _ (by simp only [inR_cons, inR_nil, or_false]; omega), cpV, ifn (by omega),
        selV, ifn (by omega), hV3 _ (by simp only [inR_cons, inR_nil, or_false]; omega), cpV, ifn (by omega),
        hlow x hx]
    refine ⟨_, R9, hb, fun m hm => ?_, fun i hi => ?_⟩
    · have hl7 : T.S.Repr m (off S oSt) ((pre ++ (List.range c).map fun i => V₀ (oBuf + i)) ++
          (List.range 1).map fun i => cpV (selV V3 (decide (c = l)) 64) (fun i => selV V3 (decide (c = l)) 64
            (oSt2 + i)) oSt 256 (oBuf + c + i)) :=
        hT.local_ (fun i hi => by
          rw [off_plus, hm i hi, cpV, ifp ⟨by omega, by omega⟩, Nat.add_sub_cancel_left,
            hV7' _ (by simp only [inR_cons, inR_nil, or_false]; omega)]) hR7
      refine VG.Proof.RsaOaep.X86_64.repr_congr ?_ hl7
      rw [List.range_succ (n := c), List.map_append, List.append_assoc]
      simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero]
      rw [cpV, ifn (by omega), selV, ifn (by omega), hV3 _ (by simp only [inR_cons, inR_nil, or_false]; omega),
        cpV, ifn (by omega), hlow _ (by omega)]
    · have hi64 : i < 64 := by omega
      rw [cpV, ifn (by omega), hV7 _ (by simp only [inR_cons, inR_nil, or_false]; omega), cpV, ifn (by omega),
        selV, ifp ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
      by_cases hcl : c = l
      · subst hcl
        rw [decide_eq_true rfl, ifp rfl, ifp (by omega), hV3' _ (by simp only [inR_cons, inR_nil, or_false]; omega),
          hdig i (by omega)]
      · rw [decide_eq_false hcl, ifn (by simp), hV3 _ (by simp only [inR_cons, inR_nil, or_false]; omega), cpV,
          ifn (by omega), hdg i hi]
        by_cases hlc : l < c
        · rw [ifp hlc, ifp (by omega)]
        · rw [ifn hlc, ifn (by omega)]

include hT in
/-- With any salt length, the salt's length `sl` found (word 5) after `pos`
(word 32): `rax` is 1 if `acc` (word 4) is zero and
`H(0⁸ ‖ mHash ‖ salt)` is `H`, the salt the `sl` bytes of `DB` after `pos`. -/
theorem autoBack_ok (hF : Fns stack e₀ T fi fu ff) {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = T.S.H.hash x)
    {u : State} {F S : Addr} (hh : Here stack e₀ u F S) (L : Lay u F S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {D e db pos sl : Nat} {p : Addr}
    (hD : W 39 = BitVec.ofNat 64 D) (hDl : T.S.digestBytes = D)
    (hfn : W 45 = fi ∧ W 46 = fu ∧ W 47 = ff) (hp : W 27 = p) (he : W 33 = off S e)
    (hdb : W 44 = BitVec.ofNat 64 db) (hpos : W 32 = BitVec.ofNat 64 pos) (hsl : W 5 = BitVec.ofNat 64 sl)
    (hps : pos + 1 + sl = db) (hfit : e + db + D ≤ oBuf)
    (hsrc : ∀ i < D, InRegions (u.rd ++ u.wr) (p + BitVec.ofNat 64 i) 1)
    (hdis : ∀ i < D, ∀ j < D, p + BitVec.ofNat 64 i ≠ off S (oMp + 8 + j)) :
    WP isa autoBack u fun u' => Lay u' F S ∧ Here stack e₀ u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ calleeSaved, u'.gpr r = u.gpr r) ∧
      u'.gpr .rax = if W 4 = 0 ∧ ∀ i < D, (Hs.hash (Spec.RsaPss.zeros 8 ++
          (List.range D).map (fun i => u.mem (p + BitVec.ofNat 64 i)) ++
          (List.range sl).map (fun i => V (e + pos + 1 + i)))).getD i 0 = V (e + db + i) then 1 else 0 := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hT
  have c1 : oSt = 3072 := rfl
  have c2 : oDig = 3328 := rfl
  have c3 : oBuf = 1024 := rfl
  have c4 : oW = 4096 := rfl
  have c5 : oRsa = 8192 := rfl
  have c6 : oMp = 3584 := rfl
  have c8 : oSt2 = 3712 := rfl
  have hD64 : D ≤ 64 := by omega
  unfold autoBack seqs seqs seqs seqs seqs seqs seqs
  refine WP.seq (WP.mono (WP.here (by decide) hh (mPrefix_ok L R hp hD (by omega) hD64 hsrc hdis))
    fun u1 ⟨⟨L1, k1, R1⟩, hh1⟩ => ?_)
  refine WP.seq (WP.mono (WP.here (by decide) hh1 (copyDb_ok L1 R1 he hdb (by omega) (by omega)))
    fun u2 ⟨⟨L2, k2, hcx2, R2⟩, hh2⟩ => ?_)
  refine WP.seq (WP.mono (WP.here (by decide) hh2 (VG.Proof.RsaOaep.X86_64.shift_ok L2 R2 hcx2 hpos (by omega) fun x h1 h2 => by
      rw [cpV, ifn (by omega), VG.Proof.RsaOaep.X86_64.clrV, ifp ⟨by omega, by omega⟩]))
    fun u3 ⟨⟨L3, k3, V3, W3, R3, hW3, hB3, hO3⟩, hh3⟩ => ?_)
  have hw3 : ∀ k, k < nW → k ≠ 34 → k ≠ 35 → k ≠ 36 → W3 k = W k := hW3
  -- What the steps so far leave of the bytes outside the buffer.
  have hV3 : ∀ x, x < oRsa → ¬ (oBuf ≤ x ∧ x < oBuf + 2048) → ¬ (oMp ≤ x ∧ x < oMp + 8 + D) → V3 x = V x :=
    fun x _ h1 h2 => by
      rw [hO3 x h1, cpV, ifn (by omega), VG.Proof.RsaOaep.X86_64.clrV, ifn (by omega)]
      simp only [mpV, stBytes, cpV]
      rw [ifn (by omega), ifn (by omega)]
  have hpre : (List.range (D + 8)).map (fun i => V3 (oMp + i)) =
      Spec.RsaPss.zeros 8 ++ (List.range D).map (fun i => u.mem (p + BitVec.ofNat 64 i)) := by
    rw [← mpV_bytes V _ D]
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    rw [hO3 _ (by omega), cpV, ifn (by omega), VG.Proof.RsaOaep.X86_64.clrV, ifn (by omega)]
  have hsalt : ∀ i < sl, V3 (oBuf + i) = V (e + pos + 1 + i) := fun i hi => by
    rw [hB3 i (by omega), VG.Proof.RsaOaep.X86_64.bufB, ifp (by omega), cpV, ifp ⟨by omega, by omega⟩]
    simp only [mpV, stBytes, cpV]
    rw [ifn (by omega), ifn (by omega)]
    exact congrArg V (by omega)
  have hD3 : W3 39 = BitVec.ofNat 64 D := (hw3 39 (by decide) (by decide) (by decide) (by decide)).trans hD
  have hfn3 : W3 45 = fi ∧ W3 46 = fu ∧ W3 47 = ff :=
    ⟨(hw3 45 (by decide) (by decide) (by decide) (by decide)).trans hfn.1,
      (hw3 46 (by decide) (by decide) (by decide) (by decide)).trans hfn.2.1,
      (hw3 47 (by decide) (by decide) (by decide) (by decide)).trans hfn.2.2⟩
  refine WP.seq (WP.mono (hashPrefix_ok hT hF hh3 L3 R3 hD3 hD64 hfn3)
    fun u4 ⟨L4, hh4, rd4, wr4, cs4, V4, R4, hV4, hr4⟩ => ?_)
  refine WP.seq (WP.mono (WP.here rfl hh4 (copyQ_ok L4 R4 (a := oSt) (b := oSt2) (by decide) (by decide)
    (by decide) (by decide) (by decide))) fun u5 ⟨⟨L5, k5, R5⟩, hh5⟩ => ?_)
  refine WP.seq (WP.mono (WP.here rfl hh5 (ctr0_ok L5 R5)) fun u6 ⟨⟨L6, k6, R6⟩, hh6⟩ => ?_)
  -- The bytes that the loop starts from.
  have hV5 : ∀ x, x < oSt → cpV V4 (fun i => V4 (oSt + i)) oSt2 256 x = V3 x := fun x hx => by
    rw [cpV, ifn (by omega), hV4 _ (by simp only [hR, inR_cons, inR_nil, or_false]; omega)]
  have hsv0 : ∀ m : Mem, (∀ i < T.S.stateBytes, m (off S (oSt + i)) = cpV V4 (fun i => V4 (oSt + i)) oSt2 256
      (oSt2 + i)) → T.S.Repr m (off S oSt) (((List.range (D + 8)).map fun i => V3 (oMp + i)) ++
        (List.range 0).map fun i => cpV V4 (fun i => V4 (oSt + i)) oSt2 256 (oBuf + i)) := fun m hm => by
    rw [List.range_zero, List.map_nil, List.append_nil]
    refine hT.local_ (fun i hi => ?_) hr4
    rw [off_plus, hm i hi, cpV, ifp ⟨by omega, by omega⟩, Nat.add_sub_cancel_left, R4.scr _ (by omega)]
  have I0 : CandI stack e₀ u6 T F S (cpV V4 (fun i => V4 (oSt + i)) oSt2 256) W3
      ((List.range (D + 8)).map fun i => V3 (oMp + i)) D sl 0 u6 :=
    ⟨L6, hh6, rfl, rfl, fun _ _ => rfl, _, R6, fun _ _ => rfl, hsv0, fun i _ => by
      rw [ifn (Nat.not_lt_zero _)]⟩
  have hpl : ((List.range (D + 8)).map fun i => V3 (oMp + i)).length = D + 8 := by simp
  refine WP.seq (WP.loop (M := isa) (fun n w => ∃ c, n = db - c ∧ c < db ∧ CandI stack e₀ u6 T F S
      (cpV V4 (fun i => V4 (oSt + i)) oSt2 256) W3 ((List.range (D + 8)).map fun i => V3 (oMp + i)) D sl c w)
    ?_ (db - 0) u6 ⟨0, rfl, by omega, I0⟩)
  rintro n w ⟨c, rfl, hc, I⟩
  refine WP.mono (cand_ok hT hF hD3 hDl hfn3 ((hw3 5 (by decide) (by decide) (by decide) (by decide)).trans hsl)
    (by omega) ((hw3 44 (by decide) (by decide) (by decide) (by decide)).trans hdb) (by omega) hpl I hc)
    fun w' ⟨hz, I'⟩ => ?_
  by_cases hl : c + 1 < db
  · exact .inr ⟨by simp only [eval, hz]; simp; omega, db - (c + 1), by omega, c + 1, rfl, hl, I'⟩
  refine .inl ⟨by simp only [eval, hz]; simp; omega, ?_⟩
  obtain ⟨Vf, Rf, hlow, -, hdg⟩ := I'.rep
  have hwf : ∀ k, k < nW → k ≠ 19 → k ≠ 34 → k ≠ 35 → k ≠ 36 → upd W3 19 (BitVec.ofNat 64 (c + 1)) k = W k :=
    fun k hk h1 h2 h3 h4 => (upd_ne _ _ h1).trans (hw3 k hk h2 h3 h4)
  refine WP.mono (WP.here (by decide) I'.here (cmpH_ok I'.L Rf
    ((hwf 33 (by decide) (by decide) (by decide) (by decide) (by decide)).trans he)
    ((hwf 44 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdb)
    ((hwf 39 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hD) (by omega) hD64 (by omega)))
    fun u' ⟨⟨k', hm', hax⟩, hh'⟩ => ⟨I'.L.congr (k'.gpr (by decide)) k'.2.2 (by rw [hm']), hh', ?_, ?_, ?_, ?_⟩
  · exact k'.2.1.trans (I'.rd.trans (k6.2.1.trans (k5.2.1.trans (rd4.trans (k3.2.1.trans (k2.2.1.trans k1.2.1))))))
  · exact k'.2.2.trans (I'.wr.trans (k6.2.2.trans (k5.2.2.trans (wr4.trans (k3.2.2.trans (k2.2.2.trans k1.2.2))))))
  · intro r hr
    rw [keep_cs' k' (cs_disj _ (by decide)) r hr, I'.cs r hr, keep_cs' k6 (cs_disj _ (by decide)) r hr,
      keep_cs' k5 (cs_disj _ (by decide)) r hr, cs4 r hr, keep_cs' k3 (cs_disj _ (by decide)) r hr,
      keep_cs' k2 (cs_disj _ (by decide)) r hr, keep_cs' k1 (cs_disj _ (by decide)) r hr]
  · have hsl' : (List.range sl).map (fun i => cpV V4 (fun i => V4 (oSt + i)) oSt2 256 (oBuf + i)) =
        (List.range sl).map (fun i => V (e + pos + 1 + i)) := List.map_congr_left fun i hi => by
      have := List.mem_range.mp hi
      rw [hV5 _ (by omega), hsalt i this]
    have hc : (upd W3 19 (BitVec.ofNat 64 (c + 1)) 4 = 0 ∧ ∀ i < D, Vf (oDig + i) = Vf (e + db + i)) ↔
        (W 4 = 0 ∧ ∀ i < D, (Hs.hash (Spec.RsaPss.zeros 8 ++
          (List.range D).map (fun i => u.mem (p + BitVec.ofNat 64 i)) ++
          (List.range sl).map (fun i => V (e + pos + 1 + i)))).getD i 0 = V (e + db + i)) := by
      rw [hwf 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
      refine and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun hi => ?_
      rw [hdg i hi, ifp (by omega), hlow _ (by omega), hV5 _ (by omega),
        hV3 _ (by omega) (by omega) (by omega), hHh, hpre, hsl']
    rw [hax]
    by_cases h : upd W3 19 (BitVec.ofNat 64 (c + 1)) 4 = 0 ∧ ∀ i < D, Vf (oDig + i) = Vf (e + db + i)
    · rw [ifp h, ifp (hc.mp h)]
    · rw [ifn h, ifn (fun h' => h (hc.mpr h'))]

include hT in
/-- The salt's hash, with its length given (`fixed`, word 28 zero) or found,
and the comparison: `rax` is 1 if `acc` (word 4) is zero and
`H(0⁸ ‖ mHash ‖ salt)` is `H`, the salt the `ln` bytes of `DB` after `pos`. -/
theorem saltBack_ok (hF : Fns stack e₀ T fi fu ff) {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = T.S.H.hash x)
    {u : State} {F S : Addr} (hh : Here stack e₀ u F S) (L : Lay u F S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {D e db pos ln sl : Nat} {fixed : Bool} {p : Addr}
    (hD : W 39 = BitVec.ofNat 64 D) (hDl : T.S.digestBytes = D)
    (hfn : W 45 = fi ∧ W 46 = fu ∧ W 47 = ff) (hp : W 27 = p) (he : W 33 = off S e)
    (hdb : W 44 = BitVec.ofNat 64 db) (hpos : W 32 = BitVec.ofNat 64 pos) (hln : W 5 = BitVec.ofNat 64 ln)
    (hps : pos + 1 + ln = db) (hany : W 28 = if fixed then 0 else 1) (hsl : W 29 = BitVec.ofNat 64 sl)
    (hsl1 : fixed = true → sl ≤ db) (hfx : fixed = true → W 4 = 0 → sl = ln) (hfit : e + db + D ≤ oBuf)
    (hsrc : ∀ i < D, InRegions (u.rd ++ u.wr) (p + BitVec.ofNat 64 i) 1)
    (hdis : ∀ i < D, ∀ j < D, p + BitVec.ofNat 64 i ≠ off S (oMp + 8 + j)) :
    WP isa saltBack u fun u' => Lay u' F S ∧ Here stack e₀ u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r ∈ calleeSaved, u'.gpr r = u.gpr r) ∧
      u'.gpr .rax = if W 4 = 0 ∧ ∀ i < D, (Hs.hash (Spec.RsaPss.zeros 8 ++
          (List.range D).map (fun i => u.mem (p + BitVec.ofNat 64 i)) ++
          (List.range ln).map (fun i => V (e + pos + 1 + i)))).getD i 0 = V (e + db + i) then 1 else 0 := by
  unfold saltBack
  refine WP.seq (WP.mono (WP.here rfl hh (WP.keep [.rax] (Q := fun v => v.zf = some fixed ∧ v.mem = u.mem) ?_ rfl))
    fun v ⟨⟨⟨hz, hm⟩, hk⟩, hhv⟩ => ?_)
  · xrun [ea_sp, L.rsp, L.ld (d := sAny) (by decide), R.rd (d := sAny) 28 rfl (by decide), hany]
    cases fixed <;> decide
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  have Rv : Rep v.mem F S V W := hm ▸ R
  have hsrc' : ∀ i < D, InRegions (v.rd ++ v.wr) (p + BitVec.ofNat 64 i) 1 := by
    rw [hk.2.1, hk.2.2]; exact hsrc
  obtain ⟨-, hzF, -, hzDF, -⟩ := sizes hT
  have hcs : ∀ {P : Prop} (w : State), w.rd = v.rd → w.wr = v.wr → (∀ r ∈ calleeSaved, w.gpr r = v.gpr r) →
      P → w.rd = u.rd ∧ w.wr = u.wr ∧ (∀ r ∈ calleeSaved, w.gpr r = u.gpr r) ∧ P :=
    fun w h1 h2 h3 h4 => ⟨h1.trans hk.2.1, h2.trans hk.2.2,
      fun r hr => (h3 r hr).trans (keep_cs' hk (cs_disj _ (by decide)) r hr), h4⟩
  refine WP.ite (M := isa) _ (show isa.eval .e v = _ from hz) (fun hb => ?_) (fun hb => ?_)
  · subst hb
    refine WP.mono (fixedBack_ok hT hF hHh hhv Lv Rv hD hDl (by omega) hfn hp he hdb hsl (hsl1 rfl) (by omega)
      hsrc' hdis) fun w ⟨Lw, hw, rdw, wrw, csw, hax⟩ => ⟨Lw, hw, ?_⟩
    rw [hm] at hax
    refine hcs w rdw wrw csw (hax.trans ?_)
    by_cases h4 : W 4 = 0
    · obtain rfl := hfx rfl h4
      have e1 : e + db - sl = e + pos + 1 := by omega
      simp only [e1]
    · rw [ifn (fun h => h4 h.1), ifn (fun h => h4 h.1)]
  · subst hb
    refine WP.mono (autoBack_ok hT hF hHh hhv Lv Rv hD hDl hfn hp he hdb hpos hln hps (by omega) hsrc' hdis)
      fun w ⟨Lw, hw, rdw, wrw, csw, hax⟩ => ⟨Lw, hw, ?_⟩
    rw [hm] at hax
    exact hcs w rdw wrw csw hax

end VG.Proof.RsaPss.X86_64
