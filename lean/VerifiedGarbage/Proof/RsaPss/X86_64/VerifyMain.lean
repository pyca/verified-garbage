import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCall
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBlocks
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect

/-!
# RSASSA-PSS verification on x86-64: after the checks

`vfront_ok`: `DB`'s slots, the public-key operation's arguments, and the
call, which leaves RSAVP1's result (zeros if it fails, `vx`) at
`scratch + oEm`.
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (pubChkContract)

variable {G : Spec.Mgf1.Hash}

theorem WP.seq_inv {A B : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq A B) s Q) :
    WP isa A s fun t => WP isa B t Q := by
  obtain ⟨t, s', he, hq⟩ := h
  cases he with | seq h1 h2 => exact ⟨_, _, h1, _, _, h2, hq⟩

/-- A sequence, in two pieces. -/
theorem WP.seqs_append : ∀ {l₁ l₂ : List (Prog isa)}, l₁ ≠ [] → l₂ ≠ [] → ∀ {s : State} {Q : State → Prop},
    WP isa (seqs l₁) s (fun t => WP isa (seqs l₂) t Q) → WP isa (seqs (l₁ ++ l₂)) s Q
  | [], _, h₁, _, _, _, _ => absurd rfl h₁
  | [c], l₂, _, h₂, s, Q, h => by
    obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil h₂
    exact WP.seq h
  | c :: c' :: cs, l₂, _, h₂, s, Q, h => by
    have ih := @WP.seqs_append (c' :: cs) l₂ (List.cons_ne_nil _ _) h₂
    exact WP.seq (WP.mono (WP.seq_inv h) fun t ht => ih ht)

/-- RSAVP1's result, `k` bytes, or zeros if it fails. -/
def vx (s : State) : List Byte :=
  (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .rsi).toNat)).getD (Spec.RsaPss.zeros (s.gpr .rsi).toNat)

/-- `Rep` across a change of `EM`'s place alone. -/
theorem Rep.of_em {m m' : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W)
    (G' : Geo F S) {k : Nat} (hk : oEm + k ≤ oRsa)
    (h : ∀ x, ((⟨F, frameBytes⟩ : Region).Contains x 1 ∨ ((⟨S, oRsa⟩ : Region).Contains x 1 ∧
      ¬ (⟨off S oEm, k⟩ : Region).Contains x 1)) → m' x = m x) :
    Rep m' F S (fun o => if oEm ≤ o ∧ o < oEm + k then m' (off S o) else V o) W where
  scr o ho := by
    have := G'.Sw
    split
    · rfl
    · rename_i hn
      rw [h _ (.inr ⟨Offset.contains_base _ (by omega) (by unfold oRsa at *; omega), fun hc =>
        (Offset.disjoint S (d := o) (n := 1) (e := oEm) (k := k) (by omega) (by unfold oRsa at *; omega)
          (by unfold oRsa at *; omega)) (off S o)
          (Offset.contains S (d := o) (n := 1) (e := o) (k := 1) (le_refl _) (le_refl _)
            (by unfold oRsa at *; omega)) hc⟩), R.scr o ho]
  fr k' hk' := by
    rw [← R.fr k' hk']
    refine Mem.readW_congr fun i hi => h _ (.inl ?_)
    have := G'.Fw
    rw [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.contains_base _ (by unfold nW frameBytes at *; omega) (by unfold nW frameBytes at *; omega)

theorem vframe_keep {s u v : State} (hp : VPre G s) (hw : u.wr = frR s :: s.wr) (hsp : u.gpr .rsp = fb s)
    (hM : Frame (vwrR s) s.mem u.mem)
    (hk : ∀ a, (∀ r ∈ u.wr, ¬ r.Contains a 1) → ¬ (below (u.gpr .rsp) 8).Contains a 1 → v.mem a = u.mem a) :
    Frame (vwrR s) s.mem v.mem := by
  intro x hx
  refine (hk x (fun r hr hc => ?_) (fun hc => ?_)).trans (hM x hx)
  · rw [hw, hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hx _ (List.mem_cons_self ..) (vframe_sub s x hc)
    · exact hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hc
  · rw [hsp] at hc; exact hx _ (List.mem_cons_self ..) (vret_sub s x hc)

theorem vfront_ok {pubN : String} {pubC : Prog isa}
    (hv : ∀ s, pubContract.pre s → ∃ t s', Exec isa pubC s t s' ∧ abiPreserved s s' ∧ pubChkContract.post s s')
    (hspC : SpSafe pubC) (hdC : pubC.x86_64Depth = 0)
    {s u : State} (hp : VPre G s) {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay u (fb s) (stackArg s 3)) (R : Rep u.mem (fb s) (stackArg s 3) V W) (hw : u.wr = frR s :: s.wr)
    (hrd : u.rd = s.rd) (hM : Frame (vwrR s) s.mem u.mem) {lo a : Nat}
    (h17 : W 17 = s.gpr .rsi) (h18 : W 18 = s.gpr .rdi) (h19 : W 19 = s.gpr .rdx) (h20 : W 20 = s.gpr .rcx)
    (h22 : W 22 = stackArg s 4) (h26 : W 26 = BitVec.ofNat 64 lo) (h38 : W 38 = s.gpr .r9)
    (hax : u.gpr .rax = BitVec.ofNat 64 a) :
    WP isa (seqs [.block dbSlots, .block pubArgs, .call pubN pubC]) u fun u3 =>
      Lay u3 (fb s) (stackArg s 3) ∧ u3.wr = u.wr ∧ u3.rd = u.rd ∧
      (∀ r ∈ [Reg.r13, .r14, .r15], u3.gpr r = u.gpr r) ∧ Frame (vwrR s) s.mem u3.mem ∧
      ∃ V1 W1, Rep u3.mem (fb s) (stackArg s 3) V1 W1 ∧ (∀ j < nW, 4 ≤ j → j ≠ 23 → j ≠ 24 → W1 j = W j) ∧
        W1 23 = off (stackArg s 3) (oEm + lo) ∧ W1 24 = BitVec.ofNat 64 (a + 1) ∧
        (∀ i < (s.gpr .rsi).toNat, V1 (oEm + i) = (vx s).getD i 0) ∧
        (∀ o, ¬ (oEm ≤ o ∧ o < oEm + (s.gpr .rsi).toNat) → V1 o = V o) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  simp only [seqs]
  -- `DB`'s slots.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [dbSlots]) (Nat.zero_le 8)
    (dbSlots_ok L R h26 hax)) fun u1 ⟨⟨L1, k1, R1⟩, f1⟩ => ?_)
  have hM1 := vframe_keep hp hw L.rsp hM f1
  have g1 : ∀ j, j ≠ 23 → j ≠ 24 → upd (upd W 24 (BitVec.ofNat 64 (a + 1))) 23 (off (stackArg s 3) (oEm + lo)) j =
      W j := fun j h23 h24 => by simp [upd, h23, h24]
  -- The arguments.
  refine WP.seq (WP.mono (WP.keepIn (by decide) (Nat.zero_le 8)
    (pubArgs_ok L1 R1 (by rw [g1 17 (by decide) (by decide), h17]) (by rw [g1 18 (by decide) (by decide), h18])
      (by rw [g1 19 (by decide) (by decide), h19]) (by rw [g1 20 (by decide) (by decide), h20])
      (by rw [g1 22 (by decide) (by decide), h22]) (by rw [g1 38 (by decide) (by decide), h38])))
    fun u2 ⟨⟨k2, L2, ⟨W2, R2, hW2a, hW2b⟩, h2di, h2si, h2dx, h2cx, h2r8, h2r9⟩, f2⟩ => ?_)
  have hw1 : u1.wr = frR s :: s.wr := k1.2.2.trans hw
  have hw2 : u2.wr = frR s :: s.wr := k2.2.2.trans hw1
  have hM2 := vframe_keep hp hw1 L1.rsp hM1 f2
  -- The call.
  refine WP.mono (pub_call hv hspC hdC hp L2.rsp ((k2.2.1.trans k1.2.1).trans hrd) hw2 hM2
    (fun i hi => (R2.fr i (by unfold nW frameBytes; omega)).trans (hW2a i hi)) h2di h2si h2dx h2cx h2r8 h2r9)
    fun u3 ⟨rd3, wr3, cs3, _, hM3, hk3, hout3⟩ => ?_
  have hEm : oEm + (s.gpr .rsi).toNat ≤ oRsa := by unfold oEm oRsa; omega
  have R3 := R2.of_em L2.geo hEm hk3
  have L3 : Lay u3 (fb s) (stackArg s 3) := L2.of_rep' R2 R3 rfl (cs3 .rsp (by decide)) wr3
  refine ⟨L3, wr3.trans (k2.2.2.trans k1.2.2), rd3.trans (k2.2.1.trans k1.2.1), fun r hr => ?_, hM3, _, _, R3,
    fun j hj h4 h23 h24 => by rw [hW2b j hj h4, g1 j h23 h24], by rw [hW2b 23 (by decide) (by decide)]; simp [upd],
    by rw [hW2b 24 (by decide) (by decide)]; simp [upd], fun i hi => ?_, fun o ho => ?_⟩
  · have hr3 : r = .r13 ∨ r = .r14 ∨ r = .r15 := by simpa using hr
    have h1 : r ∈ calleeSaved := by rcases hr3 with rfl | rfl | rfl <;> decide
    have h2 : r ∉ [Reg.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] := by rcases hr3 with rfl | rfl | rfl <;> decide
    rw [cs3 r h1, k2.gpr h2, k1.gpr (by rcases hr3 with rfl | rfl | rfl <;> decide)]
  · -- `EM`'s bytes are RSAVP1's result.
    have hb : Spec.Rsa.bytesAt u3.mem (off (stackArg s 3) oEm) (s.gpr .rsi).toNat = vx s := by
      unfold vx
      cases hpo : Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .rsi).toNat) with
      | none => rw [hpo] at hout3; exact hout3.2
      | some y => rw [hpo] at hout3; exact hout3.2
    rw [← hb, bytesAt_off]
    simp only [ifp (show oEm ≤ oEm + i ∧ oEm + i < oEm + (s.gpr .rsi).toNat by omega)]
    rw [getD_map_range, ifp hi]
  · simp only [ifn ho]

/-! ## `DB`, its first nonzero byte, and `acc` -/

theorem fnz_congr {f g : Nat → Byte} : ∀ {j : Nat}, (∀ i < j, f i = g i) → fnz f j = fnz g j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [fnz, fnz_congr (j := j) (fun i hi => h i (by omega)), h j (by omega)]

/-- `DB` after the mask and the top bits. -/
theorem db_bytes (V : Nat → Byte) (mk : List Byte) {e db z : Nat} (hmk : mk.length = db) :
    ∀ i < db, upd (mixV V mk e db) e (mixV V mk e db e &&& ((0xFF : Byte) >>> z)) (e + i) =
      (Spec.RsaPss.clearTop z (Spec.Mgf1.xorBytes ((List.range db).map fun i => V (e + i)) mk)).getD i 0 := by
  intro i hi
  rw [clearTop_getD]
  have hx : ∀ j < db, (Spec.Mgf1.xorBytes ((List.range db).map fun i => V (e + i)) mk).getD j 0 =
      V (e + j) ^^^ mk.getD j 0 := fun j hj => by
    rw [xorBytes_getD (by simp; omega) (by omega), getD_map_range, ifp hj]
  simp only [upd, mixV]
  by_cases h0 : i = 0
  · subst h0
    rw [ifp (by omega), ifp rfl, ifp (show e ≤ e ∧ e < e + db by omega), hx 0 hi, Nat.sub_self, Nat.add_zero]
  · rw [ifn (by omega), ifn h0, ifp (show e ≤ e + i ∧ e + i < e + db by omega), hx i hi,
      show e + i - e = i by omega]

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H) (K : Pbkdf2.Md.X86_64.Callees H)

include hH K in
theorem vmid_ok (lk : Pbkdf2.Md.X86_64.MgfLink H hH) {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {k lo db z : Nat} {fixed : Bool}
    (hk : W 17 = BitVec.ofNat 64 k) (he : W 23 = off S (oEm + lo)) (hdb : W 24 = BitVec.ofNat 64 db)
    (hc : W 25 = BitVec.setWidth 64 ((0xFF : Byte) >>> z)) (hlo : W 26 = BitVec.ofNat 64 lo)
    (hany : W 35 = if fixed then 0 else 1)
    (hlo1 : lo ≤ 1) (hdb1 : 1 ≤ db) (hlay : lo + db + H.D + 1 = k) (hk2 : k ≤ 1024) :
    let hB := (List.range H.D).map fun i => V (oEm + lo + db + i)
    let dbL := Spec.RsaPss.clearTop z (Spec.Mgf1.xorBytes ((List.range db).map fun i => V (oEm + lo + i))
      (Spec.Mgf1.mgf1 lk.G hB db))
    let fd := decide (lz dbL < db)
    let pos := if lz dbL < db then lz dbL else 0
    let val := if lz dbL < db then dbL.getD (lz dbL) 0 else 0
    WP isa (seqs [.block acc0, mgfXor H, .block clearTop, posScan, posCheck H]) u fun u' => Lay u' F S ∧
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u'.gpr r = u.gpr r) ∧
      ∃ V' W', Rep u'.mem F S V' W' ∧
        W' 33 = acc1V (acc0V (V (oEm + k - 1)) (V oEm) (V (oEm + lo)) ((0xFF : Byte) >>> z) lo) fd val fixed
          (BitVec.ofNat 64 (db - pos - 1)) (W 36) ∧
        W' 34 = BitVec.ofNat 64 pos ∧ W' 27 = BitVec.ofNat 64 (db - pos - 1 + (8 + H.D)) ∧
        (∀ j < nW, (j < 27 ∨ 34 < j) → W' j = W j) ∧
        (∀ i < db, V' (oEm + lo + i) = dbL.getD i 0) ∧
        (∀ o < oRsa, ctOut o → ¬ (oEm + lo ≤ o ∧ o < oEm + lo + db) → V' o = V o) := by
  intro hB dbL fd pos val
  have hD := hH.hD0
  have hDN := hH.hDN
  have c1 : oEm = 2560 := rfl
  have c5 : oRsa = 8192 := rfl
  have hG := validG hH lk.hash lk.len
  simp only [seqs]
  -- `acc0`.
  refine WP.seq (WP.mono (acc0_ok L R (c := (0xFF : Byte) >>> z) hk he hc hlo (by omega) hk2 (by omega))
    fun u1 ⟨L1, k1, R1⟩ => ?_)
  set a0 := acc0V (V (oEm + k - 1)) (V oEm) (V (oEm + lo)) ((0xFF : Byte) >>> z) lo
  have g1 : ∀ j, j ≠ 33 → upd W 33 a0 j = W j := fun j h => by simp [upd, h]
  -- The mask.
  refine WP.seq (WP.mono (mgfXor_ok hH K lk.hash lk.len hG L1 R1 (e := oEm + lo) (db := db)
    ⟨by omega, hdb1, by omega⟩ (by rw [g1 23 (by decide), he]) (by rw [g1 24 (by decide), hdb]))
    fun u2 ⟨L2, rd2, wr2, cs2, V2, W2, R2, hW2, hV2⟩ => ?_)
  -- The top bits.
  have h23 : W2 23 = off S (oEm + lo) := by rw [hW2 23 (by decide) (by omega), g1 23 (by decide), he]
  have h25 : W2 25 = BitVec.setWidth 64 ((0xFF : Byte) >>> z) := by
    rw [hW2 25 (by decide) (by omega), g1 25 (by decide), hc]
  refine WP.seq (WP.mono (clearTop_ok L2 R2 (e := oEm + lo) h23 h25 (by omega)) fun u3 ⟨L3, k3, R3⟩ => ?_)
  set V3 := upd V2 (oEm + lo) (V2 (oEm + lo) &&& ((0xFF : Byte) >>> z))
  -- `DB`'s bytes.
  have hmk : (Spec.Mgf1.mgf1 lk.G hB db).length = db := Proof.Mgf1.mgf1_length hG _ _
  have hV3 : ∀ i < db, V3 (oEm + lo + i) = dbL.getD i 0 := fun i hi => by
    have hm : ∀ o < oRsa, ctOut o → V2 o = mixV V (Spec.Mgf1.mgf1 lk.G hB db) (oEm + lo) db o := hV2
    have hco : ∀ j < db, ctOut (oEm + lo + j) := fun j hj => ⟨by unfold oLen; omega, by unfold oY; omega⟩
    have := db_bytes V (Spec.Mgf1.mgf1 lk.G hB db) (e := oEm + lo) (z := z) hmk i hi
    rw [← this]
    simp only [V3, upd]
    by_cases h0 : i = 0
    · subst h0
      have hco0 : ctOut (oEm + lo) := ⟨by unfold oLen; omega, by unfold oY; omega⟩
      rw [Nat.add_zero, ifp rfl, ifp rfl, hm _ (by omega) hco0]
    · rw [ifn (by omega), ifn (by omega), hm _ (by omega) (hco i hi)]
  have hfnz : fnz (fun i => V3 (oEm + lo + i)) db = if lz dbL < db then some (lz dbL) else none := by
    rw [fnz_congr (g := fun i => dbL.getD i 0) fun i hi => hV3 i hi]
    exact fnz_lz dbL db (by simp only [dbL]; rw [clearTop_length, Proof.Mgf1.xorBytes_length]; simp [hmk])
  -- The first nonzero byte.
  have R3' : Rep u3.mem F S V3 W2 := R3
  have h23' : W2 23 = off S (oEm + lo) := h23
  have h24 : W2 24 = BitVec.ofNat 64 db := by rw [hW2 24 (by decide) (by omega), g1 24 (by decide), hdb]
  refine WP.seq (WP.mono (posScan_ok L3 R3' h23' h24 hdb1 (by omega))
    fun u4 ⟨k4, hm4, hdx4, hsi4, h114⟩ => ?_)
  have L4 : Lay u4 F S := L3.congr (k4.gpr (by decide)) k4.2.2 (by rw [hm4])
  have R4 : Rep u4.mem F S V3 W2 := hm4 ▸ R3'
  rw [hfnz] at hdx4 hsi4 h114
  -- Its checks.
  have h35 : W2 35 = if fixed then 0 else 1 := by rw [hW2 35 (by decide) (by omega), g1 35 (by decide), hany]
  have hpos : pos < db := by simp only [pos]; split <;> omega
  refine WP.mono (posCheck_ok hH L4 R4 (db := db) (pos := pos) (fd := fd) (val := val) h24 h35 hpos
    (by rw [hdx4]; simp only [fd]; split <;> simp_all)
    (by rw [hsi4]; simp only [pos]; split <;> simp_all)
    (by rw [h114]; simp only [val]; split <;> simp_all)) fun u5 ⟨L5, k5, R5⟩ => ?_
  refine ⟨L5, ?_, ?_, fun r hr => ?_, _, _, R5, ?_, by simp [upd], by simp [upd], fun j hj hj' => ?_, fun i hi => ?_,
    fun o ho hco hn => ?_⟩
  · rw [k5.2.1, k4.2.1, k3.2.1, rd2, k1.2.1]
  · rw [k5.2.2, k4.2.2, k3.2.2, wr2, k1.2.2]
  · rw [keep_cs k5 (by decide) r hr, keep_cs k4 (by decide) r hr, keep_cs k3 (by decide) r hr, cs2 r hr,
      keep_cs k1 (by decide) r hr]
  · simp only [upd, Nat.reduceEqDiff, ite_true, ite_false]
    rw [hW2 33 (by decide) (by omega), hW2 36 (by decide) (by omega), g1 36 (by decide)]
    simp [upd]
  · simp only [upd]
    rw [ifn (by omega), ifn (by omega), ifn (by omega), hW2 j hj (by omega), g1 j (by omega)]
  · exact hV3 i hi
  · simp only [V3, upd]
    rw [ifn (by omega), hV2 o ho hco]
    simp only [mixV]
    rw [ifn hn]

/-! ## The salt, its hash, and the result -/

include hH K in
theorem vback_ok (lk : Pbkdf2.Md.X86_64.MgfLink H hH) {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {lo db pos : Nat} {dig : Addr}
    (he : W 23 = off S (oEm + lo)) (hdb : W 24 = BitVec.ofNat 64 db) (hpos : W 34 = BitVec.ofNat 64 pos)
    (hl : W 27 = BitVec.ofNat 64 (db - pos - 1 + (8 + H.D))) (hdg : W 37 = dig)
    (hlo1 : lo ≤ 1) (hdb1 : 1 ≤ db) (hpd : pos < db) (hfit : lo + db + H.D + 1 ≤ 1024)
    (hdR : ∀ i < H.D, InRegions (u.rd ++ u.wr) (dig + BitVec.ofNat 64 i) 1)
    (hdO : ∀ i < H.D, Outside u.wr F (dig + BitVec.ofNat 64 i)) :
    let msg := Spec.RsaPss.zeros 8 ++ (List.range H.D).map (bytesF u.mem dig) ++
      ((List.range db).map fun i => V (oEm + lo + i)).drop (pos + 1)
    WP isa (seqs [clearY, copyDigest H, copyDb H, shift H, .block (verifyNb H), ctHash H, cmpH H]) u fun u' =>
      Lay u' F S ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], u'.gpr r = u.gpr r) ∧
      (∃ V' W', Rep u'.mem F S V' W' ∧
        ∀ j < nW, j ≠ 28 → j ≠ 29 → j ≠ 30 → j ≠ 44 → j ≠ 45 → j ≠ 46 → W' j = W j) ∧
      u'.gpr .rax = if W 33 = 0 ∧ ∀ i < H.D, (lk.G.hash msg).getD i 0 = V (oEm + lo + db + i) then 1 else 0 := by
  intro msg
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c3 : oDig = 2304 := rfl
  have c5 : oRsa = 8192 := rfl
  simp only [seqs]
  -- `Y` cleared.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [clearY]) (Nat.zero_le 8)
    (clearY_ok L R)) fun u1 ⟨⟨L1, k1, hcx1, R1⟩, f1⟩ => ?_)
  have hS1 := chain (u := u) rfl L.rsp (fun _ _ => rfl) f1
  -- `mHash`.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [copyDigest]) (Nat.zero_le 8)
    (copyDigest_ok hH L1 R1 (p := dig) hdg hcx1
      (fun i hi => by rw [k1.2.1, k1.2.2]; exact hdR i hi)
      (fun i hi j hj => Outside.ne L1 (by rw [k1.2.2]; exact hdO i hi) (by omega))))
    fun u2 ⟨⟨L2, k2, R2⟩, f2⟩ => ?_)
  have hS2 := chain (u := u) k1.2.2 L1.rsp hS1 f2
  -- `DB`.
  refine WP.seq (WP.mono (copyDb_ok L2 R2 (e := oEm + lo) (db := db) he hdb ((k2.gpr (by decide)).trans hcx1)
    hdb1 (by omega) (by omega)) fun u3 ⟨L3, k3, R3⟩ => ?_)
  set V4 := clrV V oY 2048 with hV4
  set V5 := cpV V4 (fun i => u1.mem (dig + BitVec.ofNat 64 i)) (oY + 8) H.D with hV5
  set V6 := cpV V5 (fun i => V5 (oEm + lo + i)) (oY + (8 + H.D)) db with hV6
  have e5 : ∀ i < db, V5 (oEm + lo + i) = V (oEm + lo + i) := fun i hi => by
    simp only [hV5, hV4, cpV, clrV]; rw [ifn (by omega), ifn (by omega)]
  -- The shift.
  have hz : ∀ j, db ≤ j → j < db + 512 → V6 (oY + 8 + H.D + j) = 0 := fun j h1 h2 => by
    simp only [hV6, hV5, hV4, cpV, clrV]; rw [ifn (by omega), ifn (by omega), ifp (by omega)]
  refine WP.seq (WP.mono (shift_ok hH L3 R3 (pos := pos) (db := db) hpos hdb (by omega) hdb1 (by omega) hz)
    fun u4 I4 => ?_)
  obtain ⟨V7, W4, R4, -, -, -, hW4, hV7, hO7⟩ := I4.rep
  have hp10 : (pos + 1) % 2 ^ 10 = pos + 1 := Nat.mod_eq_of_lt (by rw [show (2 : Nat) ^ 10 = 1024 from rfl]; omega)
  rw [hp10] at hV7
  have g4 : ∀ j, j ≠ 44 → j ≠ 45 → j ≠ 46 → j < nW → W4 j = W j := fun j a b c d => hW4 j d a b c
  -- `nbm`.
  refine WP.seq (WP.mono (verifyNb_ok hH I4.L R4 (db := db) (by rw [g4 24 (by decide) (by decide) (by decide)
    (by decide), hdb]) (by omega)) fun u5 ⟨L5, k5, R5⟩ => ?_)
  -- The hash of `M'`.
  have hml : msg.length = db - pos - 1 + (8 + H.D) := by
    simp only [msg, List.length_append, RsaPss.zeros_length, List.length_map, List.length_range, List.length_drop]
    omega
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hL := hH.dims.L
  have hnb1 := Nat.lt_div_mul_add (a := db + (7 + H.D + H.P.L)) (b := H.P.B) hB0
  have hnb2 := Nat.div_mul_le_self (db + (7 + H.D + H.P.L)) H.P.B
  have hmsg : ∀ i, msg.getD i 0 = if i < 8 then 0 else if i < 8 + H.D then u.mem (dig + BitVec.ofNat 64 (i - 8))
      else if i < 8 + H.D + (db - (pos + 1)) then V (oEm + lo + (pos + 1 + (i - (8 + H.D)))) else 0 := fun i => by
    simp only [msg, getD_app, List.length_append, RsaPss.zeros_length, List.length_map, List.length_range,
      getD_map_range, bytesF, RsaPss.zeros_getD]
    by_cases h1 : i < 8
    · rw [ifp (by omega), ifp h1, ifp h1]
    by_cases h2 : i < 8 + H.D
    · rw [ifp h2, ifn h1, ifp (by omega), ifn h1, ifp h2]
    rw [ifn h2, ifn h1, ifn h2]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_map]
    by_cases h3 : i < 8 + H.D + (db - (pos + 1))
    · rw [ifp h3, List.getElem?_range (by omega)]; rfl
    · rw [ifn h3, List.getElem?_eq_none (by simp; omega)]; rfl
  refine WP.seq (WP.mono (ctHash_ok hH K L5 R5 (msg := msg) (nbm := (db + (7 + H.D + H.P.L)) / H.P.B + 1)
      (by rw [hml]; simp only [upd]; rw [ifn (by decide), g4 27 (by decide) (by decide) (by decide) (by decide), hl])
      (by simp [upd]) (by rw [hml, Nat.succ_mul]; omega) (by rw [Nat.succ_mul]; omega) (fun i hi => ?_))
    fun u6 ⟨L6, rd6, wr6, cs6, V8, W6, R6, hout6, hW6, hdig6⟩ => ?_)
  · rw [hmsg]
    have hi' : i < 2048 := by rw [Nat.succ_mul] at hi; omega
    by_cases hY : 8 + H.D ≤ i ∧ i < 8 + H.D + db
    · have := hV7 (i - (8 + H.D)) (by omega)
      rw [show oY + 8 + H.D + (i - (8 + H.D)) = oY + i by omega] at this
      rw [this, ifn (show ¬ i < 8 by omega), ifn (show ¬ i < 8 + H.D by omega)]
      by_cases h3 : i - (8 + H.D) + (pos + 1) < db
      · rw [ifp h3, ifp (show i < 8 + H.D + (db - (pos + 1)) by omega)]
        simp only [hV6, cpV]
        rw [ifp (by omega), show oY + 8 + H.D + (i - (8 + H.D) + (pos + 1)) - (oY + (8 + H.D)) =
          pos + 1 + (i - (8 + H.D)) by omega, e5 _ (by omega)]
      · rw [ifn h3, ifn (show ¬ i < 8 + H.D + (db - (pos + 1)) by omega)]
    · rw [hO7 _ (by omega)]
      simp only [hV6, hV5, hV4, cpV, clrV]
      rw [ifn (by omega)]
      by_cases h1 : i < 8
      · rw [ifn (by omega), ifp (by omega), ifp h1]
      by_cases h2 : i < 8 + H.D
      · rw [ifp (by omega), ifn h1, ifp h2, show oY + i - (oY + 8) = i - 8 by omega]
        exact hS1 _ (hdO _ (by omega))
      · rw [ifn (by omega), ifp (by omega), ifn h1, ifn h2, ifn (by omega)]
  -- The comparison.
  have h23 : W6 23 = off S (oEm + lo) := by
    rw [hW6 23 (by decide) (by decide) (by decide)]; simp only [upd]
    rw [ifn (by decide), g4 23 (by decide) (by decide) (by decide) (by decide), he]
  have h24 : W6 24 = BitVec.ofNat 64 db := by
    rw [hW6 24 (by decide) (by decide) (by decide)]; simp only [upd]
    rw [ifn (by decide), g4 24 (by decide) (by decide) (by decide) (by decide), hdb]
  refine WP.mono (cmpH_ok hH L6 R6 h23 h24 (by omega)) fun u7 ⟨k7, hm7, hax7⟩ => ?_
  have L7 : Lay u7 F S := L6.congr (k7.gpr (by decide)) k7.2.2 (by rw [hm7])
  have hrd : u6.rd = u.rd := by
    rw [rd6, k5.2.1, I4.keep.2.1, k3.2.1, k2.2.1, k1.2.1]
  have hwr : u6.wr = u.wr := by
    rw [wr6, k5.2.2, I4.keep.2.2, k3.2.2, k2.2.2, k1.2.2]
  refine ⟨L7, k7.2.1.trans hrd, k7.2.2.trans hwr, fun r hr => ?_, ⟨V8, W6, hm7 ▸ R6, fun j hj a b c d e f => ?_⟩, ?_⟩
  · rw [keep_cs k7 (by decide) r hr, cs6 r hr, keep_cs k5 (by decide) r hr, keep_cs I4.keep (by decide) r hr,
      keep_cs k3 (by decide) r hr, keep_cs k2 (by decide) r hr, keep_cs k1 (by decide) r hr]
  · rw [hW6 j hj b c]; simp only [upd]; rw [ifn a, g4 j d e f hj]
  · rw [hax7]
    have h33 : W6 33 = W 33 := by
      rw [hW6 33 (by decide) (by decide) (by decide)]; simp only [upd]
      rw [ifn (by decide), g4 33 (by decide) (by decide) (by decide) (by decide)]
    have hH' : ∀ i < H.D, V8 (oDig + i) = (lk.G.hash msg).getD i 0 := fun i hi => by
      rw [map_range_getD hdig6 hi, ← lk.hash]
    have hE : ∀ i < H.D, V8 (oEm + lo + db + i) = V (oEm + lo + db + i) := fun i hi => by
      rw [hout6 _ (by omega) ⟨by unfold oLen; omega, by omega⟩, hO7 _ (by omega)]
      simp only [hV6, hV5, hV4, cpV, clrV]
      rw [ifn (by omega), ifn (by omega), ifn (by omega)]
    rw [h33]
    congr 1
    apply propext
    exact and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun hi => by rw [hH' i hi, hE i hi]

end VG.Proof.RsaPss.X86_64
